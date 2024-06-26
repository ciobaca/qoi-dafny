/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca 2023-2024
 */

include "helper.dfy"

// Represent a single pixel as an RGB tuple (3 color channels)
datatype RGB = RGB(r : byte, g : byte, b : byte)

// Represent a single pixel as an RGBA tuple (4 color channels)
datatype RGBA = RGBA(r : byte, g : byte, b : byte, a : byte)

// Used to represent the number of channels in an image
newtype {:nativeType "byte"} Channels = x : int | 3 <= x <= 4 witness 3

// Represent the colorspace for an image (only useful to interpret the
// image data, does not change the compression itself at all)
datatype ColorSpace = SRGB | Linear

// Image metadata
datatype Desc = Desc(width : uint32, height : uint32, channels : Channels, colorSpace : ColorSpace)

// Representation of a complete image
datatype Image = Image(desc : Desc, data : seq<byte>)

// Compute the hash value of a pixel -- used for dictionary-based encoding
function hashRGBA(color : RGBA) : byte
  ensures 0 <= hashRGBA(color) <= 63
{
  ((color.r as int * 3 + color.g as int * 5 + color.b as int * 7 + color.a as int * 11) % 64) as byte
}

// Compute the hash value of a pixel (for dictionary-based encoding)
function hash(color : RGB) : byte
  ensures 0 <= hash(color) <= 63
{
  hashRGBA(RGBA(color.r, color.g, color.b, 255))
}

// represents the size of a run (used for RLE encoding)
newtype {:nativeType "byte"} Size = x : int | 1 <= x <= 62 witness 1

// represents an index into previously seen colors (for dictionary-based encoding)
newtype {:nativeType "byte"} Index64 = x : int | 0 <= x <= 63

// 6 bit, 4 bit, and 2 bit difference, respectively (used for delta encoding)
newtype {:nativeType "short"} Diff64 = x : int | -32 <= x <= 31
newtype {:nativeType "short"} Diff16 = x : int | -8 <= x <= 7
newtype {:nativeType "short"} Diff = x : int | -2 <= x <= 1

// valid representation of an image
predicate validImage(image : Image)
{
  |image.data| == image.desc.width as int * image.desc.height as int * image.desc.channels as int
}

// Used for one type of delta encoding (6 bits)
datatype RGBDiff = RGBDiff(dr : Diff, dg : Diff, db : Diff)
  
// Used for second type of delta encoding (14 bits)
datatype RGBLuma = RGBLuma(dr : Diff16, dg : Diff64, db : Diff16)

// Abstract representation of one chunk
datatype Op = OpRun(size : Size) // chunk represents a segment of the same color
  | OpIndex(index : Index64)     // index into previously seen colors
  | OpDiff(diff : RGBDiff)       // delta encoding (first type)
  | OpLuma(luma : RGBLuma)       // delta encoding (second type)
  | OpRGB(rgb : RGB)             // pixel value (3 channels)
  | OpRGBA(rgba : RGBA)          // pixel value (4 channels)

// Abstract Encoding of Image as a sequence of Chunks
datatype AEI = AEI(width : uint32, height : uint32, ops : seq<Op>)

// The state of the algorithm (contains previously seen colors)
datatype State = State(prev : RGBA, index : seq<RGBA>)

// The state must contain exactly 64 previously seen colors
ghost predicate validState(state : State)
{
  |state.index| == 64
}

// Specification of how the state should change with each pixel being read
function updateState(previous : State, pixel : RGBA) : State
  requires validState(previous)
  ensures validState(updateState(previous, pixel))
{
  State(prev := pixel, index := previous.index[hashRGBA(pixel) := pixel])
}

// Initial state contains all black pixels
function initState() : State
{
  State(prev := RGBA(0, 0, 0, 255), index := seq(64, i => RGBA(r := 0, g := 0, b := 0, a := 255)))
}

// Specification of how the state should change with a sequence of pixels
function updateStateStar(previous : State, pixels : seq<RGBA>) : State
  requires validState(previous)
  ensures validState(updateStateStar(previous, pixels))
{
  if |pixels| == 0 then
    previous
  else
    updateState(updateStateStar(previous, pixels[..|pixels| - 1]), pixels[|pixels| - 1])
}

// Helper lemma on updating by two sequences of pixels
lemma updateStateStarConcat(state : State,
  pixels1 : seq<RGBA>, state1 : State,
  pixels2 : seq<RGBA>, state2 : State)
  requires validState(state)
  requires validState(state1)
  requires validState(state2)
  requires updateStateStar(state, pixels1) == state1
  requires updateStateStar(state1, pixels2) == state2
  ensures updateStateStar(state, pixels1 + pixels2) == state2
  decreases |pixels2|
{
  if |pixels2| == 0
  {
    assert pixels1 + pixels2 == pixels1;
  }
  else
  {
    ghost var len := |pixels2|;
    ghost var state2p := updateStateStar(state1, pixels2[..len - 1]);
    updateStateStarConcat(state, pixels1, state1, pixels2[..len - 1], state2p);
    assert pixels1 + pixels2 == (pixels1 + pixels2[..len - 1]) + [ pixels2[len - 1] ];
  }
}

// Specification for the decoding of one chunk
function specDecodeOp(state : State, op : Op) : seq<RGBA>
  requires validState(state)
{
  match op
  {
  case OpRGB(RGB(r, g, b)) =>
    [ RGBA(r, g, b, state.prev.a) ]
  case OpRun(size) =>
    seq(size, i => state.prev)
  case OpIndex(index) =>
    [ state.index[index] ]
  case OpDiff(RGBDiff(dr, dg, db)) =>
    [ RGBA(add_byte(state.prev.r, byte_from(dr as int)),
        add_byte(state.prev.g, byte_from(dg as int)),
        add_byte(state.prev.b, byte_from(db as int)),
        state.prev.a
        ) ]
  case OpLuma(RGBLuma(dr, dg, db)) =>
    [ RGBA(add_byte(add_byte(state.prev.r, byte_from(dg as int)), byte_from(dr as int)),
        add_byte(state.prev.g, byte_from(dg as int)),
        add_byte(add_byte(state.prev.b, byte_from(dg as int)), byte_from(db as int)),
        state.prev.a
        ) ]
  case OpRGBA(rgba) =>
    [ rgba ]
  }
}

// Specification for the decoding of several chunks
function specOpsAux(ops : seq<Op>, state : State) : seq<RGBA>
  requires validState(state)
{
  if |ops| == 0 then 
    []
  else
    var pixels : seq<RGBA> := specDecodeOp(state, ops[0]);
    pixels + specOpsAux(ops[1..], updateStateStar(state, pixels))
}

// Helper lemma (associativity)
lemma specOpsAuxAssoc(ops : seq<Op>, state : State)
  requires validState(state)
  requires |ops| > 0
  ensures specOpsAux(ops[..|ops| - 1], state) +
  specDecodeOp(updateStateStar(state, specOpsAux(ops[..|ops|-1], state)), ops[|ops| - 1]) ==
  specOpsAux(ops, state)
{
  if |ops| - 1 == 0
  {
  }
  else
  {
    ghost var len := |ops|;
    ghost var ops1 := ops[1..];
    assert |ops1| == len - 1;
    ghost var len1 := |ops1|;

    ghost var state1 := updateStateStar(state, specDecodeOp(state, ops[0]));
    specOpsAuxAssoc(ops1, state1);

    assert specOpsAux(ops1[..len1 - 1], state1) +
      specDecodeOp(updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)), ops1[len1 - 1]) ==
      specOpsAux(ops1, state1);
    ghost var pixels1 := specDecodeOp(state, ops[0]);
    assert specOpsAux(ops, state) == pixels1 + specOpsAux(ops1, state1);
    assert ops1[|ops1| - 1] == ops[|ops| - 1];
    assert ops1[..|ops1| - 1] == ops[1..|ops| - 1];
    assert specOpsAux(ops[..|ops| - 1], state) == pixels1 + specOpsAux(ops1[..len1 - 1], state1);
    assert ops[|ops| - 1] == ops1[len1 - 1];
    updateStateStarConcat(state,
      pixels1, state1,
      specOpsAux(ops1[..len1 - 1], state1), updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)));
    assert
      updateStateStar(state, specOpsAux(ops[..|ops|-1], state)) ==
      updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1));
    assert
      specDecodeOp(updateStateStar(state, specOpsAux(ops[..|ops|-1], state)), ops[|ops| - 1]) ==
      specDecodeOp(updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)), ops1[len1 - 1]);
    assert specOpsAux(ops, state) ==
      specOpsAux(ops[..|ops| - 1], state) + 
      specDecodeOp(updateStateStar(state1, specOpsAux(ops1[..len1 - 1], state1)), ops1[len1 - 1]);
  }
}

// Main specification for the decoding of several chunks
function specOps(ops : seq<Op>) : seq<RGBA>
{
  specOpsAux(ops, initState())
}

lemma specOpsAuxMonotone(ops : seq<Op>, state : State, i : int)
  requires 0 <= i <= |ops|
  requires validState(state)
  ensures |specOpsAux(ops, state)| >= |specOpsAux(ops[..i], state)|
{
  if (|ops| == 0)
  {
  }
  else
  {
    if (i == 0)
    {
    }
    else
    {
      var pixels : seq<RGBA> := specDecodeOp(state, ops[0]);
      var state' := updateStateStar(state, pixels);
      specOpsAuxMonotone(ops[1..], state', i - 1);
      assert |specOpsAux(ops, state)| == |pixels| + |specOpsAux(ops[1..], state')|;
      assert ops[..i][0] == ops[0];
      assert |specOpsAux(ops[..i], state)| == |pixels| + |specOpsAux(ops[..i][1..], state')|;
      assert |specOpsAux(ops[1..], state')| >= |specOpsAux(ops[1..][..i-1], state')|;
      calc {
        |specOpsAux(ops, state)|;
      ==
        |pixels| + |specOpsAux(ops[1..], state')|;
      >=
        |pixels| + |specOpsAux(ops[1..][..i-1], state')|;
      == { assert ops[1..][..i-1] == ops[..i][1..]; }
        |pixels| + |specOpsAux(ops[..i][1..], state')|;
      ==
        |specOpsAux(ops[..i], state)|;
      }
    }
  }
}

lemma specOpsMonotone(ops : seq<Op>, i : int)
  requires 0 <= i <= |ops|
  ensures |specOps(ops)| >= |specOps(ops[..i])|
{
  specOpsAuxMonotone(ops, initState(), i);
}

lemma specOpsDecompose(ops : seq<Op>, i : int, state : State)
  requires 0 <= i < |ops|
  requires validState(state)
  requires state == updateStateStar(initState(), specOpsAux(ops[..i], initState()))
  ensures |specOps(ops[..i+1])| == |specOps(ops[..i])| + |specDecodeOp(state, ops[i])|
{
  ghost var ops' := ops[..i+1];
  assert ops'[..i] == ops[..i];
  assert ops'[i] == ops[i];
  specOpsAuxAssoc(ops', initState());
  assert specOpsAux(ops'[..|ops'| - 1], initState()) +
    specDecodeOp(updateStateStar(initState(), specOpsAux(ops'[..|ops'|-1], initState())), ops'[|ops'| - 1]) ==
    specOpsAux(ops', initState());
}

// Specification for convering a sequence of RGBA tuples into a sequence of bytes
function toByteStreamRGB(data : seq<RGBA>) : seq<byte>
{
  if |data| == 0 then
    []
  else
    [ data[0].r, data[0].g, data[0].b ] + toByteStreamRGB(data[1..])
}

// Specification for convering a sequence of RGB tuples into a sequence of bytes
function toByteStreamRGBA(data : seq<RGBA>) : seq<byte>
{
  if |data| == 0 then
    []
  else
    [ data[0].r, data[0].g, data[0].b, data[0].a ] + toByteStreamRGBA(data[1..])
}

// Specification for convering a sequence of pixels into a sequence of
// bytes (depending on the number of color channels)
function toByteStream(desc : Desc, data : seq<RGBA>) : seq<byte>
{
  match (desc.channels)
  {
  case 3 =>
    toByteStreamRGB(data)
  case 4 =>
    toByteStreamRGBA(data)
  }
}

// When is an Abstract Encoded Image valid?
predicate validAEI(aei : AEI)
{
  |specOps(aei.ops)| == aei.width as int * aei.height as int
}

// Entry point for the specification: what image data corresponds to an abtract encoded image
function spec(aei : AEI) : seq<RGBA>
  requires validAEI(aei)
{
  specOps(aei.ops)
}
