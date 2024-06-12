/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca 2023-2024
 */

include "helper.dfy"

datatype RGB = RGB(r : byte, g : byte, b : byte)

datatype RGBA = RGBA(r : byte, g : byte, b : byte, a : byte)

newtype {:nativeType "byte"} Channels = x : int | 3 <= x <= 4 witness 3

datatype ColorSpace = SRGB | Linear

datatype Desc = Desc(width : uint32, height : uint32, channels : Channels, colorSpace : ColorSpace)

datatype Image = Image(desc : Desc, data : seq<byte>)
  // ImageRGB(desc : Desc, dataRGB : seq<RGB>)
  // | ImageRGBA(desc : Desc, dataRGBA : seq<RGBA>)

function hashRGBA(color : RGBA) : byte
  ensures 0 <= hashRGBA(color) <= 63
{
  ((color.r as int * 3 + color.g as int * 5 + color.b as int * 7 + color.a as int * 11) % 64) as byte
}

function hash(color : RGB) : byte
  ensures 0 <= hash(color) <= 63
{
  hashRGBA(RGBA(color.r, color.g, color.b, 255))
//  ((color.r as int * 3 + color.g as int * 5 + color.b as int * 7 + 255 * 11) % 64) as byte
}

newtype {:nativeType "byte"} Size = x : int | 1 <= x <= 62 witness 1
newtype {:nativeType "byte"} Index64 = x : int | 0 <= x <= 63
newtype {:nativeType "short"} Diff = x : int | -2 <= x <= 1
newtype {:nativeType "short"} Diff64 = x : int | -32 <= x <= 31
newtype {:nativeType "short"} Diff16 = x : int | -8 <= x <= 7
  
// function method channels(image : Image) : byte
//   ensures 3 <= channels(image) <= 4
// {
//   image.desc.channels
//   // match image
//   // {
//   // case ImageRGB(desc, d) =>
//   //   3
//   // case ImageRGBA(desc, d) =>
//   //   4
//   // }
// }

predicate validImage(image : Image)
{
  |image.data| == image.desc.width as int * image.desc.height as int * image.desc.channels as int
  // match image
  // {
  // case ImageRGB(desc, data) =>
  //   |data| == desc.width as int * desc.height as int && desc.channels == 3
  // case ImageRGBA(desc, data) =>
  //   |data| == desc.width as int * desc.height as int && desc.channels == 4
  // }
}

datatype RGBDiff = RGBDiff(dr : Diff, dg : Diff, db : Diff)
datatype RGBLuma = RGBLuma(dr : Diff16, dg : Diff64, db : Diff16)

datatype Op = OpRun(size : Size)
  | OpIndex(index : Index64)
  | OpDiff(diff : RGBDiff)
  | OpLuma(luma : RGBLuma)
  | OpRGB(rgb : RGB)
  | OpRGBA(rgba : RGBA)

datatype AEI = AEI(width : uint32, height : uint32, ops : seq<Op>)

datatype State = State(prev : RGBA, index : seq<RGBA>)

ghost predicate validState(state : State)
{
  |state.index| == 64
}

function updateState(previous : State, pixel : RGBA) : State
  requires validState(previous)
  ensures validState(updateState(previous, pixel))
{
  State(prev := pixel, index := previous.index[hashRGBA(pixel) := pixel])
}

function initState() : State
{
  State(prev := RGBA(0, 0, 0, 255), index := seq(64, i => RGBA(r := 0, g := 0, b := 0, a := 255)))
}

function updateStateStar(previous : State, pixels : seq<RGBA>) : State
  requires validState(previous)
  ensures validState(updateStateStar(previous, pixels))
{
  if |pixels| == 0 then
    previous
  else
    updateState(updateStateStar(previous, pixels[..|pixels| - 1]), pixels[|pixels| - 1])
}

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

function specOpsAux(ops : seq<Op>, state : State) : seq<RGBA>
  requires validState(state)
{
  if |ops| == 0 then 
    []
  else
    var pixels : seq<RGBA> := specDecodeOp(state, ops[0]);
    pixels + specOpsAux(ops[1..], updateStateStar(state, pixels))
}

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

function specOps(ops : seq<Op>) : seq<RGBA>
{
  specOpsAux(ops, initState())
}

function toByteStreamRGB(data : seq<RGBA>) : seq<byte>
{
  if |data| == 0 then
    []
  else
    [ data[0].r, data[0].g, data[0].b ] + toByteStreamRGB(data[1..])
}

function toByteStreamRGBA(data : seq<RGBA>) : seq<byte>
{
  if |data| == 0 then
    []
  else
    [ data[0].r, data[0].g, data[0].b, data[0].a ] + toByteStreamRGBA(data[1..])
}

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

// function method stateOpsAux(ops : seq<Op>, state : State) : State
//   requires validState(state)
//   ensures validState(stateOpsAux(ops, state))
// {
//   if |ops| == 0 then
//     state
//   else
//     var pixels : seq<RGBA> := specDecodeOp(state, ops[0]);
//     stateOpsAux(ops[1..], updateStateStar(state, pixels))
// }

// function method stateOps(ops : seq<Op>) : State
//   ensures validState(stateOps(ops))
// {
//   stateOpsAux(ops, initState())
// }

predicate validAEI(aei : AEI)
{
  |specOps(aei.ops)| == aei.width as int * aei.height as int
}

function spec(aei : AEI) : seq<RGBA>
  requires validAEI(aei)
{
  specOps(aei.ops)
}
