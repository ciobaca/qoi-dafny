/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca, May 2023
 */
include "spec.dfy"
include "specbit.dfy"

function method canDiff(curr : RGBA, prev : RGBA) : Option<RGBDiff>
  ensures forall dr, dg, db : Diff :: canDiff(curr, prev) == Some(RGBDiff(dr, dg, db)) ==>
  curr.r == add_byte(prev.r, byte_from(dr as int)) && 
  curr.g == add_byte(prev.g, byte_from(dg as int)) && 
  curr.b == add_byte(prev.b, byte_from(db as int)) &&
  curr.a == prev.a
{
  var dr : int := curr.r as int - prev.r as int;
  var dg : int := curr.g as int - prev.g as int;
  var db : int := curr.b as int - prev.b as int;
  var da : int := curr.a as int - prev.a as int;
  if (-2 <= dr <= 1 && -2 <= dg <= 1 && -2 <= db <= 1 && da == 0) then
    Some(RGBDiff(dr as Diff, dg as Diff, db as Diff))
  else
    None
}

function method canLuma(curr : RGBA, prev : RGBA) : Option<RGBLuma>
  ensures forall luma : RGBLuma// , dgr : Diff16 :: forall dg : Diff64 :: forall dgb : Diff16
  ::
  canLuma(curr, prev) == Some(luma) ==>
  curr.r == add_byte(add_byte(prev.r, byte_from(luma.dg as int)), byte_from(luma.dr as int)) && 
  curr.g == add_byte(prev.g, byte_from(luma.dg as int)) && 
  curr.b == add_byte(add_byte(prev.b, byte_from(luma.dg as int)), byte_from(luma.db as int))  && 
  curr.a == prev.a
{
  // assume false; // help speed up, will still compile without (but slower)
  var dr : int := curr.r as int - prev.r as int;
  var dg : int := curr.g as int - prev.g as int;
  var db : int := curr.b as int - prev.b as int;
  var da : int := curr.a as int - prev.a as int;
  if (-32 <= dg <= 31 && -8 <= (dr - dg) <= 7 && -8 <= (db - dg) <= 7 && da == 0) then
    Some(RGBLuma((dr - dg) as Diff16, dg as Diff64, (db - dg) as Diff16))
  else
    None
}

method encodePixelAEI(curr : RGBA,
  prev : RGBA,
  index : array<RGBA>,
  ghost state : State,
  encoding : seq<Op>)
  returns (r : seq<Op>)
  requires validState(state)
  requires state.prev == prev
  requires state.index == index[..]
  requires index.Length == 64
  requires state ==
    updateStateStar(initState(), specOps(encoding))
  modifies index
  ensures index.Length == 64
  ensures index[..] == old(index[..])[hashRGBA(curr) := curr]
  ensures specOps(encoding) + [ curr ] == specOps(r)
{
  var len : int := |encoding|;
  if (curr == prev) {
    if (len > 0 && encoding[len - 1].OpRun? && encoding[len - 1].size < 62) {
      r := encoding[len - 1 := OpRun(encoding[len - 1].size + 1)];
      ghost var pixels_prev := specOps(encoding[..len - 1]);
      ghost var state_prev := updateStateStar(initState(), pixels_prev);
      ghost var pixels1 := specDecodeOp(state_prev, encoding[len - 1]);
      specOpsAuxAssoc(encoding, initState());
      assert specOps(encoding) == pixels_prev + pixels1;
      ghost var pixels2 := specDecodeOp(state_prev, r[len - 1]);
      assert pixels1 == seq(encoding[len - 1].size, i => state_prev.prev);
      assert pixels2 == seq(encoding[len - 1].size + 1, i => state_prev.prev);
      assert curr == state_prev.prev;
      assert pixels2 == pixels1 + [ curr ];
      assert encoding == encoding[..len];
      assert encoding[..len] == encoding[..len - 1] + [ encoding[len - 1] ];
      specOpsAuxAssoc(r, initState());
      assert specOps(r) == pixels_prev + pixels2;
      assert specOps(encoding) + [ curr ] == specOps(r);
    } else {
      r := encoding + [ OpRun(1) ];
      specOpsAuxAssoc(r, initState());
      assert specOps(encoding) + [ curr ] == specOps(r);
    }
  } else if (index[hashRGBA(curr)] == curr) {
    // QOI_OP_INDEX
    r := encoding + [ OpIndex(hashRGBA(curr) as Index64) ];
    specOpsAuxAssoc(r, initState());
    assert specOps(encoding) + [ curr ] == specOps(r);
  } else if (canDiff(curr, prev) != None) {
    // QOI_OP_DIFF
    var result := canDiff(curr, prev).some;
    r := encoding + [ OpDiff(result) ];
    specOpsAuxAssoc(r, initState());
    assert specOps(encoding) + [ curr ] == specOps(r);
  } else if (canLuma(curr, prev) != None) {
    // QOI_OP_LUMA
    var result := canLuma(curr, prev).some;
    r := encoding + [ OpLuma(result) ];
    specOpsAuxAssoc(r, initState());
    assert specOps(encoding) + [ curr ] == specOps(r);
  } else if (curr.a == prev.a) {
    // QOI_OP_RGB
    r := encoding + [ OpRGB(RGB(curr.r, curr.g, curr.b)) ];
    specOpsAuxAssoc(r, initState());
    assert specOps(encoding) + [ curr ] == specOps(r);
  } else {
    r := encoding + [ OpRGBA(RGBA(curr.r, curr.g, curr.b, curr.a)) ];
    specOpsAuxAssoc(r, initState());
    assert specOps(encoding) + [ curr ] == specOps(r);
  }
  var h := hashRGBA(curr);
  index[h] := curr;
}

method encodeAEI(image : seq<RGBA>) returns (r : seq<Op>)
//  requires w >= 1
//  requires h >= 1
//  requires |image| == w as int * h as int
  ensures specOps(r) == image
{
  var ops : seq<Op> := [];
  var prev : RGBA := RGBA(r := 0, g := 0, b := 0, a := 255);
  var index : array<RGBA> := new RGBA[64](i => RGBA(r := 0, g := 0, b := 0, a := 255));
  var i : int := 0;
  var wh : int := |image|;
  ghost var state := initState();
  while (i < wh)
    invariant 0 <= i <= wh;
    decreases wh - i;
    invariant state == updateStateStar(
      initState(), image[..i]);
    invariant state.prev == prev;
    invariant state.index == index[..];
    invariant specOps(ops) == image[..i];
  {
    var curr := image[i];
    ops := encodePixelAEI(curr, prev, index, state, ops);
    state := updateState(state, curr);
    prev := curr;
    i := i + 1;
    assert image[..i] == image[..i-1] + [ curr ];
    assert state == updateStateStar(initState(), image[..i]);
  }
  return ops;
}

method decodeAEI(ops : seq<Op>) returns (r : seq<RGBA>) // (r : Option<seq<RGBA>>)
  ensures r == specOps(ops)
  // ensures validAEI(aei) ==> r.Some? && r.some == spec(aei)
//  ensures !validAEI(aei) ==> r.None?
{
  var i := 0;
  //var ops := aei.ops;
  //var w := aei.width;
  //var h := aei.height;
  var image : seq<RGBA> := [];
  // var prev : RGBA := RGBA(r := 0, g := 0, b := 0, a := 255);
  // var index : array<RGBA> := new RGBA[64](i => RGBA(r := 0, g := 0, b := 0, a := 255));
  var state := initState();
  while (i < |ops|)
    invariant 0 <= i <= |ops|;
    invariant state == updateStateStar(initState(), image);
    invariant specOps(ops[..i]) == image;
//    invariant aei.ops == ops;
//    invariant aei.width == w;
//    invariant aei.height == h;
  {
    ghost var image0 := image;
    ghost var state0 := state;
    assert specOpsAux(ops[..i], initState()) == image;
    var op := ops[i];
    var pixels := specDecodeOp(state, op);
    updateStateStarConcat(initState(), image, state, pixels, updateStateStar(state, pixels));
    image := image + pixels;
    state := updateStateStar(state, pixels);
    i := i + 1;
    specOpsAuxAssoc(ops[..i], initState());
    assert ops[..i][..|ops[..i]| - 1] == ops[..i - 1];
  }
  assert ops[..] == ops[..i];
  return image;
  // if (|image| == w as int * h as int) {
  //   return Some(image);
  // } else {
  //   return None;
  // }
}

function method asRGBA3(data : seq<byte>) : seq<RGBA>
  requires |data| % 3 == 0;
  ensures toByteStreamRGB(asRGBA3(data)) == data
  ensures |asRGBA3(data)| == |data| / 3;
{
  if |data| == 0 then
    []
  else
    [ RGBA(data[0], data[1], data[2], 255) ] + asRGBA3(data[3..])
}

function method asRGBA4(data : seq<byte>) : seq<RGBA>
  requires |data| % 4 == 0;
  ensures toByteStreamRGBA(asRGBA4(data)) == data
  ensures |asRGBA4(data)| == |data| / 4;
{
  if |data| == 0 then
    []
  else
    [ RGBA(data[0], data[1], data[2], data[3]) ] + asRGBA4(data[4..])
}

function method asRGBA(data : seq<byte>, desc : Desc) : seq<RGBA>
  requires |data| == desc.width as int * desc.height as int * desc.channels as int;
  ensures toByteStream(desc, asRGBA(data, desc)) == data
  ensures |asRGBA(data, desc)| == desc.width as int * desc.height as int;
{
  if desc.channels == 3 then
    asRGBA3(data)
  else 
    asRGBA4(data)
}

method encodeAll(image : Image) returns (r : seq<byte>)
  requires validImage(image)
  ensures validByteStream(r)
  ensures image == specEndToEnd(r)
{
  var header := genHeader(image.desc);
  var footer := genFooter();
  assert |image.data| == image.desc.width as int * image.desc.height as int * image.desc.channels as int;
  var ops := encodeAEI(asRGBA(image.data, image.desc));
  assert |specOps(ops)| == image.desc.width as int * image.desc.height as int;
  var bits := encodeBitSeq(ops);
  r := header + bits + footer;
  var len := |r|;
  assert header == r[..14];
  assert image.desc == specHeader(r[..14]);
  assert footer == r[len - 8..];
  assert decodeBitSeqSure(r[14..len-8]) == ops;
  assert specOps(ops) == asRGBA(image.data, image.desc);
  // assert decodeAEI(ops) == image.data;
  assert |r| >= 14 + 8;
  assert validHeader(r[..14]);
  assert validFooter(r[len - 8..]);
  assert validBitSeq(r[14..len-8]);
  assert |specOps(decodeBitSeqSure(r[14..len-8]))| ==
    specHeader(r[..14]).width as int *
    specHeader(r[..14]).height as int;
  assert validByteStream(r);
}

method parseHeader(header : seq<byte>) returns (r : Option<Desc>)
  requires |header| == 14
  ensures validHeader(header) ==> r.Some? && r.some == specHeader(header)
  ensures !validHeader(header) ==> r.None?
{
  if header[0..4] != [ 'q' as byte, 'o' as byte, 'i' as byte, 'f' as byte ] {
    return None;
  }
  if 3 <= header[12] <= 4 && validColorSpaceAsByte(header[13]) {
    var desc := Desc(
    pack(header[4..8]),
    pack(header[8..12]),
    header[12] as Channels,
    colorSpaceFromByte(header[13]));
    pack_unpack(header[4..8]);
    pack_unpack(header[8..12]);
    assert genHeader(desc) == header;
    assert validHeader(header);
    return Some(desc);
  }
  return None;
}

method decodeAll(byteStream : seq<byte>) returns (r : Option<Image>)
  ensures !validByteStream(byteStream) ==> r.None?
  ensures validByteStream(byteStream) ==> r.Some? && r.some == specEndToEnd(byteStream)
{
  if (|byteStream| < 14 + 8) {
    return None;
  } else {
    var len := |byteStream|;
    var header := byteStream[..14];
    var footer := byteStream[len - 8..];
    if (footer != genFooter()) {
      return None;
    }
    var descOption := parseHeader(header);
    if (descOption.None?) {
      return None;
    }
    var desc := descOption.some;
    var opsOption := decodeBitSeq(byteStream[14..len-8]);
    if (opsOption.None?) {
      return None;
    }
    var ops := opsOption.some;
    var rgbs : seq<RGBA> := decodeAEI(ops);
    var data := toByteStream(desc, rgbs);
    if |rgbs| != desc.width as int * desc.height as int {
      return None;
    }
    return Some(Image(desc, data));
  }
}

method test(i : int) returns (r : seq<RGBA>)
  requires 0 <= i <= 2;
  ensures |r| == 3;
{
  var p1 := RGBA(1, 2, 3, 255);
  var p2 := RGBA(0, 1, 0, 255);
  var p3 := RGBA(3, 8, 9, 255);
  var p4 := RGBA(4, 9, 7, 255);
  var p5 := RGBA(25, 23, 29, 255);
  if (i == 0) {
    return [ p2, p2, p2// , p3, p3,
    // p3, p4, p3, p4,
    // p1, p1, p1, p1,
    // p2, p3, p1, p2
    ];
  } else if i == 1 {
    return [ p1, p5, p2// , p3, p3,
    // p3, p4, p3, p4,
    // p1, p1, p1, p1,
    // p2, p3, p1, p2 
    ];
  } else if i == 2 {
    return [ p1, p5, p1// , p3, p3,
    // p3, p4, p3, p4,
    // p1, p1, p1, p1,
    // p2, p3, p1, p2 
    ];
  }
}

method test4() returns (r : Image)
  ensures validImage(r);
{
  var desc := Desc(4, 4, 3, Linear);
  var data := [
    7, 7, 250,  7, 7, 250,  7, 7, 250,  7, 7, 250,
    7, 7, 250,  8, 6, 251,  15, 17, 255,  8, 6, 251,
    8, 6, 251,  8, 6, 251,  8, 6, 251,  8, 6, 251,
    4, 5, 100,  4, 5, 100,  4, 5, 100,  4, 5, 100
    ];
  assert |data| == 3 * 4 * 4;
  return Image(desc, data);
}

method Main()
{
  var w : uint32 := 3;
  var h : uint32 := 1;
  for i := 0 to 1 {
    print("\n\n\nTest ");
    print(i);
    print("\n");
    var image : Image := test4();
    // var header := init(w, h);
    var result := encodeAll(image);
    // var image2 := decode(result);
    print("Initial image");
    print(image);
    print("\n\nEncoded");
    print(result);
    print("\n");
  }
}
