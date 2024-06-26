/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca 2023-2024
 */

include "spec.dfy"
include "specbit.dfy"

// Check if two pixels are close enough to use delta encoding (type 1)
function canDiff(curr : RGBA, prev : RGBA) : Option<RGBDiff>
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

// Check if two pixels are close enough to use delta encoding (type 2)
function canLuma(curr : RGBA, prev : RGBA) : Option<RGBLuma>
  ensures forall luma : RGBLuma// , dgr : Diff16 :: forall dg : Diff64 :: forall dgb : Diff16
  ::
  canLuma(curr, prev) == Some(luma) ==>
  curr.r == add_byte(add_byte(prev.r, byte_from(luma.dg as int)), byte_from(luma.dr as int)) && 
  curr.g == add_byte(prev.g, byte_from(luma.dg as int)) && 
  curr.b == add_byte(add_byte(prev.b, byte_from(luma.dg as int)), byte_from(luma.db as int))  && 
  curr.a == prev.a
{
  var dr : int := curr.r as int - prev.r as int;
  var dg : int := curr.g as int - prev.g as int;
  var db : int := curr.b as int - prev.b as int;
  var da : int := curr.a as int - prev.a as int;
  if (-32 <= dg <= 31 && -8 <= (dr - dg) <= 7 && -8 <= (db - dg) <= 7 && da == 0) then
    (
    assert curr.a == prev.a;
    assert curr.g == add_byte(prev.g, byte_from((dg as Diff64) as int));
    assert curr.r == add_byte(add_byte(prev.r, byte_from((dg as Diff64) as int)), byte_from((dr - dg) as int));
    assert curr.b == add_byte(add_byte(prev.b, byte_from((dg as Diff64) as int)), byte_from((db - dg) as int));
    Some(RGBLuma((dr - dg) as Diff16, dg as Diff64, (db - dg) as Diff16))
      )
  else
    None
}

// Encode one pixel of the image
method encodePixelAEI(curr : RGBA,
  prev : RGBA,
  index : array<RGBA>,
  ghost state : State,
  encoding : array<Op>,
  len : int)
  returns (newlen : int)
  requires 0 <= len < encoding.Length
  requires validState(state)
  requires state.prev == prev
  requires state.index == index[..]
  requires index.Length == 64
  requires state ==
    updateStateStar(initState(), specOps(encoding[..len]))
  modifies index
  ensures index.Length == 64
  ensures index[..] == old(index[..])[hashRGBA(curr) := curr]
  ensures newlen == len || newlen == len + 1
  ensures specOps(old(encoding[..len])) + [ curr ] == specOps(encoding[..newlen])
  modifies encoding
{
  newlen := len + 1;
  if (curr == prev) {
    if (len > 0 && encoding[len - 1].OpRun? && encoding[len - 1].size < 62) {
      ghost var pixels_prev := specOps(encoding[..len - 1]);
      ghost var state_prev := updateStateStar(initState(), pixels_prev);
      ghost var pixels1 := specDecodeOp(state_prev, encoding[len - 1]);
      specOpsAuxAssoc(encoding[..len], initState());
      assert encoding[..len][..len - 1] == encoding[..len - 1];
      assert specOps(encoding[..len]) == pixels_prev + pixels1;

      encoding[len - 1] := OpRun(encoding[len - 1].size + 1);
      newlen := len;
      ghost var pixels2 := specDecodeOp(state_prev, encoding[len - 1]);

      assert encoding[..len - 1] == old(encoding[..len - 1]);
      assert old(encoding[len - 1]) == OpRun(old(encoding[len - 1]).size);
      assert encoding[len - 1] == OpRun(old(encoding[len - 1]).size + 1);
      assert pixels1 == seq(old(encoding[len - 1].size), i => state_prev.prev);
      assert pixels2 == seq(old(encoding[len - 1].size) + 1, i => state_prev.prev);
      assert curr == state_prev.prev;
      assert pixels2 == pixels1 + [ curr ];
      assert encoding[..len] == encoding[..len - 1] + [ encoding[len - 1] ];
      specOpsAuxAssoc(encoding[..newlen], initState());
      assert specOps(encoding[..len]) == pixels_prev + pixels2;
      assert specOps(old(encoding[..len])) + [ curr ] == specOps(encoding[..newlen]);
    } else {
      assert encoding[..len] == old(encoding[..len]);
      assert encoding[..newlen] == encoding[..len] + [ encoding[len] ];
      encoding[len] := OpRun(1);
      specOpsAuxAssoc(encoding[..newlen], initState());
      assert specOps(encoding[..len]) + [ curr ] == specOps(encoding[..newlen]);
    }
  } else if (index[hashRGBA(curr)] == curr) {
    // QOI_OP_INDEX
    encoding[len] := OpIndex(hashRGBA(curr) as Index64);
    assert encoding[..len] == old(encoding[..len]);
    assert encoding[..newlen] == encoding[..len] + [ encoding[len] ];
    specOpsAuxAssoc(encoding[..newlen], initState());
    assert specOps(encoding[..len]) + [ curr ] == specOps(encoding[..newlen]);
  } else if (canDiff(curr, prev) != None) {
    // QOI_OP_DIFF
    var result := canDiff(curr, prev).some;
    assert encoding[..len] == old(encoding[..len]);
    assert encoding[..newlen] == encoding[..len] + [ encoding[len] ];
    encoding[len] := OpDiff(result);
    specOpsAuxAssoc(encoding[..newlen], initState());
    assert specOps(encoding[..len]) + [ curr ] == specOps(encoding[..newlen]);
  } else if (canLuma(curr, prev) != None) {
    // QOI_OP_LUMA
    var result := canLuma(curr, prev).some;
    encoding[len] := OpLuma(result);
    assert encoding[..len] == old(encoding[..len]);
    assert encoding[..newlen] == encoding[..len] + [ encoding[len] ];
    specOpsAuxAssoc(encoding[..newlen], initState());
    assert specOps(encoding[..len]) + [ curr ] == specOps(encoding[..newlen]);
  } else if (curr.a == prev.a) {
    // QOI_OP_RGB
    encoding[len] := OpRGB(RGB(curr.r, curr.g, curr.b));
    assert encoding[..len] == old(encoding[..len]);
    assert encoding[..newlen] == encoding[..len] + [ encoding[len] ];
    specOpsAuxAssoc(encoding[..newlen], initState());
    assert specOps(encoding[..len]) + [ curr ] == specOps(encoding[..newlen]);
  } else {
    encoding[len] := OpRGBA(RGBA(curr.r, curr.g, curr.b, curr.a));
    assert encoding[..len] == old(encoding[..len]);
    assert encoding[..newlen] == encoding[..len] + [ encoding[len] ];
    specOpsAuxAssoc(encoding[..newlen], initState());
    assert specOps(encoding[..len]) + [ curr ] == specOps(encoding[..newlen]);
  }
  var h := hashRGBA(curr);
  index[h] := curr;
}

lemma seqLast(s : seq<RGBA>)
  requires |s| > 0
  ensures s == s[..|s| - 1] + [ s[|s| - 1] ]
{
}

// Encode all pixels in a image into an array of chunks
method encodeAEI(image : seq<RGBA>) returns (r : array<Op>, len : int)
  ensures 0 <= len <= r.Length
  ensures specOps(r[..len]) == image
{
  r := new Op [|image|];
  var prev : RGBA := RGBA(r := 0, g := 0, b := 0, a := 255);
  var index : array<RGBA> := new RGBA[64](i => RGBA(r := 0, g := 0, b := 0, a := 255));
  var i : int := 0;
  var wh : int := |image|;
  len := 0;
  ghost var state := initState();
  while (i < wh)
    invariant 0 <= len <= i <= wh
    decreases wh - i
    invariant state == updateStateStar(
      initState(), image[..i])
    invariant state.prev == prev
    invariant state.index == index[..]
    invariant specOps(r[..len]) == image[..i]
  {
    var curr := image[i];
    len := encodePixelAEI(curr, prev, index, state, r, len);
    state := updateState(state, curr);
    prev := curr;
    i := i + 1;
    assert image[i - 1] == curr;
    assert image[..i][..i-1] == image[..i-1];
    seqLast(image[..i]);
    assert image[..i] == image[..i-1] + [ image[i - 1] ];
    assert state == updateStateStar(initState(), image[..i]); 
 }
}

ghost predicate updatedState(state : State, newstate : State, pixels : seq<RGBA>)
  requires validState(state)
{
  newstate == updateStateStar(state, pixels)
}

lemma updatedStateNext(state : State, oldnewstate : State, newstate : State,
  pixels : seq<RGBA>, pixel : RGBA)
  requires validState(state)
  requires updatedState(state, oldnewstate, pixels)
  requires newstate == updateState(oldnewstate, pixel)
  ensures updatedState(state, newstate, pixels + [ pixel ])
{
}

method decodeOp(state : State, op : Op, len : int, res : array<RGBA>) returns (newlen : int, newstate : State, ok : bool)
  requires validState(state)
  //requires res.Length >= len + |specDecodeOp(state, op)|
  requires 0 <= len
  ensures ok == (len + |specDecodeOp(state, op)| <= res.Length)
  ensures ok ==> newlen == len + |specDecodeOp(state, op)|
  ensures ok ==> res[..newlen] == old(res[..len]) + specDecodeOp(state, op)
  ensures ok ==> newstate == updateStateStar(state, specDecodeOp(state, op))
  ensures ok ==> validState(state)
  modifies res
{
  match op
  {
  case OpRGB(RGB(r, g, b)) =>
    ok := len + 1 <= res.Length;
    if (ok) {
      var pixel := RGBA(r, g, b, state.prev.a);
      res[len] := pixel;
      newlen := len + 1;
      newstate := updateState(state, pixel);
    }
  case OpRun(size) =>
    {
      var pixel := state.prev;
      var i : int := 0;
      newlen := len;
      newstate := state;
      var pixels := seq(size, j => pixel);
      ok := len + size as int <= res.Length;
      if (ok) {
        while (i < size as int)
        invariant |pixels| == size as int
        invariant newlen == len + i
        invariant 0 <= i <= size as int
        invariant res[len..newlen] == seq(i, j => pixel)
        invariant old(res[..len]) == res[..len]
        invariant validState(newstate)
        invariant updatedState(state, newstate, pixels[..i])
        {
          res[newlen] := pixel;
          newlen := newlen + 1;
          assert 0 <= i < size as int;
          assert pixels[i] == pixel;
          i := i + 1;
          assert pixels[..i] == pixels[..i - 1] + [ pixel ];
          ghost var oldnewstate := newstate;
          newstate := updateState(newstate, pixel);
          updatedStateNext(state, oldnewstate, newstate, pixels[..i - 1], pixel);
          assert updatedState(state, newstate, pixels[..i]);
        }
        assert updatedState(state, newstate, pixels[..size as int]);
        assert pixels[..size as int] == pixels;
        assert newstate == updateStateStar(state, specDecodeOp(state, op));
        assert |specDecodeOp(state, op)| == size as int;
      }
    }
  case OpIndex(index) =>
    ok := len + 1 <= res.Length;
    if (ok) {
      var pixel := state.index[index];
      res[len] := pixel;
      newlen := len + 1;
      newstate := updateState(state, pixel);
    }
  case OpDiff(RGBDiff(dr, dg, db)) =>
    ok := len + 1 <= res.Length;
    if (ok) {
      var pixel := RGBA(add_byte(state.prev.r, byte_from(dr as int)),
      add_byte(state.prev.g, byte_from(dg as int)),
      add_byte(state.prev.b, byte_from(db as int)),
      state.prev.a
      );
      res[len] := pixel;
      newlen := len + 1;
      newstate := updateState(state, pixel);
    }
  case OpLuma(RGBLuma(dr, dg, db)) =>
    ok := len + 1 <= res.Length;
    if (ok) {
      var pixel := RGBA(add_byte(add_byte(state.prev.r, byte_from(dg as int)), byte_from(dr as int)),
      add_byte(state.prev.g, byte_from(dg as int)),
      add_byte(add_byte(state.prev.b, byte_from(dg as int)), byte_from(db as int)),
      state.prev.a
      );
      res[len] := pixel;
      newlen := len + 1;
      newstate := updateState(state, pixel);
    }
  case OpRGBA(rgba) =>
    ok := len + 1 <= res.Length;
    if (ok) {
      var pixel := rgba;
      res[len] := pixel;
      newlen := len + 1;
      newstate := updateState(state, pixel);
    }
  }
}

// Decode a sequence of chunks as the image data
method decodeAEI(ops : array<Op>, size : int) returns (r : array<RGBA>, ok : bool)
  requires size >= 0
  ensures ok == (|specOps(ops[..])| == size)
  ensures r.Length == size
  ensures ok ==> r[..size] == specOps(ops[..])
{
  var i := 0;
  var state := initState();
  var len := 0;
  r := new RGBA [size];
  ok := true;
  while (i < ops.Length)
    invariant 0 <= i <= ops.Length
    invariant 0 <= len <= size
    invariant validState(state)
    invariant len <= size
    invariant state == updateStateStar(initState(), r[..len])
    invariant specOps(ops[..i]) == r[..len]
  {
    ghost var image0 := r[..len];
    ghost var state0 := state;
    assert specOpsAux(ops[..i], initState()) == r[..len];
    var op := ops[i];
    ghost var pixels := specDecodeOp(state, op);
    updateStateStarConcat(initState(), r[..len], state, pixels, updateStateStar(state, pixels));
    var ok' : bool;
    ghost var len0 := len;
    len, state, ok' := decodeOp(state, op, len, r);
    if (!ok')
    {
      assert len0 + |specDecodeOp(state0, op)| > r.Length == size;
      assert len0 == |specOps(ops[..i])|;
      specOpsMonotone(ops[..], i + 1);
      assert |specOps(ops[..])| >= |specOps(ops[..i + 1])|;
      specOpsDecompose(ops[..], i, state0);
      assert |specOps(ops[..i + 1])| == |specOps(ops[..i])| + |specDecodeOp(state0, ops[i])|;
      assert |specOps(ops[..])| > size;
      ok := false;
      return;
    }
    i := i + 1;
    specOpsAuxAssoc(ops[..i], initState());
    assert ops[..i][..|ops[..i]| - 1] == ops[..i - 1];
  }
  if (ok) {
    if (len != size)
    {
      assert len <= size;
      assert specOps(ops[..i]) == r[..len];
      assert specOps(ops[..ops.Length]) == r[..len];
      assert ops[..ops.Length] == ops[..];
      assert specOps(ops[..]) == r[..len];
      assert |specOps(ops[..])| == len;
      assert |specOps(ops[..])| < size;
      ok := false;
      return;
    }
    assert ops[..] == ops[..i];
  }
}

// Interpret a sequence of bytes as a sequence of RGB pixels
function asRGBA3(data : seq<byte>) : seq<RGBA>
  requires |data| % 3 == 0
  ensures toByteStreamRGB(asRGBA3(data)) == data
  ensures |asRGBA3(data)| == |data| / 3
{
  if |data| == 0 then
    []
  else
    [ RGBA(data[0], data[1], data[2], 255) ] + asRGBA3(data[3..])
}

lemma asRGBA3Last(data : seq<byte>)
  requires |data| % 3 == 0
  requires |data| > 0
  ensures asRGBA3(data) == asRGBA3(data[..|data| - 3]) + [ RGBA(data[|data|-3], data[|data|-2], data[|data|-1], 255) ]
{
  if (|data| == 3)
  {
  }
  else
  {
    asRGBA3Last(data[3..]);
    assert asRGBA3(data[3..]) ==
      asRGBA3(data[3..][..|data[3..]| - 3]) +
      [ RGBA(data[3..][|data[3..]|-3], data[3..][|data[3..]|-2], data[3..][|data[3..]|-1], 255) ];
    assert data[3..][|data[3..]| - 3] == data[|data| - 3];
    assert data[3..][|data[3..]| - 2] == data[|data| - 2];
    assert data[3..][|data[3..]| - 1] == data[|data| - 1];
    assert data[3..][..|data[3..]| - 3] == data[3..|data| - 3];
    calc {
      asRGBA3(data);
    ==
      [ RGBA(data[0], data[1], data[2], 255) ] + asRGBA3(data[3..]);
    ==
      [ RGBA(data[0], data[1], data[2], 255) ] +
      asRGBA3(data[3..|data| - 3]) +
      [ RGBA(data[|data| - 3], data[|data| - 2], data[|data| - 1], 255) ];
    ==
      ([ RGBA(data[0], data[1], data[2], 255) ] +
      asRGBA3(data[3..|data| - 3])) +
      [ RGBA(data[|data| - 3], data[|data| - 2], data[|data| - 1], 255) ];
    ==
      asRGBA3(data[..|data| - 3]) + [ RGBA(data[|data|-3], data[|data|-2], data[|data|-1], 255) ];
    }
  }
}

lemma asRGBA4Last(data : seq<byte>)
  requires |data| % 4 == 0
  requires |data| > 0
  ensures asRGBA4(data) == asRGBA4(data[..|data| - 4]) + [ RGBA(data[|data|-4], data[|data|-3], data[|data|-2], data[|data|-1]) ]
{
  if (|data| == 4)
  {
  }
  else
  {
    asRGBA4Last(data[4..]);
    assert asRGBA4(data[4..]) ==
      asRGBA4(data[4..][..|data[4..]| - 4]) +
      [ RGBA(data[4..][|data[4..]|-4], data[4..][|data[4..]|-3], data[4..][|data[4..]|-2], data[4..][|data[4..]|-1]) ];
    assert data[4..][|data[4..]| - 4] == data[|data| - 4];
    assert data[4..][|data[4..]| - 3] == data[|data| - 3];
    assert data[4..][|data[4..]| - 2] == data[|data| - 2];
    assert data[4..][|data[4..]| - 1] == data[|data| - 1];
    assert data[4..][..|data[4..]| - 4] == data[4..|data| - 4];
    calc {
      asRGBA4(data);
    ==
      [ RGBA(data[0], data[1], data[2], data[3]) ] + asRGBA4(data[4..]);
    ==
      [ RGBA(data[0], data[1], data[2], data[3]) ] +
      asRGBA4(data[4..|data| - 4]) +
      [ RGBA(data[|data| - 4], data[|data| - 3], data[|data| - 2], data[|data| - 1]) ];
    ==
      ([ RGBA(data[0], data[1], data[2], data[3]) ] +
      asRGBA4(data[4..|data| - 4])) +
      [ RGBA(data[|data| - 4], data[|data| - 3], data[|data| - 2], data[|data| - 1]) ];
    ==
      asRGBA4(data[..|data| - 4]) + [ RGBA(data[|data|-4], data[|data|-3], data[|data|-2], data[|data| - 1]) ];
    }
  }
}

method toRGBA3(data : seq<byte>) returns (result : array<RGBA>)  
  requires |data| % 3 == 0
  ensures result.Length == |data| / 3
  ensures toByteStreamRGB(result[..]) == data
  ensures result[..] == asRGBA3(data)
{
  result := new RGBA [|data| / 3];
  var i := 0;
  var i3 := 0;
  while (i < |data|)
    invariant i == i3 * 3
    invariant 0 <= i <= |data|
    invariant result[..i3] == asRGBA3(data[..i])
    invariant toByteStreamRGB(result[..i3]) == data[..i]
  {
    result[i3] := RGBA(data[i + 0], data[i + 1], data[i + 2], 255);
    i := i + 3;
    i3 := i3 + 1;
    assert result[..i3 - 1] == asRGBA3(data[..i - 3]);
    assert result[i3 - 1] == RGBA(data[i - 3], data[i - 2], data[i - 1], 255);
    asRGBA3Last(data[..i]);
    assert data[..i][..i - 3] == data[..i - 3];
    assert data[..i][i - 3] == data[i - 3];
    assert data[..i][i - 2] == data[i - 2];
    assert data[..i][i - 1] == data[i - 1];
  }
  assert i == |data|;
  assert data == data[..i];
  assert i3 == result.Length;
  assert result[..] == result[..i3];
}

// Interpret a sequence of bytes as a sequence of RGBA pixels
function asRGBA4(data : seq<byte>) : seq<RGBA>
  requires |data| % 4 == 0
  ensures toByteStreamRGBA(asRGBA4(data)) == data
  ensures |asRGBA4(data)| == |data| / 4
{
  if |data| == 0 then
    []
  else
    [ RGBA(data[0], data[1], data[2], data[3]) ] + asRGBA4(data[4..])
}

method toRGBA4(data : seq<byte>) returns (result : array<RGBA>)  
  requires |data| % 4 == 0
  ensures result.Length == |data| / 4
  ensures toByteStreamRGBA(result[..]) == data
  ensures result[..] == asRGBA4(data)
{
  result := new RGBA [|data| / 4];
  var i := 0;
  var i4 := 0;
  while (i < |data|)
    invariant i == i4 * 4
    invariant 0 <= i <= |data|
    invariant result[..i4] == asRGBA4(data[..i])
    invariant toByteStreamRGBA(result[..i4]) == data[..i]
  {
    result[i4] := RGBA(data[i + 0], data[i + 1], data[i + 2], data[i + 3]);
    i := i + 4;
    i4 := i4 + 1;
    assert result[..i4 - 1] == asRGBA4(data[..i - 4]);
    assert result[i4 - 1] == RGBA(data[i - 4], data[i - 3], data[i - 2], data[i - 1]);
    asRGBA4Last(data[..i]);
    assert data[..i][..i - 4] == data[..i - 4];
    assert data[..i][i - 4] == data[i - 4];
    assert data[..i][i - 3] == data[i - 3];
    assert data[..i][i - 2] == data[i - 2];
    assert data[..i][i - 1] == data[i - 1];
  }
  assert i == |data|;
  assert data == data[..i];
  assert i4 == result.Length;
  assert result[..] == result[..i4];
}

// Interpret a sequence of bytes as a sequence of RGBA pixels
function asRGBA(data : seq<byte>, desc : Desc) : seq<RGBA>
  requires |data| == desc.width as int * desc.height as int * desc.channels as int
  ensures toByteStream(desc, asRGBA(data, desc)) == data
  ensures |asRGBA(data, desc)| == desc.width as int * desc.height as int
{
  if desc.channels == 3 then
    asRGBA3(data)
  else 
    asRGBA4(data)
}

method toRGBA(data : seq<byte>, desc : Desc) returns (result : array<RGBA>)  
  requires |data| == desc.width as int * desc.height as int * desc.channels as int
  ensures toByteStream(desc, result[..]) == data
  ensures result.Length == desc.width as int * desc.height as int
  ensures result[..] == asRGBA(data, desc)
{
  if (desc.channels == 3)
  {
    result := toRGBA3(data);
  }
  else
  {
    result := toRGBA4(data);
  }
}

// Create the header for an image
method writeHeader(desc : Desc, result : array<byte>) returns (len : int)
  requires result.Length >= |specHeader(desc)|
  modifies result
  ensures 0 <= len <= result.Length
  ensures result[0..len] == specHeader(desc)
  ensures len == |specHeader(desc)|
{
  result[0] := 'q' as byte;
  result[1] := 'o' as byte;
  result[2] := 'i' as byte;
  result[3] := 'f' as byte;
  result[4] := unpack(desc.width)[0];
  result[5] := unpack(desc.width)[1];
  result[6] := unpack(desc.width)[2];
  result[7] := unpack(desc.width)[3];
  result[8] := unpack(desc.height)[0];
  result[9] := unpack(desc.height)[1];
  result[10] := unpack(desc.height)[2];
  result[11] := unpack(desc.height)[3];
  result[12] := desc.channels as byte;
  result[13] := byteFromColorSpace(desc.colorSpace);
  len := 14;
}

// Create the header for an image
method writeFooter(result : array<byte>, pos : int) returns (newpos : int)
  requires 14 <= pos < pos + 8 <= result.Length
  modifies result
  ensures pos <= newpos <= result.Length
  ensures result[0..14] == old(result[0..14])
  ensures result[14..pos] == old(result[14..pos])
  ensures result[pos..newpos] == specFooter()
  ensures newpos == pos + 8
{
  result[pos + 0] := 0 as byte;
  result[pos + 1] := 0 as byte;
  result[pos + 2] := 0 as byte;
  result[pos + 3] := 0 as byte;
  result[pos + 4] := 0 as byte;
  result[pos + 5] := 0 as byte;
  result[pos + 6] := 0 as byte;
  result[pos + 7] := 1 as byte;
  newpos := pos + 8;
}

method writeBitsOp(op : Op, result : array<byte>, pos : int) returns (newpos : int)
  requires 14 <= pos < pos + 5 <= result.Length
  modifies result
  ensures 14 <= pos <= newpos <= result.Length
  ensures result[0..14] == old(result[0..14])
  ensures result[14..pos] == old(result[14..pos])
  ensures result[pos..newpos] == encodeOpSpec(op)
{
  newpos := pos + 1;
  match op
  {
  case OpRun(size) =>
    result[pos] := 128 + 64 + (size as int - 1) as byte;
  case OpIndex(index) =>
    result[pos] := index as byte;
  case OpDiff(diff) =>
    result[pos] := 64 +
    16 * encodeDiff(diff.dr) +
    4 * encodeDiff(diff.dg) +
    encodeDiff(diff.db);
  case OpLuma(luma) =>
    result[pos + 0] := 128 + encodeDiff64(luma.dg);
    result[pos + 1] := 16 * encodeDiff16(luma.dr) + encodeDiff16(luma.db);
    newpos := pos + 2;
  case OpRGB(rgb) =>
    result[pos + 0] := 254;
    result[pos + 1] := rgb.r;
    result[pos + 2] := rgb.g;
    result[pos + 3] := rgb.b;
    newpos := pos + 4;
  case OpRGBA(rgba) =>
    result[pos + 0] := 255;
    result[pos + 1] := rgba.r;
    result[pos + 2] := rgba.g;
    result[pos + 3] := rgba.b;
    result[pos + 4] := rgba.a;
    newpos := pos + 5;
  }
}

method encodeBitsOps(ops : array<Op>, opsLen : int, result : array<byte>, pos : int) returns (newpos : int)
  requires 0 <= opsLen <= ops.Length
  requires 14 == pos <= result.Length
  requires pos + 5 * opsLen + 8 <= result.Length
  modifies result
  ensures newpos + 8 <= result.Length
  ensures pos <= newpos <= result.Length
  ensures result[0..14] == old(result[0..14])
  ensures result[pos..newpos] == encodeOpsSpec(ops[..opsLen])
  ensures validBitSeq(result[pos..newpos])
{
  var i := 0;
  newpos := pos;
  while (i < opsLen)
    invariant 0 <= i <= opsLen
    invariant pos <= newpos
    invariant newpos + 5 * (opsLen - i) + 8 <= result.Length
    invariant result[..pos] == old(result[..pos])
    invariant result[pos..newpos] == encodeOpsSpec(ops[..i])
  {
    ghost var oldpos := newpos;
    newpos := writeBitsOp(ops[i], result, newpos);
    i := i + 1;
    encodeOpsSpecLast(ops[..i]);    assert init(ops[..i]) == ops[..i-1];
    assert result[pos..oldpos] == encodeOpsSpec(init(ops[..i]));
    assert result[oldpos..newpos] == encodeOpSpec(last(ops[..i]));
    assert result[pos..oldpos] + result[oldpos..newpos] ==
      encodeOpsSpec(ops[..i - 1]) + encodeOpSpec(ops[i - 1]);
    assert result[pos..oldpos] + result[oldpos..newpos] == encodeOpsSpec(ops[..i]);
 }
}

lemma resultOk(image : Image, result : array<byte>, len : int, ops : array<Op>, opsLen : int)
  requires validImage(image)
  requires 0 <= 14 + 8 <= len <= result.Length
  requires 0 <= opsLen <= ops.Length
  
  requires result[0..14] == specHeader(image.desc)
  requires result[14..len-8] == encodeOpsSpec(ops[..opsLen])
  requires result[len-8..len] == specFooter()
  requires validBitSeq(result[14..len-8])
  requires specOps(ops[..opsLen]) == asRGBA(image.data, image.desc)
  ensures validByteStream(result[0..len])
  ensures image == specEndToEnd(result[..len])
{
  ghost var byteStream := result[0..len];
  assert byteStream[0..14] == result[0..14];
  assert byteStream[14..len-8] == result[14..len-8];
  assert byteStream[len-8..] == result[len-8..len];
  assert |byteStream| >= 14 + 8;
  assert validHeader(byteStream[0..14]);
  assert validFooter(byteStream[len - 8..]);
  encode_decode_ops(ops[..opsLen]);
  assert validBitSeq(byteStream[14..len-8]);
  assert specBits(byteStream[14..len-8]) == ops[..opsLen];
  assert specOps(ops[..opsLen]) == asRGBA(image.data, image.desc);
  assert |specOps(specBits(byteStream[14..len-8]))| ==
    image.desc.width as int *
    image.desc.height as int;
  specHeader_same(image.desc);
  assert specHeaderDesc(specHeader(image.desc)).width == image.desc.width;
  assert specHeaderDesc(specHeader(image.desc)).height == image.desc.height;
}



// Encode an image as a sequence of bytes
method encodeAll(image : Image) returns (result : array<byte>, len : int)
  requires validImage(image)
  ensures 0 <= len <= result.Length
  ensures validByteStream(result[..len])
  ensures image == specEndToEnd(result[..len])
{
  var ops : array<Op>;
  var opsLen : int;
  var arrayRGBA := toRGBA(image.data, image.desc);
  ops, opsLen := encodeAEI(arrayRGBA[..]);
  assert specOps(ops[..opsLen]) == asRGBA(image.data, image.desc);
  result := new byte [ opsLen * 5 as int + 14 + 8 ];
  len := writeHeader(image.desc, result);
  len := encodeBitsOps(ops, opsLen, result, len);
  len := writeFooter(result, len);

  resultOk(image, result, len, ops, opsLen);
}

// Extract image metadata from header
method parseHeader(byteStream : seq<byte>) returns (r : Option<Desc>)
  requires |byteStream| == 14
  ensures validHeader(byteStream[0..14]) ==> r.Some? && r.some == specHeaderDesc(byteStream[0..14])
  ensures !validHeader(byteStream[0..14]) ==> r.None?
{
  if byteStream[0..4] != [ 'q' as byte, 'o' as byte, 'i' as byte, 'f' as byte ] {
    return None;
  }
  if 3 <= byteStream[12] <= 4 && validColorSpaceAsByte(byteStream[13]) {
    var desc := Desc(
    pack(byteStream[4..8]),
    pack(byteStream[8..12]),
    byteStream[12] as Channels,
    colorSpaceFromByte(byteStream[13]));
    pack_unpack(byteStream[4..8]);
    pack_unpack(byteStream[8..12]);
    assert specHeader(desc) == byteStream[0..14];
    assert validHeader(byteStream[0..14]);
    return Some(desc);
  }
  return None;
}

// Decode a sequence of bytes as an image
method decodeAll(byteStream : array<byte>) returns (r : Option<Image>)
  //ensures !validByteStream(byteStream) ==> r.None?
  //ensures validByteStream(byteStream) ==> r.Some? && r.some == specEndToEnd(byteStream)
{
  if (byteStream.Length < 14 + 8) {
    return None;
  } else {
    var len := byteStream.Length;
    var header := byteStream[..14];
    var footer := byteStream[len - 8..];
    if (footer != specFooter()) {
      return None;
    }
    var descOption := parseHeader(header);
    if (descOption.None?) {
      return None;
    }
    var desc := descOption.some;
    var opsOption;
    var len';
    opsOption, len' := decodeBitsOps(byteStream, 14, len - 8);
    if (opsOption.None?) {
      return None;
    }
    var ops := opsOption.some;
    var rgbs : array<RGBA>;
    var ok : bool;
    rgbs, ok := decodeAEI(ops, desc.width as int * desc.height as int);
    if (ok) {
      var data := toByteStream(desc, rgbs[..]);
      if rgbs.Length != desc.width as int * desc.height as int {
        return None;
      }
      return Some(Image(desc, data));
    } else {
      return None;
    }
  }
}
