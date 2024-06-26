/*
Dafny implementation of encoder and decoder for the QOI image format.

https://qoiformat.org/qoi-specification.pdf

(C) Stefan Ciobaca 2023-2024
 */

include "helper.dfy"
include "spec.dfy"

// Signed delta as unsigned byte
function encodeDiff64(diff : Diff64) : byte
  ensures 0 <= encodeDiff64(diff) <= 63
{
  (diff as int + 32) as byte
}

// Signed delta as unsigned byte
function encodeDiff16(diff : Diff16) : byte
  ensures 0 <= encodeDiff16(diff) <= 15
{
  (diff as int + 8) as byte
}

// Signed delta as unsigned byte
function encodeDiff(diff : Diff) : byte
  ensures 0 <= encodeDiff(diff) <= 3
{
  (diff as int + 2) as byte
}

// Encode a chunk as a sequence of bytes
function encodeOpSpec(op : Op) : seq<byte>
  ensures validBits(encodeOpSpec(op))
  ensures sizeBitEncoding(opTypeOfOp(op)) == |encodeOpSpec(op)|
  ensures decodeBits(encodeOpSpec(op)) == op
{
  match op
  {
  case OpRun(size) =>
    [ 128 + 64 + (size as int - 1) as byte ]
  case OpIndex(index) =>
    [ index as byte ]
  case OpDiff(diff) =>
    [ 64 +
    16 * encodeDiff(diff.dr) +
    4 * encodeDiff(diff.dg) +
    encodeDiff(diff.db) ]
  case OpLuma(luma) =>
    [
    128 + encodeDiff64(luma.dg),
    16 * encodeDiff16(luma.dr) +
    encodeDiff16(luma.db)
    ]
  case OpRGB(rgb) =>
    [ 254,
    rgb.r,
    rgb.g,
    rgb.b
    ]
  case OpRGBA(rgba) =>
    [ 255,
    rgba.r,
    rgba.g,
    rgba.b,
    rgba.a
    ]
  }
}

// Types of chunks
datatype OpType = TypeRun | TypeIndex | TypeDiff | TypeLuma | TypeRGB | TypeRGBA

// Return the chunk type out of the first byte
function opTypeOfBits(bits : byte) : OpType
{
  if bits == 254 then
    TypeRGB
  else if bits == 255 then
    TypeRGBA
  else if bits >= 128 + 64 then
    TypeRun
  else if bits >= 128 then
    TypeLuma
  else if bits >= 64 then
    TypeDiff
  else
    TypeIndex
}

// Extract the chunk type from a chunk
function opTypeOfOp(op : Op) : OpType
{
  match op
  {
  case OpRun(size : Size) =>
    TypeRun
  case OpIndex(index : Index64) =>
    TypeIndex
  case OpDiff(diff : RGBDiff) =>
    TypeDiff
  case OpLuma(luma : RGBLuma) =>
    TypeLuma
  case OpRGB(rgb : RGB) =>
    TypeRGB
  case OpRGBA(rgba : RGBA) =>
    TypeRGBA
  }
}

// Sanity check
lemma opTypeOfBits_correct(op : Op)
  ensures opTypeOfOp(op) == opTypeOfBits(encodeOpSpec(op)[0])
{
}

// Number of bytes in the encoding of each chunk type
function sizeBitEncoding(opType : OpType) : int
{
  match opType
  {
  case TypeRun =>
    1
  case TypeIndex =>
    1
  case TypeDiff =>
    1
  case TypeLuma =>
    2
  case TypeRGB =>
    4
  case TypeRGBA =>
    5
  }
}

// The byte sequence represents a valid encoding of a chunk
function validBits(bits : seq<byte>) : bool
{
  |bits| > 0 &&
    match opTypeOfBits(bits[0])
    {
    case TypeRun =>
      |bits| == 1 && bits[0] >= 128 + 64 && bits[0] - 128 - 64 <= 61
    case TypeLuma =>
      |bits| == 2 && bits[0] >= 128 && bits[0] < 128 + 64
    case TypeDiff =>
      |bits| == 1 &&
      bits[0] >= 64 && bits[0] < 128
    case TypeIndex =>
      |bits| == 1 &&
      bits[0] < 64
    case TypeRGBA =>
      |bits| == 5 &&
      bits[0] == 255
    case TypeRGB =>
      |bits| == 4 &&
      bits[0] == 254
    }
}

method areValidBits(bits : array<byte>, start : int, len : int) returns (b : bool)
  requires 0 <= start <= start + len <= bits.Length
  ensures b == validBits(bits[start..start + len])
{
  b := len > 0 &&
    match opTypeOfBits(bits[start + 0])
    {
    case TypeRun =>
      len == 1 && bits[start + 0] >= 128 + 64 && bits[start + 0] - 128 - 64 <= 61
    case TypeLuma =>
      len == 2 && bits[start + 0] >= 128 && bits[start + 0] < 128 + 64
    case TypeDiff =>
      len == 1 &&
      bits[start + 0] >= 64 && bits[start + 0] < 128
    case TypeIndex =>
      len == 1 &&
      bits[start + 0] < 64
    case TypeRGBA =>
      len == 5 &&
      bits[start + 0] == 255
    case TypeRGB =>
      len == 4 &&
      bits[start + 0] == 254
    };
}

// Decode a chunk-as-bits into an abstract chunk
function decodeBits(bits : seq<byte>) : Op
  requires validBits(bits)
{
  match opTypeOfBits(bits[0])
  {
  case TypeRun =>
    assert |bits| == 1 && bits[0] >= 128 + 64 && bits[0] - 128 - 64 <= 61;
    OpRun((bits[0] - 128 - 64 + 1) as Size)
  case TypeLuma =>
    OpLuma(
    RGBLuma(
    ((bits[1] / 16) as int - 8) as Diff16,
    ((bits[0] - 128) as int - 32) as Diff64,
    ((bits[1] % 16) as int - 8) as Diff16))
  case TypeDiff =>
    assert bits[0] < 128;
    OpDiff(
    RGBDiff(
    (((bits[0] - 64) / 16) as int - 2) as Diff,
    (((bits[0] / 4) % 4) as int - 2) as Diff,
    ((bits[0] % 4) as int - 2) as Diff))
  case TypeIndex =>
    OpIndex(bits[0] as Index64)
  case TypeRGBA =>
    OpRGBA(RGBA(bits[1], bits[2], bits[3], bits[4]))
  case TypeRGB =>
    OpRGB(RGB(bits[1], bits[2], bits[3]))
  }
}

// Check if a sequence of bytes represents a sequence of chunks
predicate validBitSeq(bits : seq<byte>)
{
  |bits| == 0 ||
    (
    var len := sizeBitEncoding(opTypeOfBits(bits[0]));
    |bits| >= len &&
    validBits(bits[0..len]) &&
    validBitSeq(bits[len..]))
}

lemma encode_decode_ops(ops : seq<Op>)
  ensures validBitSeq(encodeOpsSpec(ops))
  ensures specBits(encodeOpsSpec(ops)) == ops
{
}

// Encode a sequence of chunks as a sequence of bytes
function encodeOpsSpec(ops : seq<Op>) : seq<byte>
  ensures validBitSeq(encodeOpsSpec(ops))
  ensures specBits(encodeOpsSpec(ops)) == ops
{
  if |ops| == 0 then
    []
  else
    encodeOpSpec(head(ops)) + encodeOpsSpec(tail(ops))
}

function head<T>(l : seq<T>) : T
  requires |l| > 0
{
  l[0]
}

function tail<T>(l : seq<T>) : seq<T>
  requires |l| > 0
{
  l[1..]
}

function init<T>(l : seq<T>) : seq<T>
  requires |l| > 0
{
  l[..|l| - 1]
}

function last<T>(l : seq<T>) : T
  requires |l| > 0
{
  l[|l| - 1]
}

lemma head_init<T>(l : seq<T>)
  requires |l| >= 2
  ensures head(init(l)) == head(l)
{
}

lemma last_tail<T>(l : seq<T>)
  requires |l| >= 2
  ensures last(tail(l)) == last(l)
{
}

lemma init_tail_comm<T>(l : seq<T>)
  requires |l| >= 2
  ensures init(tail(l)) == tail(init(l))
{
}

lemma encodeOpsSpecLast(ops : seq<Op>)
  requires |ops| > 0
  ensures encodeOpsSpec(ops) == encodeOpsSpec(init(ops)) + encodeOpSpec(last(ops))
{
  if (|ops| == 1)
  {
  }
  else
  {
    calc {
      encodeOpsSpec(ops);
    ==
      encodeOpSpec(head(ops)) +
      encodeOpsSpec(tail(ops));
    ==
      encodeOpSpec(head(ops)) +
      encodeOpsSpec(init(tail(ops))) +
      encodeOpSpec(last(tail(ops)));
    == { encodeOpsSpecLast(tail(ops)); }
      encodeOpSpec(head(ops)) +
      encodeOpsSpec(init(tail(ops))) +
      encodeOpSpec(last(tail(ops)));
    == { head_init(ops); }
      encodeOpSpec(head(init(ops))) +
      encodeOpsSpec(init(tail(ops))) +
      encodeOpSpec(last(tail(ops)));
    == { init_tail_comm(ops); last_tail(ops); }
      encodeOpSpec(head(init(ops))) +
      encodeOpsSpec(tail(init(ops))) +
      encodeOpSpec(last(ops));
    ==
      (encodeOpSpec(head(init(ops))) +
      encodeOpsSpec(tail(init(ops)))) +
      encodeOpSpec(last(ops));
    == { assert encodeOpsSpec(init(ops)) == encodeOpSpec(head(init(ops))) + encodeOpsSpec(tail(init(ops))); }
      encodeOpsSpec(init(ops)) +
      encodeOpSpec(last(ops));
    }
    assert encodeOpsSpec(ops) == encodeOpsSpec(init(ops)) + encodeOpSpec(last(ops));
  }
}

// Decode a sequence of bytes as a sequence of chunks
function specBits(bits : seq<byte>) : seq<Op>
  requires validBitSeq(bits)
{
  if |bits| == 0 then
    []
  else
    (
    var len := sizeBitEncoding(opTypeOfBits(bits[0]));
    [ decodeBits(bits[0..len]) ] + specBits(bits[len..])
    )
}

// Decode a sequence of bytes; return None if invalid
lemma helperDecode2(bits : seq<byte>, i : int)
  requires 0 <= i <= |bits|
  requires validBits(bits[i..])
  requires validBitSeq(bits[..i])
  ensures validBitSeq(bits)
  ensures specBits(bits[..]) == specBits(bits[..i]) + [ decodeBits(bits[i..]) ]
{
  if (|bits[..i]| == 0)
  {
  }
  else
  {
    assert bits[0] == bits[..i][0];
    var len := sizeBitEncoding(opTypeOfBits(bits[0]));
    assert |bits[..i]| >= len;
    assert len <= i;
    assert validBits(bits[..i][0..len]);
    assert validBitSeq(bits[..i][len..]);
    assert bits[..i][len..] == bits[len..i];
    assert validBitSeq(bits[len..i]);
    assert bits[len..][..i - len] == bits[len..i];
    helperDecode2(bits[len..], i - len);
  }
}

lemma helperSegment(bits : array<byte>, start : int, i : int, len : int)
  requires 0 <= start <= start + i <= bits.Length
  requires 0 <= len <= i
  ensures bits[start..start + i][..i - len] == bits[start..start + i - len]
{
  
}
  
method decodeBitsOps(bits : array<byte>, start : int, end : int) returns (r : Option<array<Op>>, lenr : int)
  requires 0 <= start <= end <= bits.Length
  ensures !validBitSeq(bits[start..end]) ==> r.None?
  ensures r.Some? ==> 0 <= lenr <= r.some.Length
  ensures validBitSeq(bits[start..end]) ==>
  r.Some? && r.some[..lenr] == specBits(bits[start..end])
{
  var i := 0;
  var j := 0;
  var result : array<Op> := new Op [end - start];
  while (i < end - start)
    invariant 0 <= j <= i <= end - start
    invariant validBitSeq(bits[start + i..end]) == validBitSeq(bits[start..end])
    invariant validBitSeq(bits[start..start + i])
    invariant result[..j] == specBits(bits[start..start + i])
  {
    var len := sizeBitEncoding(opTypeOfBits(bits[start + i]));
    assert len > 0;
    if (i + len > end - start)
    {
      assert |bits[start + i..end]| == end - start - i;
      assert len > end - start - i;
      assert !validBitSeq(bits[start + i..end]);
      assert !validBitSeq(bits[start..end]);
      return None, j;
    }
    else
    {
      var b := areValidBits(bits, start + i, len);
      if (b)
      {
        //assert validBits(bits[start + i..start + i + len]);
        //assert len > 0;
        assert bits[start + i..end][len..] == bits[start + i + len..end];
        result[j] := decodeBits(bits[start + i..start + i + len]);
        j := j + 1;
        i := i + len;
        calc {
          bits[start..start + i][..i - len];
        == { helperSegment(bits, start, i, len); }
          bits[start..start + i - len];
        }
        assert validBitSeq(bits[start..start + i][..i - len]);
        helperDecode2(bits[start..start + i], i - len);
        assert result[..j - 1] == specBits(bits[start..start + i - len]);
        assert result[..j] == specBits(bits[start..start + i]);
        assert validBitSeq(bits[start + i..end]) == validBitSeq(bits[start..end]);
      }
      else
      {
        assert !validBitSeq(bits[start + i..end]);
        assert !validBitSeq(bits[start..end]);
        return None, j;
      }
    }
  }
  assert validBitSeq(bits[start..start + i]);
  assert bits[start..end] == bits[start..start + i];
  return Some(result), j;
}

lemma specHeaderValid(desc : Desc)
  ensures validHeader(specHeader(desc))
  ensures specHeaderDesc(specHeader(desc)) == desc
{
}

// Create the header from the image metadata
function specHeader(desc : Desc) : seq<byte>
{
  [ 'q' as byte, 'o' as byte, 'i' as byte, 'f' as byte ]
    + unpack(desc.width)
    + unpack(desc.height)
    + [ desc.channels as byte ]
    + [ byteFromColorSpace(desc.colorSpace) ]
}

// Is this sequence of bytes a valid QOI header?
predicate validHeader(bits : seq<byte>)
{
  |bits| == 14 &&
    bits[0..4] == [ 'q' as byte, 'o' as byte, 'i' as byte, 'f' as byte ] &&
    3 <= bits[12] <= 4 &&
    0 <= bits[13] <= 1
    //exists desc :: bits == genHeader(desc)
}

// Decode a header as metadata
function specHeaderDesc(header : seq<byte>) : Desc
  requires validHeader(header)
{
  Desc(
    pack(header[4..8]),
    pack(header[8..12]),
    header[12] as Channels,
    colorSpaceFromByte(header[13])
    )
}

lemma specHeader_same(desc : Desc)
  ensures specHeaderDesc(specHeader(desc)) == desc
{
}

// The footer consists of 7 zeroes and 1 one.
function specFooter() : seq<byte>
{
  seq(7, i => 0 as byte) + [ 1 as byte ]
}

predicate validFooter(bits : seq<byte>)
{
  bits == specFooter()
}

// The byteStream contains a valid image
predicate validByteStream(byteStream : seq<byte>)
{
  var len := |byteStream|;
  |byteStream| >= 14 + 8 &&
    validHeader(byteStream[0..14]) &&
    validFooter(byteStream[len - 8..]) &&
    validBitSeq(byteStream[14..len-8]) &&
    |specOps(specBits(byteStream[14..len-8]))| ==
    specHeaderDesc(byteStream[0..14]).width as int *
    specHeaderDesc(byteStream[0..14]).height as int
}

// Which image does the byteStream correspond to?
function specEndToEnd(byteStream : seq<byte>) : Image
  requires validByteStream(byteStream)
{
  var desc := specHeaderDesc(byteStream[..14]);
  var len := |byteStream|;
  Image(desc, toByteStream(desc, specOps(specBits(byteStream[14..len-8]))))
}

// Convert colorSpace to/from a byte
function byteFromColorSpace(colorSpace : ColorSpace) : byte
{
  match colorSpace
  {
  case SRGB =>
    0
  case Linear =>
    1
  }
}

predicate validColorSpaceAsByte(b : byte)
{
  b == 0 || b == 1
}

function colorSpaceFromByte(b : byte) : ColorSpace
  requires validColorSpaceAsByte(b)
{
  if b == 0 then
    SRGB
  else
    Linear
}
