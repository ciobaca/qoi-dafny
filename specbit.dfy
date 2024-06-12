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
function encodeBits(op : Op) : seq<byte>
  ensures validBits(encodeBits(op))
  ensures sizeBitEncoding(opTypeOfOp(op)) == |encodeBits(op)|
  ensures decodeBits(encodeBits(op)) == op
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
  ensures opTypeOfOp(op) == opTypeOfBits(encodeBits(op)[0])
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

// Encode a sequence of chunks as a sequence of bytes
function encodeBitSeq(ops : seq<Op>) : seq<byte>
  ensures validBitSeq(encodeBitSeq(ops))
  ensures decodeBitSeqSure(encodeBitSeq(ops)) == ops
{
  if |ops| == 0 then
    []
  else
    encodeBits(ops[0]) + encodeBitSeq(ops[1..])
}

// Decode a sequence of bytes as a sequence of chunks
function decodeBitSeqSure(bits : seq<byte>) : seq<Op>
  requires validBitSeq(bits)
{
  if |bits| == 0 then
    []
  else
    (
    var len := sizeBitEncoding(opTypeOfBits(bits[0]));
    [ decodeBits(bits[0..len]) ] + decodeBitSeqSure(bits[len..])
    )
}

// Decode a sequence of bytes; return None if invalid
method decodeBitSeq(bits : seq<byte>) returns (r : Option<seq<Op>>)
  ensures !validBitSeq(bits) ==> r.None?
  ensures validBitSeq(bits) ==> r.Some? && r.some == decodeBitSeqSure(bits)
{
  if |bits| == 0 {
    r := Some([]);
  } else {
    var len := sizeBitEncoding(opTypeOfBits(bits[0]));
    if |bits| < len {
      return None;
    } else {
      if validBits(bits[0..len]) {
        var rec := decodeBitSeq(bits[len..]);
        if rec.None? {
          return None;
        } else {
          r := Some([ decodeBits(bits[0..len]) ] + rec.some);
        }
      } else {
        return None;
      }
    }
  }
}

// Create the header from the image metadata
function genHeader(desc : Desc) : seq<byte>
  ensures validHeader(genHeader(desc))
  ensures specHeader(genHeader(desc)) == desc
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
function specHeader(header : seq<byte>) : Desc
  requires validHeader(header)
{
  Desc(
    pack(header[4..8]),
    pack(header[8..12]),
    header[12] as Channels,
    colorSpaceFromByte(header[13])
    )
}

// The footer consists of 7 zeroes and 1 one.
function genFooter() : seq<byte>
{
  seq(7, i => 0 as byte) + [ 1 as byte ]
}

predicate validFooter(bits : seq<byte>)
{
  bits == genFooter()
}

// The byteStream contains a valid image
predicate validByteStream(byteStream : seq<byte>)
{
  var len := |byteStream|;
  |byteStream| >= 14 + 8 &&
    validHeader(byteStream[..14]) &&
    validFooter(byteStream[len - 8..]) &&
    validBitSeq(byteStream[14..len-8]) &&
    |specOps(decodeBitSeqSure(byteStream[14..len-8]))| ==
    specHeader(byteStream[..14]).width as int *
    specHeader(byteStream[..14]).height as int
}

// Which image does the byteStream correspond to?
function specEndToEnd(byteStream : seq<byte>) : Image
  requires validByteStream(byteStream)
{
  var desc := specHeader(byteStream[..14]);
  var len := |byteStream|;
  Image(desc, toByteStream(desc, specOps(decodeBitSeqSure(byteStream[14..len-8]))))
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
