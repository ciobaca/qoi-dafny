datatype Option<T> = None | Some(some:T)

newtype {:nativeType "byte"} byte = x : int | 0 <= x < 256
newtype {:nativeType "uint"} uint32 = x : int | 0 <= x < 4294967296

// modular arithmetic
function add_byte(x : byte, y : byte) : byte
{
  ((x as int + y as int) % 256) as byte
}

// modular arithmetic
function sub_byte(x : byte, y : byte) : byte
{
  (((x as int) + (256 - y as int)) % 256) as byte
}

lemma add_sub(x : byte, y : byte)
  ensures sub_byte(add_byte(x, y), y) == x
{
}

function byte_from(x : int) : byte
{
  (x % 256) as byte
}

// uint32 as sequence of 4 bytes
function unpack(x : uint32) : seq<byte>
  ensures |unpack(x)| == 4
{
  var b0 : byte := ((x / (256 * 256 * 256)) % 256) as byte;
  var b1 : byte := ((x / (256 * 256)) % 256) as byte;
  var b2 : byte := ((x / 256) % 256) as byte;
  var b3 : byte := (x % 256) as byte;
  [ b0, b1, b2, b3 ]
}

// 4 bytes as uint32
function pack(x : seq<byte>) : uint32
  requires |x| == 4
{
  (x[0] as uint32) * 16777216 + (x[1] as uint32) * 65536 + (x[2] as uint32) * 256 + (x[3] as uint32)
}

lemma pack_unpack(x : seq<byte>)
  requires |x| == 4
  ensures unpack(pack(x)) == x
{
}

lemma unpack_pack(x : uint32)
  ensures pack(unpack(x)) == x
{
}
