newtype {:nativeType "byte"} byte = x : int | 0 <= x < 256

function method add_byte(x : byte, y : byte) : byte
{
  ((x as int + y as int) % 256) as byte
}
  
method test()
{
  var x1 : byte := 255;
  var x2 : byte := 0;
  assert add_byte(x1, 1) == x2;
}
