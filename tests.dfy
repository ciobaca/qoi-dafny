include "qoi.dfy"

method test(i : int) returns (r : seq<RGBA>)
  requires 0 <= i <= 2
  ensures |r| == 3
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
  ensures validImage(r)
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
