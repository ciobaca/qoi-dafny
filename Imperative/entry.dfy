include "helper.dfy"
include "file_input.dfy"
include "qoi.dfy"

import opened Byte

method Main()
{
  var input : array<byte> := FileInput.Reader.getContent();
  if (input.Length < 8)
  {
    print "Invalid input";
  }
  else
  {
    var b := FileInput.Reader.shouldEncode();
    if (b)
    {
      print "Encoding", "\n";
      var width : uint32 := pack(input[0..4]);
      var height : uint32 := pack(input[4..8]);
      print "Width = ", width, "\n";
      print "Height = ", height, "\n";
      if (input.Length as int - 8 != width as int * height as int * 3)
      {
        print "Invalid input (width * height)";
      }
      else
      {
        print "Building image\n";
        var image : Image := Image(Desc(width, height, 3, SRGB), input[8..]);
        var result : array<byte>;
        var len : int;
        print "Start encoding\n";
        result, len := encodeAll(image);
        var repeat := 0;
        while (repeat < 99)
          invariant 0 <= repeat <= 99
        {
          print repeat;
          input := FileInput.Reader.getContent();
          image := Image(Desc(width, height, 3, SRGB), input[8..]);
          result, len := encodeAll(image);
          repeat := repeat + 1;
        }
        //var s : seq<byte> := result[..len];
        //var towrite : array<byte> := new byte [len];
        // var i := 0;
        // while (i < |s|)
        //   invariant 0 <= i <= |s|
        // {
        //   result[i] := s[i];
        //   i := i + 1;
        // }
        // var towrite : array<byte> := new byte [len];
        // assert len >= 0;
         // var i := 0;
         // while (i < len)
         //  invariant 0 <= i <= len
         // {
         //  towrite[i] := result[i];
         //  i := i + 1;
         // }
        if (0 <= len < 4294967296) {
          FileInput.Reader.putContent(result, len as uint32);
        } else {
          print "Error: buffer too big";
        }
      }
    }
    else
    {
      print "Decoding";
      var result : Option<Image> := decodeAll(input);
      var repeat := 0;
      while (repeat < 9)
        invariant 0 <= repeat <= 10
      {
        print repeat;
        var myinput := FileInput.Reader.getContent();
        result := decodeAll(myinput);
        //print result.Some?;
        repeat := repeat + 1;
      }
      if (result.None?)
      {
        print "Invalid encoding";
      }
      else
      {
        var image : Image := result.some;
        var w : uint32 := image.desc.width;
        var h : uint32 := image.desc.height;
        var ws := unpack(w);
        var hs := unpack(h);
        var buffer : array<byte> := new byte [8 + |image.data|];
        buffer[0] := ws[0];
        buffer[1] := ws[1];
        buffer[2] := ws[2];
        buffer[3] := ws[3];
        buffer[4] := hs[0];
        buffer[5] := hs[1];
        buffer[6] := hs[2];
        buffer[7] := hs[3];
        var i : int := 0;
        while (i < |image.data|)
          invariant 0 <= i <= |image.data|
        {
          buffer[8 + i] := image.data[i];
          i := i + 1;
        }
        if (0 <= buffer.Length < 4294967296) {
          FileInput.Reader.putContent(buffer, buffer.Length as uint32);
        } else {
          print "Error: buffer too big";
        }
      }
    }
  }
}
