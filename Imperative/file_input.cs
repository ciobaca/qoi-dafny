using System;
using System.Collections;
using System.Text;
using System.IO;

namespace @FileInput {
    public partial class @Reader
    {
        public static bool shouldEncode()
        {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {
                return !argList[1].EndsWith("qoi");
              } else {
                return false;
              }
            }

            return false;
        }

        public static byte[] getContent() {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {

                return System.IO.File.ReadAllBytes(argList[1]);
              } else {
                return new byte [0];
              }
            }

            return new byte [0];
        }

        public static void putContent(byte[] contents, uint size) {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {
                String suffix;
                if (shouldEncode()) {
                   suffix = ".qoi";
                } else {
                  suffix = ".rgb";
                }
                byte [] towrite = new byte [size];
                Array.Copy(contents, 0, towrite, 0, size);
                System.IO.File.WriteAllBytes(argList[1] + suffix, towrite);
              } else {
                return;
              }
            }

            return;
        }

        public static long getTimestamp() {
          return DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
        }
    }
}
