zfecSharp
=======

This is a port of zfec https://pypi.python.org/pypi/zfec , a fast erasure codec
for Python.

c#/.net 版本转换自： https://github.com/richardkiss/js_zfec 。



概述
========

前向纠错也叫前向纠错码(Forward Error Correction，简称FEC)，是增加数据通讯可信度的方法。
在单向通讯信道中，一旦错误被发现，其接收器将无权再请求传输。
FEC 是利用数据进行传输冗余信息的方法，当传输中出现错误，将允许接收器再建数据。

通过将一段数据，切分若干个块（block），根据参数K，和 N（K>N),通过原始block，生成K个冗余数据。
只要接受端，收到任意N个数据，即可还原出原始数据。

常用于增加影音的传输。

示例
========

            var bytesx = new byte[20];
            for (int i = 0; i < 10; i++)
            {
                bytesx[i] = (byte)(i + 1);
            }
            for (int i = 0; i < 10; i++)
            {
                bytesx[10 + i] = (byte)(i + 11);
            }
            var code = new fec(2, 3).encode(bytesx);
            code.RemoveAt(0);
            var bytes = new fec(2, 3).decode(code.ToArray());
