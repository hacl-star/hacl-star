Chacha implementation by Ted Krovetz (ted@krovetz.net)            2012.07.05

This code implements Dan Bernstein's Chacha stream cipher in C, targeting vector
machines (SSE, Altivec, NEON). I wrote it after studying the resources at
http://cr.yp.to/chacha.html and the paper "NEON crypto" at
http://cr.yp.to/highspeed/neoncrypto-20120320.pdf.

Since most of Bernstein's implementations are either fast assembly or slow C, I
decided to try to write a fast C version. I firmly believe that fast C is
possible and much more practical than assembly. As of 2012.07.05 this C version
is significantly faster on target machines than all submitted versions of Chacha
reported at the SUPERCOP website (http://bench.cr.yp.to/results-stream.html).

Chacha20 4KiB encryption speeds reported at SUPERCOP on 2012.07.05 in cpb.
                     Mine   Previous best
Intel Sandy Bridge   2.62   3.73
PPC 7447             3.33   13.02
ARM Cortex-A9        7.65   17.29

Chacha8 4KiB encryption speeds reported at SUPERCOP on 2012.07.05 in cpb.
                     Mine   Previous best
Intel Sandy Bridge   1.22   1.79
PPC 7447             1.62   6.29
ARM Cortex-A9        3.58   9.80

Intellectual Property Notices
-----------------------------

There are no known present or future claims by a copyright holder that the
distribution of this software infringes the copyright. In particular, the author
of the software is not making such claims and does not intend to make such
claims.

There are no known present or future claims by a patent holder that the use of
this software infringes the patent. In particular, the author of the software is
not making such claims and does not intend to make such claims.

My code is in the public domain.

--

Updates

2013.06.19: Transplanted some improvements from AVX2 version for short messages.
