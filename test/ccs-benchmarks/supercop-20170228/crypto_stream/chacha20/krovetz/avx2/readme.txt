Chacha implementation by Ted Krovetz (ted@krovetz.net)            2013.06.19

This code implements Dan Bernstein's Chacha stream cipher in C, targeting 
Intel AVX2 machines. I wrote it after studying the resources at
http://cr.yp.to/chacha.html and the paper "NEON crypto" at
http://cr.yp.to/highspeed/neoncrypto-20120320.pdf.

Since most of Bernstein's implementations are either fast assembly or slow C, I
decided to try to write a fast C version. I firmly believe that fast C is
possible and much more practical than assembly.

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
