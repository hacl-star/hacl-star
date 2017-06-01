This code implements Daniel J. Bernstein's ChaCha stream cipher in C,
targeting architectures with AVX2 and future AVX512 vector extensions.

The implementation improves the slightly modified implementations of Ted Krovetz in the Chromium Project
(http://src.chromium.org/viewvc/chrome/trunk/deps/third_party/nss/nss/lib/freebl/chacha20/chacha20_vec.c and
http://src.chromium.org/viewvc/chrome/trunk/deps/third_party/openssl/openssl/crypto/chacha/chacha_vec.c)
by using the Advanced Vector Extensions AVX2 and, if available in future, AVX512 to widen the vectorization
to 256-bit, respectively 512-bit.

On Intel's Haswell architecture this implementation (using AVX2) is almost ~2x faster than the fastest 
implementation here, when encrypting (decrypting) 2 blocks and more. Also, this implementation is expected 
to double the speed again, when encrypting (decrypting) 4 blocks and more, running on a future architecture
with support for AVX512.

Further details and our measurement results are provided in:
Goll, M., and Gueron,S.: Vectorization of ChaCha Stream Cipher. Cryptology ePrint Archive, 
Report 2013/759, November, 2013, http://eprint.iacr.org/2013/759.pdf

Developers and authors:
*********************************************************
Martin Goll (1) and Shay Gueron (2, 3), 
(1) Ruhr-University Bochum, Germany
(2) University of Haifa, Israel
(3) Intel Corporation, Israel Development Center, Haifa, Israel
*********************************************************

Intellectual Property Notices
-----------------------------

There are no known present or future claims by a copyright holder that the
distribution of this software infringes the copyright. In particular, the author
of the software is not making such claims and does not intend to make such
claims.

There are no known present or future claims by a patent holder that the use of
this software infringes the patent. In particular, the author of the software is
not making such claims and does not intend to make such claims.

Our implementation is in public domain.