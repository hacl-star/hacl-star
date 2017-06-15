This is a rewrite by R. Dolbeau of the reference code 'ref' by D. J. Bernstein
for chacha20 into C+intrinsics, complete with vector optimizations. Many of
those are based on my implementations of salsa20, itself based on D. J. Bernstein
vector code. The use of intrinsics allows compilation to both SSE (2-operands) and
AVX-128 (3-operands) assembly code by ICC (tested with version  14.0.3.174)
for 128 bits intrinsics. Please note that GCC 4.7.2 doesn't produce very good
code with this if you don't use AVX2 (and not that great with AVX2 either).

The code also includes AVX2 using the whole 256 bits (Haswell & later), and
AVX-512 (upcoming Knights Landing & upcoming Xeons).

= Rational =

There already is several optimized implementations of chacha20 in
supercop, but many of them are in some form of assembly. So I wrote this
in C+intrinsics for the same reasons I wrote the salsa20 implementation
(see the README.txt there).

= Features =

The code uses a completely standard storage format, as the chacha20 algorithm
is more SIMD-friendly than salsa20 (by the will of the designer, if I
understand correctly). The code contains four main computational blocks:

1) u1.h : does a single block at a time, using 128 bits SIMD operations.
Rewrite from D.J. Bernstein amd64-xmm2 code.

2) u4.h : does 4 blocks at a time, using 128 bits SIMD operations. Each
lane computes a different block (256 bytes at a time). Completely by-the-book
"unroll by four blocks, vectorize" implementation, derived from u8.h below.
All the tricks in here are standard and also used in other implementations
(i.e. replacing byte rotations by shuffles, ...).

3) u8.h : does 8 blocks at a time, using 256 bits SIMD operations. Each lane
computes a different block (512 bytes at a time). This requires AVX2 support
in both the compiler and the hardware. By-the-book "unroll-by-8 blocks,
vectorize".

4) u16.h : does 16 blocks at a time, using 512 bits SIMD operations. Each
lane computes a different block (1024 bytes at a time). There is significantly
less instructions, as AVX-512 supports 'rotate left', replacing 2 shift and one
xor by a single rotate. This requires AVX-512 support in both the compiler and
the hardware. The xor'ing and storing at the end are using scatter-gather on 512
bits vector. This is simply the natural extension in AVX-512 of the code in u8.h.
As of the writing of this (2014/07/16), there is no publicly available hardware
supporting AVX-512, one needs to use the Intel SDE to test the validity of the
code:
<https://software.intel.com/en-us/articles/intel-software-development-emulator>.

= Performance =

At least one pure assembly version is faster from 1536 and 4096 bytes messages,
but by a small margin when you use ICC (specifically, moon/avx2/64). This
code should be much faster on AVX-512. It was also probably easier to write :-)

Not all compilers defined in 'okcompilers/c' were tested. The subset tested
(shown below) was checked to produce speed comparable to that reported on
the 'supercop' website for similar CPUs. Also, the machine options chosen for
ICC in 'supercop' (-xP, ...) are obsolete and might not cover all cases.

Compiler tested (i.e., the 'okcompilers/c' file):

gcc -m64 -march=native -mtune=native -O3 -fomit-frame-pointer
gcc -m64 -march=core-avx2 -mtune=core-avx2 -O3 -fomit-frame-pointer
gcc -m64 -march=core-avx-i -mtune=core-avx-i -O3 -fomit-frame-pointer
gcc -m64 -march=corei7-avx -mtune=corei7-avx -O3 -fomit-frame-pointer
gcc -m64 -march=corei7 -mtune=corei7 -O3 -fomit-frame-pointer
icc -m64 -march=native -mtune=native -O3 -fomit-frame-pointer
icc -m64 -march=core-avx2 -mtune=core-avx2 -O3 -fomit-frame-pointer
icc -m64 -march=core-avx-i -mtune=core-avx-i -O3 -fomit-frame-pointer
icc -m64 -march=corei7-avx -mtune=corei7-avx -O3 -fomit-frame-pointer
icc -m64 -march=corei7 -mtune=corei7 -O3 -fomit-frame-pointer

The faster is almost always ICC in 'native' mode. The 'corei7' arch
does not include AVX or AVX2, 'corei7-avx' and 'core-avx-i' do not
include AVX2.

To compile the code for AVX-512, the current option of choice is '-xMIC-AVX512'
with ICC. But you need to do that by hand, as supercop will notice the
compiler produces non-executable binary and will not add it to 'c-compatible'.

-- 
Romain Dolbeau
$Date: 2014/09/07 16:10:57 $
