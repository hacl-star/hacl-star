# ABOUT #

This is an optimized library for [ChaCha](http://cr.yp.to/chacha.html), a stream cipher with a 256 bit key and a 64 bit nonce.

HChaCha is also implemented, which is used to build XChaCha, a variant which extends the nonce from 64 bits to 192 bits. See [Extending the Salsa20 nonce](http://cr.yp.to/snuffle/xsalsa-20110204.pdf).

The most optimized version for the underlying CPU, *that passes internal tests*, is selected at runtime. 

All assembler is PIC safe.

If you encrypt anything without using a MAC (HMAC, Poly1305, etc), you will be found, and made fun of.

# INITIALIZING #

The library can be initialized, i.e. the most optimized implementation that passes internal tests will be automatically selected, in two ways, **neither of which are thread safe**:

1. `int chacha_startup(void);` explicitly initializes the library, and returns a non-zero value if no suitable implementation is found that passes internal tests

2. Do nothing and use the library like normal. It will auto-initialize itself when needed, and hard exit if no suitibale implementation is found.

# CALLING #

Common assumptions:

* `chacha_key`, `chacha_iv`, and `chacha_iv24` variables can be accessed through their `b` member, which is an array of unsigned bytes.

* `rounds` is an even number 2 or greater.

* If `in` is `NULL`, the output will be stored to `out` (useful for things like random number generation or generating intermediate keys).

## ONE SHOT ##

`in` and `out` are assumed to be word aligned. Incremental support has no alignment requirements, but will obviously slow down if non word-aligned pointers are passed.

`void chacha(const chacha_key *key, const chacha_iv *iv, const uint8_t *in, uint8_t *out, size_t inlen, size_t rounds);`

`void xchacha(const chacha_key *key, const chacha_iv24 *iv, const uint8_t *in, uint8_t *out, size_t inlen, size_t rounds);`

Encrypts `inlen` bytes from `in` to `out, using `key`, `iv`, and `rounds`.

## INCREMENTAL ##

Incremental `in` and `out` buffers are *not* required to be word aligned. Unaligned buffers will require copying to aligned buffers however, which will obviously incur a speed penalty.

`void chacha_init(chacha_state *S, const chacha_key *key, const chacha_iv *iv, size_t rounds);`

`void xchacha_init(chacha_state *S, const chacha_key *key, const chacha_iv24 *iv, size_t rounds);`

Initialize the chacha_state with `key` and `iv`, and `rounds`, and sets the internal block counter to 0.

`size_t chacha_update(chacha_state *S, const uint8_t *in, uint8_t *out, size_t inlen);`

`size_t xchacha_update(chacha_state *S, const uint8_t *in, uint8_t *out, size_t inlen);`

Generates/xors up to `inlen + 63` bytes depending on how many bytes are in the internal buffer, and returns the number of encrypted bytes written to `out`.

`size_t chacha_final(chacha_state *S, uint8_t *out);`

`size_t xchacha_final(chacha_state *S, uint8_t *out);`

Generates/crypts any leftover data in the state to `out`, returns the number of bytes written.

# HChaCha #

`void hchacha(const uint8_t key[32], const uint8_t iv[16], uint8_t out[32], size_t rounds);`

Computes HChaCha in to `out`, using `key`, `iv`, and `rounds`.

# Examples #

## ENCRYPTING WITH ONE CALL ##

    const size_t rounds = 20;
    chacha_key key = {{..}};
    chacha_iv iv = {{..}};
    uint8_t in[100] = {..}, out[100];
    
    chacha(&key, &iv, in, out, 100, rounds);

## ENCRYPTING INCREMENTALLY ##

Encrypting incrementally, i.e. with multiple calls to collect/write data. Note that passing in data to be encrypted will not always result in data being written out. The implementation collects data until there is at least 1 block (64 bytes) of data available.

    const size_t rounds = 20;
    chacha_state S;
    chacha_key key = {{..}};
    chacha_iv iv = {{..}};
    uint8_t in[100] = {..}, out[100], *out_pointer = out;
    size_t i, bytes_written;
    
    chacha_init(&S, &key, &iv, rounds);

    /* add one byte at a time, extremely inefficient */
    for (i = 0; i < 100; i++) {
        bytes_written = chacha_update(&S, in + i, out_pointer, 1);
        out_pointer += bytes_written;
    }
    bytes_written = chacha_final(&S, out_pointer);

# VERSIONS #

x86-64, SSE2-32, and SSE3-32 versions are minorly modified from DJB's public domain implementations.

## Reference ##

* Generic: [chacha\_ref](app/extensions/chacha/chacha_ref.inc)

## x86 (32 bit) ##

* 386 compatible: [chacha\_x86](app/extensions/chacha/chacha_x86-32.inc)
* SSE2: [chacha\_sse2](app/extensions/chacha/chacha_sse2-32.inc)
* SSSE3: [chacha\_ssse3](app/extensions/chacha/chacha_ssse3-32.inc)
* AVX: [chacha\_avx](app/extensions/chacha/chacha_avx-32.inc)
* XOP: [chacha\_xop](app/extensions/chacha/chacha_xop-32.inc)
* AVX2: [chacha\_avx2](app/extensions/chacha/chacha_avx2-32.inc)

## x86-64 ##

* x86-64 compatible: [chacha\_x86](app/extensions/chacha/chacha_x86-64.inc)
* SSE2: [chacha\_sse2](app/extensions/chacha/chacha_sse2-64.inc)
* SSSE3: [chacha\_ssse3](app/extensions/chacha/chacha_ssse3-64.inc)
* AVX: [chacha\_avx](app/extensions/chacha/chacha_avx-64.inc)
* XOP: [chacha\_xop](app/extensions/chacha/chacha_xop-64.inc)
* AVX2: [chacha\_avx2](app/extensions/chacha/chacha_avx2-64.inc)

x86-64 will almost always be slower than SSE2, but on some older AMDs it may be faster

## ARM ##

* ARMv6 [chacha\_armv6](app/extensions/chacha/chacha_armv6-32.inc)
* NEON [chacha\_neon](app/extensions/chacha/chacha_neon-32.inc)

# BUILDING #

See [asm-opt#configuring](https://github.com/floodyberry/asm-opt#configuring) for full configure options.

If you would like to use Yasm with a gcc-compatible compiler, pass `--yasm` to configure.

The Visual Studio projects are generated assuming Yasm is available. You will need to have [Yasm.exe](http://yasm.tortall.net/Download.html) somewhere in your path to build them.

## STATIC LIBRARY ##

    ./configure
    make lib

and `make install-lib` OR copy `bin/chacha.lib` and `app/include/chacha.h` to your desired location.

## SHARED LIBRARY ##

    ./configure --pic
    make shared
    make install-shared

## UTILITIES / TESTING ##

    ./configure
    make util
    bin/chacha-util [bench|fuzz]

### BENCHMARK / TESTING ###

Benchmarking will implicitly test every available version. If any fail, it will exit with an error indicating which versions did not pass. Features tested include:

* Partial block generation
* Single block generation
* Multi block generation
* Counter handling when the 32-bit low half overflows to the upper half
* Streaming and XOR modes
* Incremental encryption
* Input/Output alignment

### FUZZING ###

Fuzzing tests every available implementation for the current CPU against the reference implementation. Features tested are:

* HChaCha output
* One-shot ChaCha
* Incremental ChaCha with potentially unaligned output 

# BENCHMARKS #

As I have not updated any benchmarks yet, raw cycle counts should have ~10-20 cycles added from the overhead of targets not being hardcoded.

## [E5200](http://ark.intel.com/products/37212/) ##

### ChaCha ###

<table>
<thead><tr><th>Impl.</th><th>1 byte</th><th>8</th><th>12</th><th>20</th><th>576 bytes</th><th>8</th><th>12</th><th>20</th><th>8192 bytes</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>SSSE3-64  </td> <td></td><td> 237</td><td> 300</td><td> 437</td> <td></td><td>  1.71</td><td>  2.23</td><td>  3.30</td> <td></td><td>  1.46</td><td>  1.90</td><td>  2.82</td> </tr>
<tr> <td>SSE2-64   </td> <td></td><td> 262</td><td> 337</td><td> 500</td> <td></td><td>  1.98</td><td>  2.65</td><td>  3.97</td> <td></td><td>  1.68</td><td>  2.29</td><td>  3.42</td> </tr>
<tr> <td>SSSE3-32  </td> <td></td><td> 287</td><td> 350</td><td> 487</td> <td></td><td>  2.04</td><td>  2.69</td><td>  3.99</td> <td></td><td>  1.72</td><td>  2.37</td><td>  3.59</td> </tr>
<tr> <td>SSE2-32   </td> <td></td><td> 312</td><td> 400</td><td> 562</td> <td></td><td>  2.43</td><td>  3.26</td><td>  4.95</td> <td></td><td>  2.12</td><td>  2.90</td><td>  4.52</td> </tr>
</tbody>
</table>

### HChaCha ###

<table>
<thead><tr><th>Impl.</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>SSSE3-64  </td> <td> 162</td><td> 237</td><td> 362</td> </tr>
<tr> <td>SSSE3-32  </td> <td> 175</td><td> 250</td><td> 375</td> </tr>
<tr> <td>SSE2-64   </td> <td> 200</td><td> 275</td><td> 450</td> </tr>
<tr> <td>SSE2-32   </td> <td> 200</td><td> 275</td><td> 450</td> </tr>
</tbody>
</table>

## [E3-1270](http://ark.intel.com/products/52276/) ##

### ChaCha ###

<table>
<thead><tr><th>Impl.</th><th>1 byte</th><th>8</th><th>12</th><th>20</th><th>576 bytes</th><th>8</th><th>12</th><th>20</th><th>8192 bytes</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>AVX-64    </td> <td></td><td> 176</td><td> 240</td><td> 364</td> <td></td><td>  1.22</td><td>  1.68</td><td>  2.64</td> <td></td><td>  1.04</td><td>  1.46</td><td>  2.29</td> </tr>
<tr> <td>SSSE3-64  </td> <td></td><td> 180</td><td> 248</td><td> 384</td> <td></td><td>  1.35</td><td>  1.88</td><td>  2.94</td> <td></td><td>  1.18</td><td>  1.65</td><td>  2.59</td> </tr>
<tr> <td>AVX-32    </td> <td></td><td> 184</td><td> 248</td><td> 380</td> <td></td><td>  1.50</td><td>  2.03</td><td>  3.10</td> <td></td><td>  1.24</td><td>  1.72</td><td>  2.68</td> </tr>
<tr> <td>SSSE3-32  </td> <td></td><td> 228</td><td> 292</td><td> 428</td> <td></td><td>  1.84</td><td>  2.47</td><td>  3.74</td> <td></td><td>  1.65</td><td>  2.23</td><td>  3.41</td> </tr>
</tbody>
</table>

### HChaCha ###

<table>
<thead><tr><th>Impl.</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>AVX-64    </td> <td> 116</td><td> 180</td><td> 308</td> </tr>
<tr> <td>AVX-32    </td> <td> 128</td><td> 192</td><td> 320</td> </tr>
<tr> <td>SSSE3-64  </td> <td> 128</td><td> 192</td><td> 328</td> </tr>
<tr> <td>SSSE3-32  </td> <td> 136</td><td> 204</td><td> 336</td> </tr>
</tbody>
</table>

## [i7-4770K](http://ark.intel.com/products/75123) ##

Timings are with Turbo Boost and Hyperthreading, so their accuracy is not concrete. 
For reference, OpenSSL and Crypto++ give ~0.8cpb for AES-128-CTR and ~1.1cpb for AES-256-CTR, 
and ~7.4cpb for SHA-512.

### ChaCha ###

<table>
<thead><tr><th>Impl.</th><th>1 byte</th><th>8</th><th>12</th><th>20</th><th>576 bytes</th><th>8</th><th>12</th><th>20</th><th>8192 bytes</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>AVX2-64   </td> <td></td><td> 146</td><td> 194</td><td> 313</td> <td></td><td>  0.68</td><td>  0.97</td><td>  1.48</td> <td></td><td>  0.52</td><td>  0.71</td><td>  1.08</td> </tr>
<tr> <td>AVX2-32   </td> <td></td><td> 170</td><td> 218</td><td> 337</td> <td></td><td>  0.83</td><td>  1.11</td><td>  1.66</td> <td></td><td>  0.62</td><td>  0.83</td><td>  1.24</td> </tr>
<tr> <td>AVX-64    </td> <td></td><td> 146</td><td> 194</td><td> 316</td> <td></td><td>  1.06</td><td>  1.50</td><td>  2.33</td> <td></td><td>  0.94</td><td>  1.32</td><td>  2.05</td> </tr>
<tr> <td>AVX-32    </td> <td></td><td> 158</td><td> 206</td><td> 328</td> <td></td><td>  1.32</td><td>  1.82</td><td>  2.81</td> <td></td><td>  1.12</td><td>  1.57</td><td>  2.47</td> </tr>
</tbody>
</table>

### HChaCha ###

(these are all literally the same version, timing differences are noise)

<table>
<thead><tr><th>Impl.</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>AVX2-64   </td> <td>  81</td><td> 155</td><td> 251</td> </tr>
<tr> <td>AVX2-32   </td> <td>  87</td><td> 155</td><td> 254</td> </tr>
<tr> <td>AVX-64    </td> <td>  87</td><td> 155</td><td> 274</td> </tr>
<tr> <td>AVX-32    </td> <td>  87</td><td> 152</td><td> 251</td> </tr>
</tbody>
</table>

## AMD FX-8120 ##

Timings are with Turbo on, so accuracy is not concrete. I'm not sure how to adjust for it either, 
and depending on clock speed (3.1ghz vs 4.0ghz), OpenSSL gives between 0.73cpb - 0.94cpb for AES-128-CTR, 
1.03cpb - 1.33cpb for AES-256-CTR, and 10.96cpb - 14.1cpb for SHA-512.

### ChaCha ###

<table>
<thead><tr><th>Impl.</th><th>1 byte</th><th>8</th><th>12</th><th>20</th><th>576 bytes</th><th>8</th><th>12</th><th>20</th><th>8192 bytes</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>XOP-64    </td> <td></td><td> 194</td><td> 269</td><td> 418</td> <td></td><td>  1.09</td><td>  1.47</td><td>  2.25</td> <td></td><td>  0.93</td><td>  1.22</td><td>  1.80</td> </tr>
<tr> <td>AVX-64    </td> <td></td><td> 245</td><td> 344</td><td> 544</td> <td></td><td>  1.41</td><td>  1.97</td><td>  3.14</td> <td></td><td>  1.20</td><td>  1.63</td><td>  2.51</td> </tr>
<tr> <td>XOP-32    </td> <td></td><td> 247</td><td> 322</td><td> 471</td> <td></td><td>  1.44</td><td>  1.96</td><td>  3.01</td> <td></td><td>  1.26</td><td>  1.70</td><td>  2.59</td> </tr>
<tr> <td>AVX-32    </td> <td></td><td> 276</td><td> 375</td><td> 573</td> <td></td><td>  1.88</td><td>  2.53</td><td>  3.78</td> <td></td><td>  1.62</td><td>  2.16</td><td>  3.23</td> </tr>
</tbody>
</table>

### HChaCha ###

<table>
<thead><tr><th>Impl.</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>XOP-64    </td> <td>  84</td><td> 160</td><td> 309</td> </tr>
<tr> <td>XOP-32    </td> <td>  91</td><td> 165</td><td> 318</td> </tr>
<tr> <td>AVX-64    </td> <td> 144</td><td> 243</td><td> 441</td> </tr>
<tr> <td>AVX-32    </td> <td> 144</td><td> 237</td><td> 441</td> </tr>
</tbody>
</table>


## ZedBoard (Cortex-A9) ##

I don't have access to the cycle counter yet, so cycles are computed by taking the microseconds times the clock speed (666mhz) divided by 1 million. For comparison, on long messages, OpenSSL 1.0.0e gives 52.3 cpb for aes-128-cbc (woof), and djb's armneon6 Salsa20/20 implementation gives 8.2 cpb.

### ChaCha ###

<table>
<thead><tr><th>Impl.</th><th>1 byte</th><th>8</th><th>12</th><th>20</th><th>576 bytes</th><th>8</th><th>12</th><th>20</th><th>8192 bytes</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>NEON-32    </td> <td></td><td> 460</td><td> 573</td><td> 814</td> <td></td><td>  3.53</td><td>  4.73</td><td>  7.13</td> <td></td><td>  3.06</td><td>  4.26</td><td>  6.47</td> </tr>
<tr> <td>ARMv6-32   </td> <td></td><td> 437</td><td> 565</td><td> 793</td> <td></td><td>  5.33</td><td>  7.07</td><td> 10.87</td> <td></td><td>  5.07</td><td>  6.93</td><td> 10.73</td> </tr>
</tbody>
</table>

### HChaCha ###

NEON shares the same implementation as ARMv6 as NEON latencies are too high for a single block.

<table>
<thead><tr><th>Impl.</th><th>8</th><th>12</th><th>20</th></tr></thead>
<tbody>
<tr> <td>NEON-32   </td> <td> 294</td><td> 446</td><td> 658</td> </tr>
<tr> <td>ARMv6-32  </td> <td> 294</td><td> 446</td><td> 658</td> </tr>
</tbody>
</table>

# LICENSE #

Public Domain, or MIT
