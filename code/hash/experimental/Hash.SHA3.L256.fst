module Hash.SHA3.L256

open FStar.Buffer
open FStar.UInt32
open FStar.UInt8


val set_rho: mem:bytes -> STL unit
                             (requires (fun h -> live h mem))
                             (ensures  (fun h0 _ h1 -> live h1 mem /\ modifies_1 mem h0 h1))
let set_rho mem =
  upd mem 0ul 1uy;
  upd mem 1ul 3uy;
  upd mem 2ul 6uy;
  upd mem 3ul 10uy;
  upd mem 4ul 15uy;
  upd mem 5ul 21uy;
  upd mem 6ul 28uy;
  upd mem 7ul 36uy;
  upd mem 8ul 45uy;
  upd mem 9ul 55uy;
  upd mem 10ul 2uy;
  upd mem 11ul 14uy;
  upd mem 12ul 27uy;
  upd mem 13ul 41uy;
  upd mem 14ul 56uy;
  upd mem 15ul 8uy;
  upd mem 16ul 25uy;
  upd mem 17ul 43uy;
  upd mem 18ul 62uy;
  upd mem 19ul 18uy;
  upd mem 20ul 39uy;
  upd mem 21ul 61uy;
  upd mem 22ul 20uy;
  upd mem 23ul 44uy
                    
val set_pi: mem:bytes -> STL unit
                             (requires (fun h -> live h mem))
                             (ensures  (fun h0 _ h1 -> live h1 mem /\ modifies_1 mem h0 h1))
let set_pi mem =
  upd mem 0ul 10uy;
  upd mem 1ul 7uy;
  upd mem 2ul 11uy;
  upd mem 3ul 17uy;
  upd mem 4ul 18uy;
  upd mem 5ul 3uy;
  upd mem 6ul 5uy;
  upd mem 7ul 16uy;
  upd mem 8ul 8uy;
  upd mem 9ul 21uy;
  upd mem 10ul 24uy;
  upd mem 11ul 4uy;
  upd mem 12ul 15uy;
  upd mem 13ul 23uy;
  upd mem 14ul 19uy;
  upd mem 15ul 13uy;
  upd mem 16ul 12uy;
  upd mem 17ul 2uy;
  upd mem 18ul 20uy;
  upd mem 19ul 14uy;
  upd mem 20ul 22uy;
  upd mem 21ul 9uy;
  upd mem 22ul 6uy;
  upd mem 23ul 1uy

val set_rc: mem:uint64s -> STL unit
                             (requires (fun h -> live h mem))
                             (ensures  (fun h0 _ h1 -> live h1 mem /\ modifies_1 mem h0 h1))
let set_rc mem =
  upd mem 0ul 1ULL; 
  upd mem 1ul 0x8082ULL;
  upd mem 2ul 0x800000000000808aULL; 
  upd mem 3ul 0x8000000080008000ULL;
  upd mem 4ul 0x808bULL; 
  upd mem 5ul 0x80000001ULL;
  upd mem 6ul 0x8000000080008081ULL;
  upd mem 7ul 0x8000000000008009ULL;
  upd mem 8ul 0x8aULL;
  upd mem 9ul 0x88ULL;
  upd mem 10ul 0x80008009ULL;
  upd mem 11ul 0x8000000aULL;
  upd mem 12ul 0x8000808bULL;
  upd mem 13ul 0x800000000000008bULL;
  upd mem 14ul 0x8000000000008089ULL;
  upd mem 15ul 0x8000000000008003ULL;
  upd mem 16ul 0x8000000000008002ULL;
  upd mem 17ul 0x8000000000000080ULL;
  upd mem 18ul 0x800aULL;
  upd mem 19ul 0x800000008000000aULL;
  upd mem 20ul 0x8000000080008081ULL;
  upd mem 21ul 0x8000000000008080ULL;
  upd mem 22ul 0x80000001ULL;
  upd mem 23ul 0x8000000080008008ULL


val _rol: s32 -> u32 -> Tot s32
let _rol x s = (x @<< s) @| (x @>> (64ul @- s))


(* Define the Keccak-f[1600] permutation function *)
val keccakf: state:uint64s -> STL unit
                                 (requires (fun h -> live h state))
                                 (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let keccakf state =
  let a = state in
  let b = create 5ul 0ULL in
  let t = 0ULL in
  let x = 0uy in
  let y = 0uy in
  let i = 0uy in

  if i < 24ul then
      // Theta
      FOR5(x, 1,
           b[x] = 0;
           FOR5(y, 5, b[x] ^= a[x + y]; ))
      FOR5(x, 1,
           FOR5(y, 5, a[y + x] ^= b[(x + 4) % 5] ^ rol(b[(x + 1) % 5], 1); ))
           
      // Rho and pi
      let t = index a 1ul in
      x = 0;
      REPEAT24(b[0] = a[pi[x]];
               a[pi[x]] = rol t (index rho x);
               t = index b 0ul;
               x++; )
      // Chi
      FOR5(y,
         5,
         FOR5(x, 1,
              b[x] = a[y + x];)
         FOR5(x, 1,
              a[y + x] = b[x] ^ ((~b[(x + 1) % 5]) & b[(x + 2) % 5]); ))
      // Iota
      a[0] ^= RC[i];
      i++;
   else ()

/******** The FIPS202-defined functions. ********/

/*** Some helper macros. ***/

#define _(S) do { S } while (0)
#define FOR(i, ST, L, S) \
  _(for (size_t i = 0; i < L; i += ST) { S; })
#define mkapply_ds(NAME, S)                                          \
  static inline void NAME(uint8_t* dst,                              \
                          const uint8_t* src,                        \
                          size_t len) {                              \
    FOR(i, 1, len, S);                                               \
  }
#define mkapply_sd(NAME, S)                                          \
  static inline void NAME(const uint8_t* src,                        \
                          uint8_t* dst,                              \
                          size_t len) {                              \
    FOR(i, 1, len, S);                                               \
  }

mkapply_ds(xorin, dst[i] ^= src[i])  // xorin
mkapply_sd(setout, dst[i] = src[i])  // setout

#define P keccakf
#define Plen 200

// Fold P*F over the full blocks of an input.
#define foldP(I, L, F) \
  while (L >= rate) {  \
    F(a, I, rate);     \
    P(a);              \
    I += rate;         \
    L -= rate;         \
  }

/** The sponge-based hash construction. **/
static inline int hash(uint8_t* out, size_t outlen,
                       const uint8_t* in, size_t inlen,
                       size_t rate, uint8_t delim) {
  if ((out == NULL) || ((in == NULL) && inlen != 0) || (rate >= Plen)) {
    return -1;
  }
  uint8_t a[Plen] = {0};
  // Absorb input.
  foldP(in, inlen, xorin);
  // Xor in the DS and pad frame.
  a[inlen] ^= delim;
  a[rate - 1] ^= 0x80;
  // Xor in the last block.
  xorin(a, in, inlen);
  // Apply P
  P(a);
  // Squeeze output.
  foldP(out, outlen, setout);
  setout(a, out, outlen);
  memset_s(a, 200, 0, 200);
  return 0;
}

/*** Helper macros to define SHA3 and SHAKE instances. ***/
#define defshake(bits)                                            \
  int shake##bits(uint8_t* out, size_t outlen,                    \
                  const uint8_t* in, size_t inlen) {              \
    return hash(out, outlen, in, inlen, 200 - (bits / 4), 0x1f);  \
  }
#define defsha3(bits)                                             \
  int sha3_##bits(uint8_t* out, size_t outlen,                    \
                  const uint8_t* in, size_t inlen) {              \
    if (outlen > (bits/8)) {                                      \
      return -1;                                                  \
    }                                                             \
    return hash(out, outlen, in, inlen, 200 - (bits / 4), 0x06);  \
  }

/*** FIPS202 SHAKE VOFs ***/
defshake(128)
defshake(256)

/*** FIPS202 SHA3 FOFs ***/
defsha3(224)
defsha3(256)
defsha3(384)
defsha3(512)
