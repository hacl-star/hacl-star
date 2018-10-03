module Spec.SHA1

module H = Spec.Hash.Helpers
module U32 = FStar.UInt32
module Seq = FStar.Seq
module E = FStar.Kremlin.Endianness

(* Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf *)

(* Section 5.3.1 *)

inline_for_extraction
let init_as_list = [
  0x67452301ul;
  0xefcdab89ul;
  0x98badcfeul;
  0x10325476ul;
  0xc3d2e1f0ul;
]

let h0 : hash_w SHA1 = Seq.seq_of_list init_as_list

let init = h0

(* Section 2.2.2: rotate left *)

inline_for_extraction
let rotl (n_:U32.t{0 < U32.v n_ /\ U32.v n_ < 32}) (x:U32.t): Tot U32.t =
  U32.((x <<^ n_) |^ (x >>^ (32ul -^ n_)))

(* Section 6.1.2 Step 1: message schedule *)

let rec w (mi: Seq.lseq (word SHA1) size_block_w) (t: U32.t {U32.v t <= 79}) : Tot (word SHA1) (decreases (U32.v t)) =
  if U32.lt t 16ul
  then Seq.index mi (U32.v t)
  else rotl 1ul (w mi (t `U32.sub` 3ul) `U32.logxor` w mi (t `U32.sub` 8ul) `U32.logxor` w mi (t `U32.sub` 14ul) `U32.logxor` w mi (t `U32.sub` 16ul))

(* Section 4.1.1: logical functions *)

inline_for_extraction
let f (t: U32.t {U32.v t <= 79}) (x y z: word SHA1) : Tot (word SHA1) =
  if U32.lt t 20ul
  then
    (x `U32.logand` y) `U32.logxor` (U32.lognot x `U32.logand` z)
  else if U32.lt 39ul t && U32.lt t 60ul
  then
    (x `U32.logand` y) `U32.logxor` (x `U32.logand` z) `U32.logxor` (y `U32.logand` z)
  else
    x `U32.logxor` y `U32.logxor` z

(* Section 4.2.1 *)

inline_for_extraction
let k (t: U32.t { U32.v t <= 79 } ) : Tot (word SHA1) =
  if U32.lt t 20ul
  then 0x5a827999ul
  else if U32.lt t 40ul
  then 0x6ed9eba1ul
  else if U32.lt t  60ul
  then 0x8f1bbcdcul
  else 0xca62c1d6ul

(* Section 6.1.2 Step 3 *)

let word_block = Seq.lseq (word SHA1) size_block_w

let step3_body'
  (mi: word_block)
  (st: hash_w SHA1)
  (t: U32.t {U32.v t < 80})
: Tot (hash_w SHA1)
= let sta = Seq.index st 0 in
  let stb = Seq.index st 1 in
  let stc = Seq.index st 2 in
  let std = Seq.index st 3 in
  let ste = Seq.index st 4 in
  let _T = rotl 5ul sta `U32.add_mod` f t stb stc std `U32.add_mod` ste `U32.add_mod` k t `U32.add_mod` w mi t in
  let e = std in
  let d = stc in
  let c = rotl 30ul stb in
  let b = sta in
  let a = _T in
  Seq.seq_of_list [
    a;
    b;
    c;
    d;
    e;
  ]

let step3_body
  (mi: word_block)
  (st: hash_w SHA1)
  (t: nat {t < 80})
: Tot (hash_w SHA1)
= step3_body' mi st (U32.uint_to_t t)

let step3
  (mi: word_block)
  (h: hash_w SHA1)
: Tot (hash_w SHA1)
= Spec.Compat.Loops.repeat_range 0 80 (step3_body mi) h

(* Section 6.1.2 Step 4 *)

let step4
  (mi: word_block)
  (h: hash_w SHA1)
: Tot (hash_w SHA1) =
  let st = step3 mi h in
  let sta = Seq.index st 0 in
  let stb = Seq.index st 1 in
  let stc = Seq.index st 2 in
  let std = Seq.index st 3 in
  let ste = Seq.index st 4 in
  Seq.seq_of_list [
    sta `U32.add_mod` Seq.index h 0;
    stb `U32.add_mod` Seq.index h 1;
    stc `U32.add_mod` Seq.index h 2;
    std `U32.add_mod` Seq.index h 3;
    ste `U32.add_mod` Seq.index h 4;
  ]

(* Section 3.1 al. 2: words and bytes, big-endian *)

let words_of_bytes_block
  (l: bytes { Seq.length l == size_block SHA1 } )
: Tot word_block
= E.seq_uint32_of_be size_block_w l

(* Section 6.1.2: outer loop body *)

let update h l =
  let mi = words_of_bytes_block l in
  step4 mi h

(* Section 5.1.1: padding *)

let pad = Spec.Hash.Common.pad SHA1

(* Section 6.1.2: no truncation needed *)

let finish = Spec.Hash.Common.finish _
