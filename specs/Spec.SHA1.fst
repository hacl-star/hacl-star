module Spec.SHA1

module H = Spec.Hash.Definitions
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

let h0 : words_state SHA1 = Seq.seq_of_list init_as_list

let init = h0

(* Section 2.2.2: rotate left *)

inline_for_extraction
let rotl (n_:U32.t{0 < U32.v n_ /\ U32.v n_ < 32}) (x:U32.t): Tot U32.t =
  U32.((x <<^ n_) |^ (x >>^ (32ul -^ n_)))

(* Section 6.1.2 Step 1: message schedule *)

let rec w' (mi: Seq.lseq (word SHA1) block_word_length) (t: nat {t <= 79}) : GTot (word SHA1) (decreases (t)) =
  if t < 16
  then Seq.index mi (t)
  else rotl 1ul (w' mi (t - 3) `U32.logxor` w' mi (t - 8) `U32.logxor` w' mi (t - 14) `U32.logxor` w' mi (t - 16))

let w (mi: Seq.lseq (word SHA1) block_word_length) (t: U32.t {U32.v t <= 79}) : GTot (word SHA1) = w' mi (U32.v t)

let compute_w_post
  (mi: Seq.lseq (word SHA1) block_word_length)
  (n: nat)
  (res: Seq.lseq (word SHA1) n)
: GTot Type0
= (n <= 80 /\ (
    forall (i: nat) . i < n ==> Seq.index res i == w' mi i
  ))

let compute_w_post_intro
  (mi: Seq.lseq (word SHA1) block_word_length)
  (n: nat)
  (res: Seq.lseq (word SHA1) n)
  (u: squash (n <= 80))
  (f: (i: nat) -> Lemma
      (requires (i < n))
      (ensures (i < n /\ Seq.index res i == w' mi i)))
: Lemma
  (compute_w_post mi n res)
= Classical.forall_intro (Classical.move_requires f)

inline_for_extraction
noextract
let compute_w_n'
  (mi: Seq.lseq (word SHA1) block_word_length)
  (n: nat { n <= 79 } )
  (w: ((i: nat {i < n}) -> Tot (y: word SHA1 {y == w' mi i})))
: Tot (y: word SHA1 {y == w' mi n})
= let r =
      if n < 16
      then Seq.index mi n
      else rotl 1ul (w (n - 3) `U32.logxor` w (n - 8) `U32.logxor` w (n - 14) `U32.logxor` w (n - 16))
  in
  r

inline_for_extraction
noextract
let compute_w_n
  (mi: Seq.lseq (word SHA1) block_word_length)
  (n: nat { n <= 79 } )
  (accu: Seq.lseq (word SHA1) n)
: Pure (word SHA1)
  (requires (compute_w_post mi n accu))
  (ensures (fun y -> n <= 79 /\ y == w' mi n))
= [@inline_let]
  let w (i: nat {i < n}) : Tot (y: word SHA1 {y == w' mi i}) = Seq.index accu i in
  compute_w_n' mi n w

inline_for_extraction
noextract
let compute_w_next
  (mi: Seq.lseq (word SHA1) block_word_length)
  (n: nat { n <= 79 } )
  (accu: Seq.lseq (word SHA1) n)
: Pure (Seq.lseq (word SHA1) (n + 1))
  (requires (compute_w_post mi n accu))
  (ensures (fun accu' -> compute_w_post mi (n + 1) accu'))
= let wn = compute_w_n mi n accu in
  let accu' = Seq.snoc accu wn in
  assert (n + 1 <= 80);
  let g
    (i: nat)
  : Lemma
    (requires (i < n + 1))
    (ensures (i < n + 1 /\ Seq.index accu' i == w' mi i))
  = if i = n
    then ()
    else ()
  in
  compute_w_post_intro mi (n + 1) accu' () g;
  accu'

let rec compute_w
  (mi: Seq.lseq (word SHA1) block_word_length)
  (n: nat)
  (accu: Seq.lseq (word SHA1) n)
: Pure (Seq.lseq (word SHA1) 80)
  (requires (compute_w_post mi n accu))
  (ensures (fun res -> compute_w_post mi 80 res))
  (decreases (80 - n))
= assert (n <= 80); // this assert is necessary for Z3 to prove that n <= 79 in the else branch
  if n = 80
  then accu
  else compute_w mi (n + 1) (compute_w_next mi n accu)

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

let word_block = Seq.lseq (word SHA1) block_word_length

let step3_body'_aux
  (mi: word_block)
  (st: words_state SHA1)
  (t: U32.t {U32.v t < 80})
  (wt: word SHA1 { wt == w mi t } )
: Tot (words_state SHA1)
= let sta = Seq.index st 0 in
  let stb = Seq.index st 1 in
  let stc = Seq.index st 2 in
  let std = Seq.index st 3 in
  let ste = Seq.index st 4 in
  let _T = rotl 5ul sta `U32.add_mod` f t stb stc std `U32.add_mod` ste `U32.add_mod` k t `U32.add_mod` wt in
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

[@"opaque_to_smt"]
let step3_body' = step3_body'_aux

[@unifier_hint_injective]
inline_for_extraction
let step3_body_w_t
  (mi: word_block)
: Tot Type
= (t: nat { t < 80 }) -> Tot (wt: word SHA1 { wt == w' mi t } )

let step3_body
  (mi: word_block)
  (w: step3_body_w_t mi)
  (st: words_state SHA1)
  (t: nat {t < 80})
: Tot (words_state SHA1)
= step3_body' mi st (U32.uint_to_t t) (w t)

inline_for_extraction
let index_compute_w
  (mi: word_block)
  (cwt: Seq.lseq (word SHA1) 80 { compute_w_post mi 80 cwt } )
: Tot (step3_body_w_t mi)
= fun (t: nat {t < 80}) -> (Seq.index cwt t <: (wt: word SHA1 { wt == w' mi t }))

let step3_aux
  (mi: word_block)
  (h: words_state SHA1)
: Tot (words_state SHA1)
= let cwt = compute_w mi 0 Seq.empty in
  Spec.Loops.repeat_range 0 80 (step3_body mi (index_compute_w mi cwt)) h

[@"opaque_to_smt"]
let step3 = step3_aux

(* Section 6.1.2 Step 4 *)

let step4_aux
  (mi: word_block)
  (h: words_state SHA1)
: Tot (words_state SHA1) =
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

[@"opaque_to_smt"]
let step4 = step4_aux

(* Section 3.1 al. 2: words and bytes, big-endian *)

let words_of_bytes_block
  (l: bytes { Seq.length l == block_length SHA1 } )
: Tot word_block
= E.seq_uint32_of_be block_word_length l

(* Section 6.1.2: outer loop body *)

let update_aux h l =
  let mi = words_of_bytes_block l in
  step4 mi h

let update = update_aux

(* Section 5.1.1: padding *)

let pad = Spec.Hash.PadFinish.pad SHA1

(* Section 6.1.2: no truncation needed *)

let finish = Spec.Hash.PadFinish.finish _
