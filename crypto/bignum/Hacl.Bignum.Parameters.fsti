module Hacl.Bignum.Parameters

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

(** The values of the prime for modular arithmetic **)
val prime: pos

(** Size of a word on the platform (32 or 64bits) **)
val word_size: ws:pos

(** Concrete platform word with side-channel protection **)
inline_for_extraction val limb: Type0
inline_for_extraction val wide: Type0
inline_for_extraction let ctr  = FStar.UInt32.t


(** Number of limbs of a bigint **)
val len: pos
inline_for_extraction val clen: l:FStar.UInt32.t{FStar.UInt32.v l = len}

type felem = b:buffer limb{length b = len}
type felem_wide = b:buffer wide{length b = len}


(** Associates a weight in bits to each limb of the bigint *)
val limb_size: s:pos{s < word_size}
inline_for_extraction val climb_size: l:FStar.UInt32.t{limb_size = FStar.UInt32.v l}

val lemma_prime_limb_size: unit -> Lemma (pow2 (len * limb_size) > prime)

(* Limb operators *)
inline_for_extraction let limb_n = word_size
inline_for_extraction val v: limb -> GTot (FStar.UInt.uint_t limb_n)

val lemma_limb_injectivity: a:limb -> b:limb -> Lemma
  (requires (True))
  (ensures (v a = v b ==> a == b))
  [SMTPat (v a); SMTPat (v b)]

inline_for_extraction val limb_zero: x:limb{v x = 0}
inline_for_extraction val limb_one: x:limb{v x = 1}

(* Addition primitives *)
inline_for_extraction val limb_add: a:limb -> b:limb{UInt.size (v a + v b) limb_n} -> Tot (c:limb{v a + v b = v c})
inline_for_extraction val limb_add_mod: a:limb -> b:limb -> Tot (c:limb{(v a + v b) % pow2 limb_n = v c})
(* Subtraction primitives *)
inline_for_extraction val limb_sub: a:limb -> b:limb{UInt.size (v a - v b) limb_n} -> Tot (c:limb{v a - v b = v c})
inline_for_extraction val limb_sub_mod: a:limb -> b:limb -> Tot (c:limb{(v a - v b) % pow2 limb_n = v c})
(* Multiplication primitives *)
inline_for_extraction val limb_mul: a:limb -> b:limb{UInt.size (v a * v b) limb_n} -> Tot (c:limb{v a * v b = v c})
inline_for_extraction val limb_mul_mod: a:limb -> b:limb -> Tot (c:limb{(v a * v b) % pow2 limb_n = v c})

(* Bitwise operators *)
inline_for_extraction val limb_logand: limb -> limb -> Tot limb
inline_for_extraction val limb_logxor: limb -> limb -> Tot limb
inline_for_extraction val limb_logor: limb -> limb -> Tot limb
inline_for_extraction val limb_lognot: limb -> Tot limb

(* Shift operators *)
inline_for_extraction val limb_shift_right: a:limb -> s:FStar.UInt32.t -> Tot (c:limb{FStar.UInt32.v s < limb_n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction val limb_shift_left: a:limb -> s:FStar.UInt32.t -> Tot (c:limb{FStar.UInt32.v s < limb_n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 limb_n)})

inline_for_extraction val limb_eq_mask: a:limb -> b:limb -> Tot (c:limb{(v a = v b ==> v c = pow2 limb_n - 1) /\ (v a <> v b ==> v c = 0)})
inline_for_extraction val limb_gte_mask: a:limb -> b:limb -> Tot (c:limb{(v a >= v b ==> v c = pow2 limb_n - 1) /\ (v a < v b ==> v c = 0)})
inline_for_extraction val limb_gt_mask: a:limb -> b:limb -> Tot (c:limb{(v a > v b ==> v c = pow2 limb_n - 1) /\ (v a <= v b ==> v c = 0)})
inline_for_extraction val limb_lt_mask: a:limb -> b:limb -> Tot (c:limb{(v a < v b ==> v c = pow2 limb_n - 1) /\ (v a >= v b ==> v c = 0)})
inline_for_extraction val limb_lte_mask: a:limb -> b:limb -> Tot (c:limb{(v a <= v b ==> v c = pow2 limb_n - 1) /\ (v a > v b ==> v c = 0)})

inline_for_extraction val limb_to_byte: x:limb -> Tot (y:Hacl.UInt8.t{Hacl.UInt8.v y = v x % pow2 8})
inline_for_extraction val byte_to_limb: x:Hacl.UInt8.t -> Tot (y:limb{Hacl.UInt8.v x = v y})


(* Wide limb operators *)
inline_for_extraction let wide_n = 2 * word_size

inline_for_extraction val w: wide -> GTot (FStar.UInt.uint_t wide_n)

val lemma_wide_injectivity: a:wide -> b:wide -> Lemma
  (requires (True))
  (ensures (w a = w b ==> a == b))
  [SMTPat (w a); SMTPat (w b)]

inline_for_extraction val wide_zero: x:wide{w x = 0}
inline_for_extraction val wide_one: x:wide{w x = 1}

(* Addition primitives *)
inline_for_extraction val wide_add: a:wide -> b:wide{UInt.size (w a + w b) wide_n} -> Tot (c:wide{w a + w b = w c})
inline_for_extraction val wide_add_mod: a:wide -> b:wide -> Tot (c:wide{(w a + w b) % pow2 wide_n = w c})
(* Subtraction primitives *)
inline_for_extraction val wide_sub: a:wide -> b:wide{UInt.size (w a - w b) wide_n} -> Tot (c:wide{w a - w b = w c})
inline_for_extraction val wide_sub_mod: a:wide -> b:wide -> Tot (c:wide{(w a - w b) % pow2 wide_n = w c})
(* Bitwise operators *)
inline_for_extraction val wide_logand: wide -> wide -> Tot wide
inline_for_extraction val wide_logxor: wide -> wide -> Tot wide
inline_for_extraction val wide_logor: wide -> wide -> Tot wide
inline_for_extraction val wide_lognot: wide -> Tot wide

(* Shift operators *)
inline_for_extraction val wide_shift_right: a:wide -> s:FStar.UInt32.t -> Tot (c:wide{FStar.UInt32.v s < wide_n ==> w c = (w a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction val wide_shift_left: a:wide -> s:FStar.UInt32.t -> Tot (c:wide{FStar.UInt32.v s < wide_n ==> w c = ((w a * pow2 (FStar.UInt32.v s)) % pow2 wide_n)})

inline_for_extraction val wide_eq_mask: a:wide -> b:wide -> Tot (c:wide{(w a = w b ==> w c = pow2 wide_n - 1) /\ (w a <> w b ==> w c = 0)})
inline_for_extraction val wide_gte_mask: a:wide -> b:wide -> Tot (c:wide{(w a >= w b ==> w c = pow2 wide_n - 1) /\ (w a < w b ==> w c = 0)})
inline_for_extraction val wide_gt_mask: a:wide -> b:wide -> Tot (c:wide{(w a > w b ==> w c = pow2 wide_n - 1) /\ (w a <= w b ==> w c = 0)})
inline_for_extraction val wide_lt_mask: a:wide -> b:wide -> Tot (c:wide{(w a < w b ==> w c = pow2 wide_n - 1) /\ (w a >= w b ==> w c = 0)})
inline_for_extraction val wide_lte_mask: a:wide -> b:wide -> Tot (c:wide{(w a <= w b ==> w c = pow2 wide_n - 1) /\ (w a > w b ==> w c = 0)})

inline_for_extraction val mul_wide: a:limb -> b:limb -> Tot (c:wide{w c = v a * v b})

inline_for_extraction val limb_to_wide: x:limb -> Tot (y:wide{w y = v x})
inline_for_extraction val wide_to_limb: x:wide -> Tot (y:limb{v y = w x % pow2 limb_n})
