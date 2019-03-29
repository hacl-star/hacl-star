module Hacl.Bignum.Parameters

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer
open Hacl.Cast
open Hacl.Bignum.Constants

(** The values of the prime for modular arithmetic **)
inline_for_extraction let prime = prime

(** Size of a word on the platform (32 or 64bits) **)
inline_for_extraction let word_size = word_size

(** Concrete platform word with side-channel protection **)
inline_for_extraction let limb : Type0 = limb
inline_for_extraction let wide : Type0 = wide
(* inline_for_extraction val limb: Type0 *)
(* inline_for_extraction val wide: Type0 *)
inline_for_extraction let ctr  = FStar.UInt32.t

(** Number of limbs of a bigint **)
inline_for_extraction let len = len
inline_for_extraction val clen: l:FStar.UInt32.t{FStar.UInt32.v l = len}
inline_for_extraction let clen = 5ul

type felem = b:buffer limb{length b = len}
type felem_wide = b:buffer wide{length b = len}

type seqelem = s:Seq.seq limb{Seq.length s = len}
type seqelem_wide = s:Seq.seq wide{Seq.length s = len}

(** Associates a weight in bits to each limb of the bigint *)
inline_for_extraction val climb_size: l:FStar.UInt32.t{limb_size = FStar.UInt32.v l}
inline_for_extraction let climb_size = assert_norm(pow2 32 > 51); 51ul

val lemma_prime_limb_size: unit -> Lemma (pow2 (len * limb_size) > prime)
let lemma_prime_limb_size () = assert_norm (pow2 (5 * 51) > pow2 255 - 19)

open Hacl.UInt64

inline_for_extraction let limb_n = word_size
inline_for_extraction val v: limb -> GTot (FStar.UInt.uint_t limb_n)
inline_for_extraction let v x = v x


val lemma_limb_injectivity: a:limb -> b:limb -> Lemma
  (requires (True))
  (ensures (v a = v b ==> a == b))
  [SMTPat (v a); SMTPat (v b)]
let lemma_limb_injectivity a b = ()

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
inline_for_extraction val limb_logand: a:limb -> b:limb -> Tot (c:limb{v c = UInt.logand (v a) (v b)})
inline_for_extraction val limb_logxor: a:limb -> b:limb -> Tot (c:limb{v c = UInt.logxor (v a) (v b)})
inline_for_extraction val limb_logor: a:limb -> b:limb -> Tot (c:limb{v c = UInt.logor (v a) (v b)})
inline_for_extraction val limb_lognot: a:limb -> Tot (b:limb{v b = UInt.lognot (v a)})

(* Shift operators *)
inline_for_extraction val limb_shift_right: a:limb -> s:FStar.UInt32.t{FStar.UInt32.v s < limb_n} -> Tot (c:limb{v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction val limb_shift_left: a:limb -> s:FStar.UInt32.t{FStar.UInt32.v s < limb_n} -> Tot (c:limb{v c = (v a * pow2 (FStar.UInt32.v s)) % pow2 limb_n})

inline_for_extraction val limb_eq_mask: a:limb -> b:limb -> Tot (c:limb{(v a = v b ==> v c = pow2 limb_n - 1) /\ (v a <> v b ==> v c = 0)})
inline_for_extraction val limb_gte_mask: a:limb -> b:limb -> Tot (c:limb{(v a >= v b ==> v c = pow2 limb_n - 1) /\ (v a < v b ==> v c = 0)})
inline_for_extraction val limb_gt_mask: a:limb -> b:limb -> Tot (c:limb{(v a > v b ==> v c = pow2 limb_n - 1) /\ (v a <= v b ==> v c = 0)})
inline_for_extraction val limb_lt_mask: a:limb -> b:limb -> Tot (c:limb{(v a < v b ==> v c = pow2 limb_n - 1) /\ (v a >= v b ==> v c = 0)})
inline_for_extraction val limb_lte_mask: a:limb -> b:limb -> Tot (c:limb{(v a <= v b ==> v c = pow2 limb_n - 1) /\ (v a > v b ==> v c = 0)})

inline_for_extraction val limb_to_byte: x:limb -> Tot (y:Hacl.UInt8.t{Hacl.UInt8.v y = v x % pow2 8})
inline_for_extraction val byte_to_limb: x:Hacl.UInt8.t -> Tot (y:limb{Hacl.UInt8.v x = v y})

inline_for_extraction let limb_zero = uint64_to_sint64 0uL
inline_for_extraction let limb_one  = uint64_to_sint64 1uL

(* Addition primitives *)
inline_for_extraction let limb_add a b = add a b
inline_for_extraction let limb_add_mod a b = add_mod a b
(* Subtraction primitives *)
inline_for_extraction let limb_sub a b = sub a b
inline_for_extraction let limb_sub_mod a b = sub_mod a b
(* Multiplication primitives *)
inline_for_extraction let limb_mul a b = mul a b
inline_for_extraction let limb_mul_mod a b = mul_mod a b

(* Bitwise operators *)
inline_for_extraction let limb_logand a b = logand a b
inline_for_extraction let limb_logxor a b = logxor a b
inline_for_extraction let limb_logor  a b = logor  a b
inline_for_extraction let limb_lognot a   = lognot a

(* Shift operators *)
inline_for_extraction let limb_shift_right a s = shift_right a s
inline_for_extraction let limb_shift_left  a s = shift_left a s

inline_for_extraction let limb_eq_mask a b  = eq_mask a b
inline_for_extraction let limb_gte_mask a b = gte_mask a b
inline_for_extraction let limb_gt_mask a b  = gt_mask a b
inline_for_extraction let limb_lt_mask a b  = lt_mask a b
inline_for_extraction let limb_lte_mask a b = lte_mask a b

inline_for_extraction let limb_to_byte x = assert_norm(pow2 8 = 256); sint64_to_sint8 x
inline_for_extraction let byte_to_limb x = sint8_to_sint64 x

(* Wide limb operators *)
inline_for_extraction let wide_n = 2 * word_size

inline_for_extraction val w: wide -> GTot (FStar.UInt.uint_t wide_n)
inline_for_extraction let w x = Hacl.UInt128.v x

(* #set-options "--admit_smt_queries true" *)

val lemma_wide_injectivity: a:wide -> b:wide -> Lemma
  (requires (True))
  (ensures (w a = w b ==> a == b))
  [SMTPat (w a); SMTPat (w b)]
let lemma_wide_injectivity a b = FStar.Classical.move_requires (FStar.UInt128.v_inj a) b

inline_for_extraction val wide_zero: x:wide{w x = 0}
inline_for_extraction val wide_one: x:wide{w x = 1}

(* Addition primitives *)
inline_for_extraction val wide_add: a:wide -> b:wide{UInt.size (w a + w b) wide_n} -> Tot (c:wide{w a + w b = w c})
inline_for_extraction val wide_add_mod: a:wide -> b:wide -> Tot (c:wide{(w a + w b) % pow2 wide_n = w c})
(* Subtraction primitives *)
inline_for_extraction val wide_sub: a:wide -> b:wide{UInt.size (w a - w b) wide_n} -> Tot (c:wide{w a - w b = w c})
inline_for_extraction val wide_sub_mod: a:wide -> b:wide -> Tot (c:wide{(w a - w b) % pow2 wide_n = w c})
(* Bitwise operators *)
inline_for_extraction val wide_logand: a:wide -> b:wide -> Tot (c:wide{w c = UInt.logand (w a) (w b)})
inline_for_extraction val wide_logxor: a:wide -> b:wide -> Tot (c:wide{w c = UInt.logxor (w a) (w b)})
inline_for_extraction val wide_logor: a:wide -> b:wide -> Tot (c:wide{w c = UInt.logor (w a) (w b)})
inline_for_extraction val wide_lognot: a:wide -> Tot (b:wide{w b = UInt.lognot (w a)})

(* Shift operators *)
inline_for_extraction val wide_shift_right: a:wide -> s:FStar.UInt32.t{FStar.UInt32.v s < wide_n} -> Tot (c:wide{w c = (w a / (pow2 (FStar.UInt32.v s)))})

inline_for_extraction val wide_shift_left: a:wide -> s:FStar.UInt32.t{FStar.UInt32.v s < wide_n} -> Tot (c:wide{w c = ((w a * pow2 (FStar.UInt32.v s)) % pow2 wide_n)})

inline_for_extraction val wide_eq_mask: a:wide -> b:wide -> Tot (c:wide{(w a = w b ==> w c = pow2 wide_n - 1) /\ (w a <> w b ==> w c = 0)})
inline_for_extraction val wide_gte_mask: a:wide -> b:wide -> Tot (c:wide{(w a >= w b ==> w c = pow2 wide_n - 1) /\ (w a < w b ==> w c = 0)})
inline_for_extraction val wide_gt_mask: a:wide -> b:wide -> Tot (c:wide{(w a > w b ==> w c = pow2 wide_n - 1) /\ (w a <= w b ==> w c = 0)})
inline_for_extraction val wide_lt_mask: a:wide -> b:wide -> Tot (c:wide{(w a < w b ==> w c = pow2 wide_n - 1) /\ (w a >= w b ==> w c = 0)})
inline_for_extraction val wide_lte_mask: a:wide -> b:wide -> Tot (c:wide{(w a <= w b ==> w c = pow2 wide_n - 1) /\ (w a > w b ==> w c = 0)})

inline_for_extraction val mul_wide: a:limb -> b:limb -> Tot (c:wide{w c = v a * v b})

inline_for_extraction val limb_to_wide: x:limb -> Tot (y:wide{w y = v x})
inline_for_extraction val wide_to_limb: x:wide -> Tot (y:limb{v y = w x % pow2 limb_n})

inline_for_extraction val uint64_to_limb: x:FStar.UInt64.t{FStar.UInt64.v x < pow2 word_size} ->
  Tot (y:limb{v y = FStar.UInt64.v x})

inline_for_extraction let wide_zero = sint64_to_sint128 (uint64_to_sint64 0uL)
inline_for_extraction let wide_one  = sint64_to_sint128 (uint64_to_sint64 1uL)

(* Addition primitives *)
inline_for_extraction let wide_add a b = Hacl.UInt128.add a b
inline_for_extraction let wide_add_mod a b = Hacl.UInt128.add_mod a b
(* Subtraction primitives *)
inline_for_extraction let wide_sub a b = Hacl.UInt128.sub a b
inline_for_extraction let wide_sub_mod a b = Hacl.UInt128.sub_mod a b

(* Bitwise operators *)
inline_for_extraction let wide_logand a b = Hacl.UInt128.logand a b
inline_for_extraction let wide_logxor a b = Hacl.UInt128.logxor a b
inline_for_extraction let wide_logor  a b = Hacl.UInt128.logor  a b
inline_for_extraction let wide_lognot a   = Hacl.UInt128.lognot a

(* Shift operators *)
inline_for_extraction let wide_shift_right a s = Hacl.UInt128.shift_right a s
inline_for_extraction let wide_shift_left  a s = Hacl.UInt128.shift_left a s

inline_for_extraction let wide_eq_mask a b  = Hacl.UInt128.eq_mask a b
inline_for_extraction let wide_gte_mask a b = Hacl.UInt128.gte_mask a b
inline_for_extraction let wide_gt_mask a b  = Hacl.UInt128.gt_mask a b
inline_for_extraction let wide_lt_mask a b  = Hacl.UInt128.lt_mask a b
inline_for_extraction let wide_lte_mask a b = Hacl.UInt128.lte_mask a b

inline_for_extraction let mul_wide x y = Hacl.UInt128.mul_wide x y

inline_for_extraction let limb_to_wide x = sint64_to_sint128 x
inline_for_extraction let wide_to_limb x = sint128_to_sint64 x

inline_for_extraction let uint64_to_limb x = Hacl.Cast.uint64_to_sint64 x

inline_for_extraction
let mask_51 : x:limb{v x = pow2 51 - 1} =
  assert_norm (0x7ffffffffffff < pow2 64);
  assert_norm (0x7ffffffffffff = pow2 51 - 1);
  uint64_to_limb 0x7ffffffffffffuL

inline_for_extraction let mask_51_wide : x:wide{w x = pow2 51 - 1} =
  limb_to_wide mask_51

inline_for_extraction let climb_mask = mask_51
inline_for_extraction let climb_mask_wide = mask_51_wide
