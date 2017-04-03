module Hacl.Spec.BignumQ.Mul

open FStar.Mul
open FStar.Seq
open FStar.UInt64
open Hacl.Spec.BignumQ.Eval

#reset-options "--max_fuel 0 --max_ifuel 0"

let qelem_56 = x:qelem{v x.[0] < 0x100000000000000 /\ v x.[1] < 0x100000000000000 /\
                     v x.[2] < 0x100000000000000 /\ v x.[3] < 0x100000000000000 /\
                     v x.[4] < 0x100000000000000}

let m: m:qelem_56{eval_q m == 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed} =
  Seq.Create.create_5 0x12631a5cf5d3eduL 0xf9dea2f79cd658uL 0x000000000014deuL 0x00000000000000uL
	             0x00000010000000uL

let mu: mu:qelem_56{eval_q mu == 0xfffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c131b} =
  Seq.Create.create_5 0x9ce5a30a2c131buL 0x215d086329a7eduL 0xffffffffeb2106uL 0xffffffffffffffuL
	             0x00000fffffffffuL

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

val choose:
  x:qelem ->
  y:qelem ->
  b:u64{b == 0uL \/ b == 1uL} ->
  Tot (z:qelem{((b == 1uL) ==> (z == x)) /\ ((b == 0uL) ==> (z == y))})
let choose x y b =
  let mask = b -%^ 1uL in
  assert_norm(pow2 64 - 1 = (0 - 1) % pow2 64);
  assert(v mask = 0 \/ v mask = pow2 64 - 1);
  assert(v mask = UInt.zero 64 \/ v mask = UInt.ones 64);
  let x0 = x.[0] in
  let x1 = x.[1] in
  let x2 = x.[2] in
  let x3 = x.[3] in
  let x4 = x.[4] in
  let y0 = y.[0] in
  let y1 = y.[1] in
  let y2 = y.[2] in
  let y3 = y.[3] in
  let y4 = y.[4] in
  let z0 = ((y0 ^^ x0) &^ mask) ^^ x0 in
  let z1 = ((y1 ^^ x1) &^ mask) ^^ x1 in
  let z2 = ((y2 ^^ x2) &^ mask) ^^ x2 in
  let z3 = ((y3 ^^ x3) &^ mask) ^^ x3 in
  let z4 = ((y4 ^^ x4) &^ mask) ^^ x4 in
  UInt.logand_lemma_1 (v (y0 ^^ x0));
  UInt.logand_lemma_1 (v (y1 ^^ x1));
  UInt.logand_lemma_1 (v (y2 ^^ x2));
  UInt.logand_lemma_1 (v (y3 ^^ x3));
  UInt.logand_lemma_1 (v (y4 ^^ x4));
  UInt.logand_lemma_2 (v (y0 ^^ x0));
  UInt.logand_lemma_2 (v (y1 ^^ x1));
  UInt.logand_lemma_2 (v (y2 ^^ x2));
  UInt.logand_lemma_2 (v (y3 ^^ x3));
  UInt.logand_lemma_2 (v (y4 ^^ x4));
  UInt.logxor_inv (v y0) (v x0);
  UInt.logxor_inv (v y1) (v x1);
  UInt.logxor_inv (v y2) (v x2);
  UInt.logxor_inv (v y3) (v x3);
  UInt.logxor_inv (v y4) (v x4);
  UInt.logxor_commutative (UInt.zero 64) (v x0);
  UInt.logxor_commutative (UInt.zero 64) (v x1);
  UInt.logxor_commutative (UInt.zero 64) (v x2);
  UInt.logxor_commutative (UInt.zero 64) (v x3);
  UInt.logxor_commutative (UInt.zero 64) (v x4);
  UInt.logxor_lemma_1 (v x0);
  UInt.logxor_lemma_1 (v x1);
  UInt.logxor_lemma_1 (v x2);
  UInt.logxor_lemma_1 (v x3);
  UInt.logxor_lemma_1 (v x4);
  let z = Seq.Create.create_5 z0 z1 z2 z3 z4 in
  if b = 0uL then lemma_eq_intro z y
  else lemma_eq_intro z x;
  z


inline_for_extraction
let lt (a:u64{v a < pow2 63}) (b:u64{v b < pow2 63}) :
  Tot (c:u64{if v a >= v b then c == 0x0uL else c == 0x1uL})
  = let r = (a -%^ b) >>^ 63ul in r

inline_for_extraction
let shiftl_56 (b:u64{b == 0uL \/ b == 1uL}) :
  Tot (c:u64{(b == 1uL ==> c == 0x100000000000000uL) /\ (b == 0uL ==> c == 0uL)})
  = assert_norm(pow2 56 = 0x100000000000000);
    b <<^ 56ul

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

val subm_step:
  x:u64{v x < 0x100000000000000} ->
  y:u64{v y <= 0x100000000000000} ->
  Tot (t:(tuple2 u64 u64){(fst t == 0uL \/ fst t == 1uL)
    /\ v x - v y == v (snd t) - 0x100000000000000 * v (fst t)
    /\ v (snd t) < 0x100000000000000})
let subm_step x y =
  let b  = lt x y in
  let t = (shiftl_56 b +^ x) -^ y in
  b, t


val subm_conditional:
  x:qelem_56 ->
  Tot (y:qelem_56{if eval_q x >= eval_q m then eval_q y = eval_q x - eval_q m else eval_q y = eval_q x})
let subm_conditional r =
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 32 = 0x100000000);
  let r0 = r.[0] in
  let r1 = r.[1] in
  let r2 = r.[2] in
  let r3 = r.[3] in
  let r4 = r.[4] in
  let m0 = m.[0] in
  let m1 = m.[1] in
  let m2 = m.[2] in
  let m3 = m.[3] in
  let m4 = m.[4] in
  let pb = m0 in
  let b, t0 = subm_step r0 m0 in
  let b, t1 = subm_step r1 (m1+^b) in
  let b, t2 = subm_step r2 (m2+^b) in
  let b, t3 = subm_step r3 (m3+^b) in
  let b, t4 = subm_step r4 (m4+^b) in
  let z = Seq.Create.create_5 t0 t1 t2 t3 t4 in
  choose r z b

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"

private let lemma_mul_ineq (a:nat) (b:nat) (c:nat) : Lemma (requires (a < c /\ b < c))
                                                        (ensures  (a * b < c * c))
  = ()

inline_for_extraction
let op_Star_Star (x:u64{v x < 0x100000000000000}) (y:u64{v y < 0x100000000000000}) :
  Tot (z:UInt128.t{UInt128.v z < 0x10000000000000000000000000000 /\ UInt128.v z = v x * v y})
  = assert_norm(0x100000000000000 * 0x100000000000000 = 0x10000000000000000000000000000);
  lemma_mul_ineq (v x) (v y) 0x100000000000000;
  FStar.UInt128.mul_wide x y

val split_56:
  x:UInt128.t{UInt128.v x < 0x100000000000000000000000000000} ->
  Tot (t:tuple2 UInt128.t u64{
    UInt128.v (fst t) == UInt128.v x / 0x100000000000000
    /\ UInt64.v (snd t) == UInt128.v x % 0x100000000000000
    /\ UInt128.v (fst t) <= 0x1000000000000000})
let split_56 x =
  let carry = FStar.UInt128.(x >>^ 56ul) in
  let t     = Int.Cast.uint128_to_uint64 x &^ 0xffffffffffffffuL in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (FStar.UInt128.v x) 56 64;
  carry, t

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

(* private *)
(* let lemma_distr_5_0 a b c d e f : Lemma *)
(*   (a * (b + 0x100000000000000 * c + 0x10000000000000000000000000000 * d + *)
(*    0x1000000000000000000000000000000000000000000 * e + 0x00000000000000000000000000000000000000000000000000000000 * f) == *)
(*    (a * b + 0x100000000000000 * a * c + 0x10000000000000000000000000000 * a * d + *)
(*    0x1000000000000000000000000000000000000000000 * a * e + 0x00000000000000000000000000000000000000000000000000000000 * a * f)) = () *)

(* private *)
(* let lemma_distr_5_1 a b c d e f : Lemma *)
(*   (0x100000000000000 * a * (b + 0x100000000000000 * c + 0x10000000000000000000000000000 * d + *)
(*    0x1000000000000000000000000000000000000000000 * e + 0x00000000000000000000000000000000000000000000000000000000 * f) == *)
(*    (0x100000000000000 * a * b + 0x10000000000000000000000000000 * a * c + 0x1000000000000000000000000000000000000000000 * a * d + *)
(*    0x100000000000000000000000000000000000000000000000000000000 * a * e + 0x0000000000000000000000000000000000000000000000000000000000000000000000 * a * f)) = () *)


(* private *)
(* let lemma_distr_5_2 a b c d e f : Lemma *)
(*   (0x10000000000000000000000000000 * a * (b + 0x100000000000000 * c + 0x10000000000000000000000000000 * d + *)
(*    0x1000000000000000000000000000000000000000000 * e + 0x00000000000000000000000000000000000000000000000000000000 * f) == *)
(*    (0x10000000000000000000000000000 * a * b + 0x1000000000000000000000000000000000000000000 * a * c + 0x100000000000000000000000000000000000000000000000000000000 * a * d + *)
(*    0x10000000000000000000000000000000000000000000000000000000000000000000000 * a * e + 0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * a * f)) = () *)

(* private *)
(* let lemma_distr_5_3 a b c d e f : Lemma *)
(*   (0x1000000000000000000000000000000000000000000 * a * (b + 0x100000000000000 * c + 0x10000000000000000000000000000 * d + *)
(*    0x1000000000000000000000000000000000000000000 * e + 0x00000000000000000000000000000000000000000000000000000000 * f) == *)
(*    (0x1000000000000000000000000000000000000000000 * a * b + 0x100000000000000000000000000000000000000000000000000000000 * a * c + 0x10000000000000000000000000000000000000000000000000000000000000000000000 * a * d + *)
(*    0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * a * e + 0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * a * f)) = () *)


(* private *)
(* let lemma_distr_5_4 a b c d e f : Lemma *)
(*   (0x100000000000000000000000000000000000000000000000000000000 * a * (b + 0x100000000000000 * c + 0x10000000000000000000000000000 * d + *)
(*    0x1000000000000000000000000000000000000000000 * e + 0x00000000000000000000000000000000000000000000000000000000 * f) == *)
(*    (0x100000000000000000000000000000000000000000000000000000000 * a * b + 0x10000000000000000000000000000000000000000000000000000000000000000000000 * a * c + 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * a * d + *)
(*    0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * a * e + 0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * a * f)) = () *)

private
let lemma_distr_5 (a:qelem) (b:qelem) : Lemma
  (eval_q a * eval_q b =
   a.[0] * b.[0] +
   0x100000000000000 * (a.[0] * b.[1] + a.[1] * b.[0]) +
   0x10000000000000000000000000000 * (a.[0] * b.[2] + a.[1] * b.[1] + a.[2] * b.[0]) +
   0x1000000000000000000000000000000000000000000 * (a.[0] * b.[3] + a.[1] * b.[2] + a.[2] * b.[1] + a.[3] * b.[0]) +
   0x100000000000000000000000000000000000000000000000000000000 * (a.[0] * b.[4] + a.[1] * b.[3] + a.[2] * b.[2] + a.[3] * b.[1] + a.[4] * b.[0]) +
   0x10000000000000000000000000000000000000000000000000000000000000000000000 * (a.[1] * b.[4] + a.[2] * b.[3] + a.[3] * b.[2] + a.[4] * b.[1]) +
   0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * (a.[2] * b.[4] + a.[3] * b.[3] + a.[4] * b.[2]) +
   0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * (a.[3] * b.[4] + a.[4] * b.[3]) +
   0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * (a.[4] * b.[4])
  )
  = lemma_distr_5_0 a.[0] b.[0] b.[1] b.[2] b.[3] b.[4];
    lemma_distr_5_1 a.[1] b.[0] b.[1] b.[2] b.[3] b.[4];
    lemma_distr_5_2 a.[2] b.[0] b.[1] b.[2] b.[3] b.[4];
    lemma_distr_5_3 a.[3] b.[0] b.[1] b.[2] b.[3] b.[4];
    lemma_distr_5_4 a.[4] b.[0] b.[1] b.[2] b.[3] b.[4]


val low_mul_5:
  x:qelem_56 ->
  y:qelem_56 ->
  Tot (z:qelem_56)
let low_mul_5 x y =
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  assert_norm(pow2 56  = 0x100000000000000);
  let x0 = x.[0] in
  let x1 = x.[1] in
  let x2 = x.[2] in
  let x3 = x.[3] in
  let x4 = x.[4] in
  let y0 = y.[0] in
  let y1 = y.[1] in
  let y2 = y.[2] in
  let y3 = y.[3] in
  let y4 = y.[4] in
  let xy00 = x0 ** y0 in
  let xy01 = x0 ** y1 in
  let xy02 = x0 ** y2 in
  let xy03 = x0 ** y3 in
  let xy04 = x0 ** y4 in
  let xy10 = x1 ** y0 in
  let xy11 = x1 ** y1 in
  let xy12 = x1 ** y2 in
  let xy13 = x1 ** y3 in
  let xy20 = x2 ** y0 in
  let xy21 = x2 ** y1 in
  let xy22 = x2 ** y2 in
  let xy30 = x3 ** y0 in
  let xy31 = x3 ** y1 in
  let xy40 = x4 ** y0 in
  let open FStar.UInt128 in
  let carry, t0 = split_56 xy00 in
  let carry, t1 = split_56 (xy01 +^ xy10 +^ carry) in
  let carry, t2 = split_56 (xy02 +^ xy11 +^ xy20 +^ carry) in
  let carry, t3 = split_56 (xy03 +^ xy12 +^ xy21 +^ xy30 +^ carry) in
  let carry, t4 = split_56 (xy04 +^ xy13 +^ xy22 +^ xy31 +^ xy40 +^ carry) in
  admit()
