module Hacl.Spec.BignumQ.Mul

open FStar.Mul
open FStar.Seq
open FStar.UInt64
open Hacl.Spec.BignumQ.Eval

module U64 = FStar.UInt64

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

inline_for_extraction
val mod_40: x:UInt128.t -> Tot (z:U64.t{v z = UInt128.v x % (pow2 40)})
inline_for_extraction
let mod_40 x =
  let x' = Int.Cast.uint128_to_uint64 x in
  let x'' = x' &^ 0xffffffffffuL in
  UInt.logand_mask (v x') 40;
  assert_norm(pow2 40   = 0x10000000000);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (UInt128.v x) 40 64;
  x''

val low_mul_5:
  x:qelem_56 ->
  y:qelem_56 ->
  Tot (z:qelem_56{eval_q z = (eval_q x * eval_q y) % pow2 264})
#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 500"
let low_mul_5 x y =
  assert_norm(pow2 128  = 0x100000000000000000000000000000000);
  assert_norm(pow2 40   = 0x10000000000);
  assert_norm(pow2 56   = 0x100000000000000);
  assert_norm(pow2 112  = 0x10000000000000000000000000000);
  assert_norm(pow2 168  = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224  = 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 264  = 0x1000000000000000000000000000000000000000000000000000000000000000000);
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
  let        t4 = mod_40   (xy04 +^ xy13 +^ xy22 +^ xy31 +^ xy40 +^ carry) in
  let open FStar.UInt64 in
  assert(v t0 = (v x0 * v y0) % pow2 56);
  assert(v t1 = ((v x1 * v y0 + v x0 * v y1 + ((v x0 * v y0) / pow2 56)) % pow2 56));
  assert(v t2 = ((v x2 * v y0 + v x1 * v y1 + v x0 * v y2 + ((v x1 * v y0 + v x0 * v y1 + ((v x0 * v y0) / pow2 56)) / pow2 56)) % pow2 56));
  assert(v t3 = ((v x3 * v y0 + v x2 * v y1 + v x1 * v y2 + v x0 * v y3 + ((v x2 * v y0 + v x1 * v y1 + v x0 * v y2 + ((v x1 * v y0 + v x0 * v y1 + ((v x0 * v y0) / pow2 56)) / pow2 56)) / pow2 56)) % pow2 56));
  assert(v t4 = (v x4 * v y0 + v x3 * v y1 + v x2 * v y2 + v x1 * v y3 + v x0 * v y4 + ((v x3 * v y0 + v x2 * v y1 + v x1 * v y2 + v x0 * v y3 + ((v x2 * v y0 + v x1 * v y1 + v x0 * v y2 + ((v x1 * v y0 + v x0 * v y1 + ((v x0 * v y0) / pow2 56)) / pow2 56)) / pow2 56)) / pow2 56)) % pow2 40);
  Hacl.Spec.BignumQ.Mul.Lemmas_1.lemma_mul_5_low_264 (v x0) (v x1) (v x2) (v x3) (v x4) (v y0) (v y1) (v y2) (v y3) (v y4);
  Seq.Create.create_5 t0 t1 t2 t3 t4


val mul_5:
  x:qelem_56 ->
  y:qelem_56 ->
  Tot (z:seq UInt128.t{
    length z = 9
    /\ (eval_q_wide z.[0] z.[1] z.[2] z.[3] z.[4] z.[5] z.[6] z.[7] z.[8]
    = eval_q x * eval_q y)
    /\ UInt128.v z.[0] < 0x10000000000000000000000000000
    /\ UInt128.v z.[1] < 0x20000000000000000000000000000
    /\ UInt128.v z.[2] < 0x30000000000000000000000000000
    /\ UInt128.v z.[3] < 0x40000000000000000000000000000
    /\ UInt128.v z.[4] < 0x50000000000000000000000000000
    /\ UInt128.v z.[5] < 0x40000000000000000000000000000
    /\ UInt128.v z.[6] < 0x30000000000000000000000000000
    /\ UInt128.v z.[7] < 0x20000000000000000000000000000
    /\ UInt128.v z.[8] < 0x10000000000000000000000000000 })    
#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let mul_5 x y =
  assert_norm(pow2 128  = 0x100000000000000000000000000000000);
  assert_norm(pow2 40   = 0x10000000000);
  assert_norm(pow2 56   = 0x100000000000000);
  assert_norm(pow2 112  = 0x10000000000000000000000000000);
  assert_norm(pow2 168  = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224  = 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 280  = 0x10000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 336  = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 392  = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 448  = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
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
  let xy14 = x1 ** y4 in
  let xy20 = x2 ** y0 in
  let xy21 = x2 ** y1 in
  let xy22 = x2 ** y2 in
  let xy23 = x2 ** y3 in
  let xy24 = x2 ** y4 in
  let xy30 = x3 ** y0 in
  let xy31 = x3 ** y1 in
  let xy32 = x3 ** y2 in
  let xy33 = x3 ** y3 in
  let xy34 = x3 ** y4 in
  let xy40 = x4 ** y0 in
  let xy41 = x4 ** y1 in
  let xy42 = x4 ** y2 in
  let xy43 = x4 ** y3 in
  let xy44 = x4 ** y4 in
  let open FStar.UInt128 in
  let z0 = xy00 in
  let z1 = xy01 +^ xy10 in
  let z2 = xy02 +^ xy11 +^ xy20 in
  let z3 = xy03 +^ xy12 +^ xy21 +^ xy30 in
  let z4 = xy04 +^ xy13 +^ xy22 +^ xy31 +^ xy40 in
  let z5 =         xy14 +^ xy23 +^ xy32 +^ xy41 in
  let z6 =                 xy24 +^ xy33 +^ xy42 in
  let z7 =                         xy34 +^ xy43 in
  let z8 =                                 xy44 in
  let z9 = Int.Cast.uint64_to_uint128 0uL in
  Hacl.Spec.BignumQ.Mul.Lemmas_1.lemma_mul_5' (U64.v x0) (U64.v x1) (U64.v x2) (U64.v x3) (U64.v x4) (U64.v y0) (U64.v y1) (U64.v y2) (U64.v y3) (U64.v y4);
  assert(eval_q x * eval_q y == eval_q_wide z0 z1 z2 z3 z4 z5 z6 z7 z8);
  Seq.Create.create_9 z0 z1 z2 z3 z4 z5 z6 z7 z8


val carry_step:
  x:UInt128.t -> y:UInt128.t{UInt128.v y < 0x50000000000000000000000000000} ->
  Tot (t:tuple2 UInt64.t UInt128.t{
    UInt128.v x + 0x100000000000000 * UInt128.v y == v (fst t) + 0x100000000000000 * UInt128.v (snd t)
    /\ v (fst t) < 0x100000000000000})
let carry_step x y =
  let carry = FStar.UInt128.(x >>^ 56ul) in
  let t     = Int.Cast.uint128_to_uint64 x &^ 0xffffffffffffffuL in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (FStar.UInt128.v x) 56 64;
  t, FStar.UInt128.add y carry


val carry:
  z:seq UInt128.t{length z = 9 /\ 
    eval_q_wide z.[0] z.[1] z.[2] z.[3] z.[4] z.[5] z.[6] z.[7] z.[8] < (pow2 256 - 1) * (pow2 256 - 1)
    /\ UInt128.v z.[0] < 0x10000000000000000000000000000
    /\ UInt128.v z.[1] < 0x20000000000000000000000000000
    /\ UInt128.v z.[2] < 0x30000000000000000000000000000
    /\ UInt128.v z.[3] < 0x40000000000000000000000000000
    /\ UInt128.v z.[4] < 0x50000000000000000000000000000
    /\ UInt128.v z.[5] < 0x40000000000000000000000000000
    /\ UInt128.v z.[6] < 0x30000000000000000000000000000
    /\ UInt128.v z.[7] < 0x20000000000000000000000000000
    /\ UInt128.v z.[8] < 0x10000000000000000000000000000 } ->
  Tot (t:tuple2 qelem_56 qelem{
      let r = fst t in let q = snd t in
      eval_q r = eval_q_wide z.[0] z.[1] z.[2] z.[3] z.[4] z.[5] z.[6] z.[7] z.[8] % pow2 264
      /\ eval_q q = eval_q_wide z.[0] z.[1] z.[2] z.[3] z.[4] z.[5] z.[6] z.[7] z.[8] / pow2 224
      /\ v q.[0] < 0x100000000000000
      /\ v q.[1] < 0x100000000000000
      /\ v q.[2] < 0x100000000000000
      /\ v q.[3] < 0x100000000000000
    })
let carry z =
  let z0 = z.[0] in
  let z1 = z.[1] in
  let z2 = z.[2] in
  let z3 = z.[3] in
  let z4 = z.[4] in
  let z5 = z.[5] in
  let z6 = z.[6] in
  let z7 = z.[7] in
  let z8 = z.[8] in
  let x0, z1' = carry_step z0 z1 in
  let x1, z2' = carry_step z1' z2 in
  let x2, z3' = carry_step z2' z3 in
  let x3, z4' = carry_step z3' z4 in
  let x4, z5' = carry_step z4' z5 in
  let x5, z6' = carry_step z5' z6 in
  let x6, z7' = carry_step z6' z7 in
  let x7, z8' = carry_step z7' z8 in
  assert(eval_q_wide z.[0] z.[1] z.[2] z.[3] z.[4] z.[5] z.[6] z.[7] z.[8]
    =   UInt64.v x0 + p1 * UInt64.v x1 + p2 * UInt64.v x2 + p3 * UInt64.v x3 + p4 * UInt64.v x4
  + p5 * UInt64.v x5 + p6 * UInt64.v x6 + p7 * UInt64.v x7 + p8 * UInt128.v z8');
  assert_norm((pow2 256 - 1) * (pow2 256 - 1) < 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert(UInt128.v z8' < 0x10000000000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  let x8 = Int.Cast.uint128_to_uint64 z8' in
  Math.Lemmas.modulo_lemma (UInt128.v z8') (pow2 64);
  assert(eval_q_wide z.[0] z.[1] z.[2] z.[3] z.[4] z.[5] z.[6] z.[7] z.[8]
    = v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4
      + p5 * v x5 + p6 * v x6 + p7 * v x7 + p8 * v x8);
  let x4' = x4 &^ 0xffffffffffuL in
  assert_norm(pow2 40 = 0x10000000000);
  UInt.logand_mask (v x4) 40;
  assert(v x4' = v x4 % pow2 40);
  Hacl.Spec.BignumQ.Mul.Lemmas_3.lemma_mod_264 x0 x1 x2 x3 x4 x5 x6 x7 x8;
  Hacl.Spec.BignumQ.Mul.Lemmas_3.lemma_div_224 x0 x1 x2 x3 x4 x5 x6 x7 x8;
  let r = Seq.Create.create_5 x0 x1 x2 x3 x4' in
  let q = Seq.Create.create_5 x4 x5 x6 x7 x8 in
  r, q
