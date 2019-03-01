module Hacl.Spec.EC.Format

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open Hacl.Cast
open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum
open Hacl.Spec.EC.Point


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

type uint8_s = Seq.seq Hacl.UInt8.t

private inline_for_extraction let zero_8 = uint8_to_sint8 0uy

val point_inf: unit -> Tot (t:spoint_513{selem (fst t) = 1 /\ selem (snd t) = 0})
let point_inf () =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  let x = Seq.upd x 0 limb_one in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 x;
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 z;
  cut (Hacl.Spec.Bignum.Bigint.seval x = 1);
  cut (Hacl.Spec.Bignum.Bigint.seval z = 0);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval x) (pow2 255 - 19);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval z) (pow2 255 - 19);
  x, z


val alloc_point: unit -> Tot (p:spoint_513{selem (fst p) = 0 /\ selem (snd p) = 0})
let alloc_point () =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 x;
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 z;
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval x) (pow2 255 - 19);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval z) (pow2 255 - 19);
  x, z


open FStar.Old.Endianness
open Hacl.Spec.Endianness
open Hacl.Endianness

val load64_le_spec: b:uint8_s{Seq.length b = 8} -> GTot (z:limb{v z = hlittle_endian b})
let load64_le_spec b =
  let z = hlittle_endian b in
  lemma_little_endian_is_bounded (reveal_sbytes b);
  Hacl.Cast.uint64_to_sint64 (FStar.UInt64.uint_to_t z)


val store64_le_spec: z:Hacl.Bignum.Limb.t -> GTot (b:uint8_s{Seq.length b = 8 /\ hlittle_endian b = v z})
let store64_le_spec z =
  let b = little_bytes 8ul (v z) in
  intro_sbytes b


inline_for_extraction let mask_51 : p:t{v p = pow2 51 - 1} = assert_norm(pow2 51 - 1 = 0x7ffffffffffff);
  uint64_to_limb 0x7ffffffffffffuL


inline_for_extraction val seq_upd_5: s0:limb -> s1:limb -> s2:limb -> s3:limb -> s4:limb -> Tot (s:seqelem{Seq.index s 0 == s0 /\ Seq.index s 1 == s1 /\ Seq.index s 2 == s2 /\ Seq.index s 3 == s3 /\ Seq.index s 4 == s4})
inline_for_extraction let seq_upd_5 s0 s1 s2 s3 s4 =
  let s = Seq.create len limb_zero in
  let s = Seq.upd s 0 s0 in
  let s = Seq.upd s 1 s1 in
  let s = Seq.upd s 2 s2 in
  let s = Seq.upd s 3 s3 in
  let s = Seq.upd s 4 s4 in
  s


val fexpand_spec: input:uint8_s{Seq.length input = 32} -> GTot (s:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 s /\ Hacl.Spec.EC.AddAndDouble.(bounds s p51 p51 p51 p51 p51) /\ Hacl.Spec.Bignum.Bigint.seval s = hlittle_endian input % pow2 255})
let fexpand_spec input =
  let i0 = load64_le_spec (Seq.slice input 0 8) in
  let i1 = load64_le_spec (Seq.slice input 6 14) in
  let i2 = load64_le_spec (Seq.slice input 12 20) in
  let i3 = load64_le_spec (Seq.slice input 19 27) in
  let i4 = load64_le_spec (Seq.slice input 24 32) in
  let output0 = (i0         ) &^ mask_51 in
  let output1 = (i1 >>^ 3ul ) &^ mask_51 in
  let output2 = (i2 >>^ 6ul ) &^ mask_51 in
  let output3 = (i3 >>^ 1ul ) &^ mask_51 in
  let output4 = (i4 >>^ 12ul) &^ mask_51 in
  UInt.logand_mask (v i0) 51;
  UInt.logand_mask (v (i1 >>^ 3ul)) 51;
  UInt.logand_mask (v (i2 >>^ 6ul)) 51;
  UInt.logand_mask (v (i3 >>^ 1ul)) 51;
  UInt.logand_mask (v (i4 >>^ 12ul)) 51;
  let s = seq_upd_5 output0 output1 output2 output3 output4 in
  Hacl.Spec.EC.Format.Lemmas.lemma_fexpand (reveal_sbytes input);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  s


inline_for_extraction let nineteen : p:t{v p = 19} = assert_norm(pow2 64 > 19); uint64_to_limb 19uL

let p51 = Hacl.Spec.EC.AddAndDouble.p51
let p13 = Hacl.Spec.EC.AddAndDouble.p13

open FStar.Mul

private val lemma_carry_local: x:nat -> y:nat -> n:nat -> Lemma
  (pow2 n * x + pow2 (n+51) * y = pow2 n * (x % (pow2 51)) + pow2 (n+51) * ((x / pow2 51) + y))
private let lemma_carry_local x y n =
  Math.Lemmas.lemma_div_mod x (pow2 51);
  Math.Lemmas.pow2_plus n 51;
  Math.Lemmas.distributivity_add_right (pow2 n) (pow2 51 * (x / pow2 51)) (x % pow2 51);
  Math.Lemmas.distributivity_add_right (pow2 (n + 51)) (x / pow2 51) y


val fcontract_first_carry_pass: input:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 input} ->
  GTot (s':seqelem{Hacl.Spec.EC.AddAndDouble.bounds s' p51 p51 p51 p51 (pow2 64)
    /\ Hacl.Spec.Bignum.Bigint.seval s' = Hacl.Spec.Bignum.Bigint.seval input})
let fcontract_first_carry_pass s =
  assert_norm(pow2 51 + pow2 13 = 0x8000000002000);
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  let t1' = t1 +^ (t0 >>^ 51ul) in
  let t0' = t0 &^ mask_51 in
  UInt.logand_mask (v t0) 51;
  lemma_carry_local (v t0) (v t1) 0;
  cut (v t0' + pow2 51 * v t1' + pow2 102 * v t2 + pow2 153 * v t3 + pow2 204 * v t4 = Hacl.Spec.Bignum.Bigint.seval s);
  let t2' = t2 +^ (t1' >>^ 51ul) in
  let t1'' = t1' &^ mask_51 in
  UInt.logand_mask (v t1') 51;
  lemma_carry_local (v t1') (v t2) 51;
  cut (v t0' + pow2 51 * v t1'' + pow2 102 * v t2' + pow2 153 * v t3 + pow2 204 * v t4
       = v t0' + pow2 51 * v t1' + pow2 102 * v t2 + pow2 153 * v t3 + pow2 204 * v t4);
  let t3' = t3 +^ (t2' >>^ 51ul) in
  let t2'' = t2' &^ mask_51 in
  UInt.logand_mask (v t2') 51;
  lemma_carry_local (v t2') (v t3) 102;
  cut (v t0' + pow2 51 * v t1'' + pow2 102 * v t2'' + pow2 153 * v t3' + pow2 204 * v t4
       = v t0' + pow2 51 * v t1'' + pow2 102 * v t2' + pow2 153 * v t3 + pow2 204 * v t4);
  let t4' = t4 +^ (t3' >>^ 51ul) in
  let t3'' = t3' &^ mask_51 in
  UInt.logand_mask (v t3') 51;
  lemma_carry_local (v t3') (v t4) 153;
  cut (v t0' + pow2 51 * v t1'' + pow2 102 * v t2'' + pow2 153 * v t3' + pow2 204 * v t4
       = v t0' + pow2 51 * v t1'' + pow2 102 * v t2'' + pow2 153 * v t3'' + pow2 204 * v t4');
  let s' = seq_upd_5 t0' t1'' t2'' t3'' t4' in
  (* assert_norm(pow2 64 / pow2 51 < pow2 13); *)
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s';
  s'


val fcontract_first_carry_full: input:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 input} ->
  GTot (s':seqelem{Hacl.Spec.EC.AddAndDouble.bounds s' (pow2 52) p51 p51 p51 p51
    /\ Hacl.Spec.Bignum.selem s' = Hacl.Spec.Bignum.selem input})
let fcontract_first_carry_full s =
  let s' = fcontract_first_carry_pass s in
  assert_norm(19 * (pow2 64 / pow2 51) + pow2 51 < pow2 52);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ s';
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec s';
  let s'' = Hacl.Spec.Bignum.Modulo.carry_top_spec s' in
  s''

private let lemma_div_51 (a:nat{a <= pow2 51}) : Lemma (a / pow2 51 = 1 ==> (a = pow2 51 /\ a % pow2 51 = 0)) = assert_norm((pow2 51 - 1) / pow2 51 = 0); assert_norm(pow2 51 % pow2 51 = 0)

val fcontract_second_carry_pass: input:seqelem{Hacl.Spec.EC.AddAndDouble.bounds input (pow2 52) p51 p51 p51 p51} ->
  GTot (s':seqelem{Hacl.Spec.EC.AddAndDouble.bounds s' p51 p51 p51 p51 (p51 + 1)
    /\ (v (Seq.index s' 4) = p51 ==> v (Seq.index s' 1) < 2)
    /\ Hacl.Spec.Bignum.Bigint.seval s' = Hacl.Spec.Bignum.Bigint.seval input})
let fcontract_second_carry_pass s =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  let t1' = t1 +^ (t0 >>^ 51ul) in
  assert_norm((pow2 52 - 1) / pow2 51 = 1);
  lemma_div_51 (v t1');
  let t0' = t0 &^ mask_51 in
  UInt.logand_mask (v t0) 51;
  lemma_carry_local (v t0) (v t1) 0;
  cut (v t0' + pow2 51 * v t1' + pow2 102 * v t2 + pow2 153 * v t3 + pow2 204 * v t4 = Hacl.Spec.Bignum.Bigint.seval s);
  let t2' = t2 +^ (t1' >>^ 51ul) in
  lemma_div_51 (v t2');
  let t1'' = t1' &^ mask_51 in
  UInt.logand_mask (v t1') 51;
  lemma_carry_local (v t1') (v t2) 51;
  cut (v t0' + pow2 51 * v t1'' + pow2 102 * v t2' + pow2 153 * v t3 + pow2 204 * v t4
       = v t0' + pow2 51 * v t1' + pow2 102 * v t2 + pow2 153 * v t3 + pow2 204 * v t4);
  let t3' = t3 +^ (t2' >>^ 51ul) in
  lemma_div_51 (v t3');
  let t2'' = t2' &^ mask_51 in
  UInt.logand_mask (v t2') 51;
  lemma_carry_local (v t2') (v t3) 102;
  cut (v t0' + pow2 51 * v t1'' + pow2 102 * v t2'' + pow2 153 * v t3' + pow2 204 * v t4
       = v t0' + pow2 51 * v t1'' + pow2 102 * v t2' + pow2 153 * v t3 + pow2 204 * v t4);
  let t4' = t4 +^ (t3' >>^ 51ul) in
  lemma_div_51 (v t4');
  let t3'' = t3' &^ mask_51 in
  UInt.logand_mask (v t3') 51;
  lemma_carry_local (v t3') (v t4) 153;
  cut (v t0' + pow2 51 * v t1'' + pow2 102 * v t2'' + pow2 153 * v t3' + pow2 204 * v t4
       = v t0' + pow2 51 * v t1'' + pow2 102 * v t2'' + pow2 153 * v t3'' + pow2 204 * v t4');
  let s' = seq_upd_5 t0' t1'' t2'' t3'' t4' in
  (* assert_norm(pow2 64 / pow2 51 < pow2 13); *)
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s';
  s'


val fcontract_second_carry_full: input:seqelem{Hacl.Spec.EC.AddAndDouble.bounds input (pow2 52) p51 p51 p51 p51} ->
  GTot (s':seqelem{Hacl.Spec.EC.AddAndDouble.bounds s' p51 p51 p51 p51 p51
    /\ Hacl.Spec.Bignum.selem s' = Hacl.Spec.Bignum.selem input})
let fcontract_second_carry_full input =
  let s' = fcontract_second_carry_pass input in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ s';
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec s';
  let s'' = Hacl.Spec.Bignum.Modulo.carry_top_spec s' in
  Hacl.Spec.Bignum.Fproduct.carry_0_to_1_spec s''

inline_for_extraction
let p51m19 : p:limb{v p = pow2 51 - 19} =
  assert_norm(pow2 51 - 19 = 0x7ffffffffffed);
  uint64_to_sint64 0x7ffffffffffeduL
inline_for_extraction
let p51m1 : p:limb{v p = pow2 51 - 1} =
  assert_norm(pow2 51 - 1 = 0x7ffffffffffff);
  uint64_to_sint64 0x7ffffffffffffuL

val lemma_fcontract_trim_1: s:seqelem -> Lemma
  (requires (Hacl.Spec.EC.AddAndDouble.bounds s p51 p51 p51 p51 p51 /\
    (let a0' = Seq.index s 0 in let a1' = Seq.index s 1 in let a2' = Seq.index s 2 in
     let a3' = Seq.index s 3 in let a4' = Seq.index s 4 in
     (v a0' <= 18 /\ v a1' = 0 /\ v a2' = 0 /\ v a3' = 0 /\ v a4' = 0) \/ (v a0' < pow2 51 - 19 \/ v a1' < pow2 51 - 1 \/ v a2' < pow2 51 - 1 \/ v a3' < pow2 51 - 1 \/ v a4' < pow2 51 - 1) )))
  (ensures (Hacl.Spec.Bignum.Bigint.seval s = Hacl.Spec.Bignum.selem s))
let lemma_fcontract_trim_1 s =
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 102 = 0x40000000000000000000000000);
  assert_norm(pow2 153 = 0x200000000000000000000000000000000000000);
  assert_norm(pow2 204 = 0x1000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 51 - 19 + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1) 
    + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1) = pow2 255 - 19);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval s) (pow2 255 - 19)


val lemma_fcontract_trim_2: a0:limb -> a1:limb -> a2:limb -> a3:limb -> a4:limb -> Lemma
  (let open Hacl.Bignum.Limb in
    (v a0 >= pow2 51 - 19 /\ v a1 = pow2 51 - 1 /\ v a2 = pow2 51 - 1 /\ v a3 = pow2 51 - 1 /\ v a4 = pow2 51 - 1) ==>
    ((v a0 - (pow2 51 - 19) + pow2 51 * (v a1 - (pow2 51 - 1)) + pow2 102 * (v a2 - (pow2 51 - 1)) + pow2 153 * (v a3 - (pow2 51 - 1)) + pow2 204 * (v a4 - (pow2 51 - 1))) % prime
    = (v a0 + pow2 51 * (v a1) + pow2 102 * (v a2) + pow2 153 * v a3 + pow2 204 * v a4) % prime))
let lemma_fcontract_trim_2 a0 a1 a2 a3 a4 =
  if (v a0 >= pow2 51 - 19 && v a1 = pow2 51 - 1 && v a2 = pow2 51 - 1 && v a3 = pow2 51 - 1 && v a4 = pow2 51 - 1)
  then (
    assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed);
    assert_norm(pow2 51 = 0x8000000000000);
    assert_norm(pow2 102 = 0x40000000000000000000000000);
    assert_norm(pow2 153 = 0x200000000000000000000000000000000000000);
    assert_norm(pow2 204 = 0x1000000000000000000000000000000000000000000000000000);
    Math.Lemmas.distributivity_add_right (pow2 51) (v a1) (pow2 51 - 1);
    Math.Lemmas.distributivity_add_right (pow2 102) (v a2) (pow2 51 - 1);
    Math.Lemmas.distributivity_add_right (pow2 153) (v a3) (pow2 51 - 1);
    Math.Lemmas.distributivity_add_right (pow2 204) (v a4) (pow2 51 - 1);
    assert_norm(pow2 51 - 19 + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1) 
      + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1) = pow2 255 - 19);
    Math.Lemmas.lemma_mod_plus (v a0 + pow2 51 * (v a1) + pow2 102 * (v a2) + pow2 153 * v a3 + pow2 204 * v a4) 1 prime
  )


val fcontract_trim: s:seqelem{Hacl.Spec.EC.AddAndDouble.bounds s p51 p51 p51 p51 p51} ->
  GTot (s':seqelem{Hacl.Spec.EC.AddAndDouble.bounds s' p51 p51 p51 p51 p51
    /\  Hacl.Spec.Bignum.Bigint.seval s' = Hacl.Spec.Bignum.selem s})
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
let fcontract_trim s =
  let a0 = Seq.index s 0 in
  let a1 = Seq.index s 1 in
  let a2 = Seq.index s 2 in
  let a3 = Seq.index s 3 in
  let a4 = Seq.index s 4 in
  let open Hacl.Bignum.Limb in
  let mask0 = gte_mask a0 p51m19 in
  let mask1 = eq_mask a1 p51m1 in
  let mask2 = eq_mask a2 p51m1 in
  let mask3 = eq_mask a3 p51m1 in
  let mask4 = eq_mask a4 p51m1 in
  let mask  = mask0 &^ mask1 &^ mask2 &^ mask3 &^ mask4 in
  UInt.logand_lemma_1 (v mask0); UInt.logand_lemma_1 (v mask1); UInt.logand_lemma_1 (v mask2);
  UInt.logand_lemma_1 (v mask3); UInt.logand_lemma_1 (v mask4);
  UInt.logand_lemma_2 (v mask0); UInt.logand_lemma_2 (v mask1); UInt.logand_lemma_2 (v mask2);
  UInt.logand_lemma_2 (v mask3); UInt.logand_lemma_2 (v mask4);
  cut (v mask = UInt.ones 64 \/ v mask = UInt.zero 64);
  cut (v mask = UInt.ones 64 ==> (v a0 >= pow2 51 - 19 /\ v a1 = pow2 51 - 1 /\ v a2 = pow2 51 - 1
    /\ v a3 = pow2 51 - 1 /\ v a4 = pow2 51 - 1));
  cut (v mask = UInt.zero 64 ==> (v a0 < pow2 51 - 19 \/ v a1 < pow2 51 - 1 \/ v a2 < pow2 51 - 1
    \/ v a3 < pow2 51 - 1 \/ v a4 < pow2 51 - 1));
  UInt.logand_lemma_1 (v p51m19); UInt.logand_lemma_1 (v p51m1);
  UInt.logand_lemma_2 (v p51m19); UInt.logand_lemma_2 (v p51m1);
  let a0' = a0 -^ (p51m19 &^ mask) in
  let a1' = a1 -^ (p51m1 &^ mask) in
  let a2' = a2 -^ (p51m1 &^ mask) in
  let a3' = a3 -^ (p51m1 &^ mask) in
  let a4' = a4 -^ (p51m1 &^ mask) in
  cut ( (v a0 >= pow2 51 - 19 /\ v a1 = pow2 51 - 1 /\ v a2 = pow2 51 - 1 /\ v a3 = pow2 51 - 1 /\ v a4 = pow2 51 - 1) ==> (v a0' <= 18 /\ v a1' = 0 /\ v a2' = 0 /\ v a3' = 0 /\ v a4' = 0) );
  cut ( (v a0 < pow2 51 - 19 \/ v a1 < pow2 51 - 1 \/ v a2 < pow2 51 - 1 \/ v a3 < pow2 51 - 1 \/ v a4 < pow2 51 - 1) ==> (v a0' = v a0 /\ v a1' = v a1 /\ v a2' = v a2 /\ v a3' = v a3 /\ v a4' = v a4) );
  let s' = seq_upd_5 a0' a1' a2' a3' a4' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s';
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  cut (Hacl.Spec.EC.AddAndDouble.bounds s' p51 p51 p51 p51 p51);
  cut ((v a0' <= 18 /\ v a1' = 0 /\ v a2' = 0 /\ v a3' = 0 /\ v a4' = 0) \/ (v a0' < pow2 51 - 19 \/ v a1' < pow2 51 - 1 \/ v a2' < pow2 51 - 1 \/ v a3' < pow2 51 - 1 \/ v a4' < pow2 51 - 1));
  lemma_fcontract_trim_1 s';
  lemma_fcontract_trim_2 a0 a1 a2 a3 a4;
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval s') prime;
  s'


val fcontract_store_lemma: x:limb{v x < pow2 51} -> a:UInt32.t{UInt32.v a <= 51} -> b:UInt32.t{UInt32.v b <= 51} ->
  Lemma (v (x <<^ a) % pow2 (UInt32.v a) = 0 /\ v (x >>^ b) < pow2 (51 - UInt32.v b))
let fcontract_store_lemma x a b =
  Math.Lemmas.lemma_div_lt (v x) 51 (UInt32.v b);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v x) 64 (UInt32.v a);
  let a' = UInt32.v a in
  cut (v (x <<^ a) = (v x * pow2 a') % pow2 64);
  cut ((v x * pow2 a') % pow2 64 = (v x % pow2 (64 - a')) * pow2 a');
  Math.Lemmas.multiple_modulo_lemma (v x % pow2 (64 - a')) (pow2 a')
  

val fcontract_store: s:seqelem{Hacl.Spec.EC.AddAndDouble.bounds s p51 p51 p51 p51 p51} ->
  GTot (s':uint8_s{Seq.length s' = 32 /\ hlittle_endian s' = Hacl.Spec.Bignum.Bigint.seval s})
let fcontract_store s =
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  let o0 = (t1 <<^ 51ul) |^ t0 in
  let o1 = (t2 <<^ 38ul) |^ (t1 >>^ 13ul) in
  let o2 = (t3 <<^ 25ul) |^ (t2 >>^ 26ul) in
  let o3 = (t4 <<^ 12ul) |^ (t3 >>^ 39ul) in
  fcontract_store_lemma t0 0ul 0ul;
  fcontract_store_lemma t1 51ul 13ul;
  fcontract_store_lemma t2 38ul 26ul;
  fcontract_store_lemma t3 25ul 39ul;
  fcontract_store_lemma t4 12ul 0ul;
  UInt.logor_disjoint (v (t1 <<^ 51ul)) (v t0) 51;
  UInt.logor_disjoint (v (t2 <<^ 38ul)) (v (t1 >>^ 13ul)) 38;
  UInt.logor_disjoint (v (t3 <<^ 25ul)) (v (t2 >>^ 26ul)) 25;
  UInt.logor_disjoint (v (t4 <<^ 12ul)) (v (t3 >>^ 39ul)) 12;
  Hacl.Spec.EC.Format.Lemmas.lemma_fcontract (v t0) (v t1) (v t2) (v t3) (v t4);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  FStar.Seq.(store64_le_spec o0 @| store64_le_spec o1 @| store64_le_spec o2 @| store64_le_spec o3)


val fcontract_spec: input:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 input} ->
  GTot (s:uint8_s{Seq.length s = 32 /\ hlittle_endian s = Hacl.Spec.Bignum.selem input})
let fcontract_spec input =
  let s = fcontract_first_carry_full input in
  let s' = fcontract_second_carry_full s in
  let s'' = fcontract_trim s' in
  fcontract_store s''


val point_of_scalar: scalar:uint8_s{Seq.length scalar = keylen} ->
  GTot (p:spoint_513{Hacl.Spec.Bignum.Bigint.seval (fst p) = hlittle_endian scalar % pow2 255
    /\ Hacl.Spec.Bignum.selem (snd p) = 1})
let point_of_scalar scalar =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  let x = fexpand_spec scalar in
  let z = Seq.upd z 0 limb_one in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 z;
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval z) (pow2 255 - 19);
  x, z


val scalar_of_point: p:spoint_513 -> GTot (scalar:uint8_s{Seq.length scalar = keylen
  /\ (let x = Hacl.Spec.Bignum.selem (fst p) in
     let z = Hacl.Spec.Bignum.selem (snd p) in
     (* pow2 255 - 21 > 0 /\ *)
     reveal_sbytes scalar == Spec.Curve25519.(encodePoint (Proj x z)))
     (* little_endian scalar = Spec.Curve25519.(x *@ (z ** (pow2 255 - 21)))) *)
  })
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let scalar_of_point point =
  assert_norm(pow2 255 > 21);
  let x = sgetx point in
  let z = sgetz point in
  cut ((Spec.Curve25519.(encodePoint (Proj (Hacl.Spec.Bignum.selem x) (Hacl.Spec.Bignum.selem z)))) == little_bytes 32ul (Spec.Curve25519.(Hacl.Spec.Bignum.selem x *@ (Hacl.Spec.Bignum.selem z ** (pow2 255 - 21)))));
  let zmone = Hacl.Spec.Bignum.Crecip.crecip_tot z in
  Hacl.Spec.EC.AddAndDouble2.lemma_513_is_53 x;
  Hacl.Spec.EC.AddAndDouble2.lemma_513_is_55 zmone;
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine x zmone;
  let y = Hacl.Spec.Bignum.fmul_tot x zmone in
  let r = fcontract_spec y in
  cut (hlittle_endian r = Spec.Curve25519.(Hacl.Spec.Bignum.selem x *@ (Hacl.Spec.Bignum.selem z ** (pow2 255 - 21))));
  lemma_little_endian_inj (reveal_sbytes r) (Spec.Curve25519.(encodePoint (Proj (Hacl.Spec.Bignum.selem x) (Hacl.Spec.Bignum.selem z))));
  r



val format_secret: secret:uint8_s{Seq.length secret = keylen} -> Tot (s:uint8_s{Seq.length s = keylen /\ reveal_sbytes s == Spec.Curve25519.decodeScalar25519 (reveal_sbytes secret)})
let format_secret secret =
  assert_norm(pow2 8 = 256);
  let e0  = Seq.index secret 0 in
  let e31 = Seq.index secret 31 in
  let open Hacl.UInt8 in
  let e0  = e0 &^ (uint8_to_sint8 248uy) in
  let e31 = e31 &^ (uint8_to_sint8 127uy) in
  let e31 = e31 |^ (uint8_to_sint8 64uy) in
  let e = Seq.upd secret 0 e0 in
  let e = Seq.upd e 31 e31 in
  e
