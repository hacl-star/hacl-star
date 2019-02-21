module Hacl.Bignum25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul

#reset-options "--max_fuel 0 --z3rlimit 100"

private let lemma_distributivity_5 x a b c d e : Lemma (x * (a + b + c + d + e) = x * a + x * b + x * c + x * d + x * e) = ()

private let lemma_times_2 a b c d e : Lemma
  (2 * a + pow2 51 * (2 * b) + pow2 102 * (2 * c) + pow2 153 * (2 * d) + pow2 204 * (2 * e)
   = 2 * (a + pow2 51 * (b) + pow2 102 * (c) + pow2 153 * (d) + pow2 204 * (e)))
  = lemma_distributivity_5 2 a (pow2 51 * b) (pow2 102 * c) (pow2 153 * d) (pow2 204 * e)

let red_51 s = Hacl.Spec.EC.AddAndDouble.(bounds s p51 p51 p51 p51 p51)
let red_513 s = Hacl.Spec.EC.AddAndDouble.red_513 s
let red_53 s = Hacl.Spec.EC.AddAndDouble.red_53 s
let red_5413 s = Hacl.Spec.EC.AddAndDouble.red_5413 s
let red_55 s = Hacl.Spec.EC.AddAndDouble.red_55 s

let lemma_red_51_is_red_513 s = ()
let lemma_red_51_is_red_53 s = ()
let lemma_red_51_is_red_5413 s = ()
let lemma_red_51_is_red_55 s = ()
let lemma_red_513_is_red_53 s = ()
let lemma_red_513_is_red_5413 s = ()
let lemma_red_513_is_red_55 s = ()
let lemma_red_53_is_red_5413 s = ()
let lemma_red_53_is_red_55 s = ()
let lemma_red_5413_is_red_55 s = ()

let seval s = Hacl.Spec.Bignum.Bigint.seval s % Spec.Curve25519.prime

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let fsum a b =
  let h = ST.get() in
  assert_norm (pow2 63 > Hacl.Spec.EC.AddAndDouble.p513);
  assert(Hacl.Spec.Bignum.Fsum.red (as_seq h a) 5);
  assert(Hacl.Spec.Bignum.Fsum.red (as_seq h b) 5);
  Hacl.Bignum.fsum a b;
  Hacl.Spec.Bignum.Fsum.lemma_fsum_eval (as_seq h a) (as_seq h b);
  Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h a) (as_seq h b)

inline_for_extraction
let fdifference a b =
  let h = ST.get() in
  assert_norm (pow2 63 > Hacl.Spec.EC.AddAndDouble.p513);
  Hacl.Bignum.fdifference a b


open Hacl.Spec.EC.AddAndDouble

inline_for_extraction
let mask_51 : p:Hacl.UInt64.t{Hacl.UInt64.v p = pow2 51 - 1} = assert_norm(pow2 51 - 1 = 0x7ffffffffffff);
  Hacl.Cast.uint64_to_sint64 0x7ffffffffffffuL

inline_for_extraction
private val lemma_carry_local: x:nat -> y:nat -> n:nat -> Lemma
  (pow2 n * x + pow2 (n+51) * y = pow2 n * (x % (pow2 51)) + pow2 (n+51) * ((x / pow2 51) + y))
let lemma_carry_local x y n =
  Math.Lemmas.lemma_div_mod x (pow2 51);
  Math.Lemmas.pow2_plus n 51;
  Math.Lemmas.distributivity_add_right (pow2 n) (pow2 51 * (x / pow2 51)) (x % pow2 51);
  Math.Lemmas.distributivity_add_right (pow2 (n + 51)) (x / pow2 51) y

inline_for_extraction
private
val fcontract_first_carry_pass_s: input:Hacl.Bignum.Parameters.seqelem{red_5413 input} ->
  GTot (s':Hacl.Bignum.Parameters.seqelem{
    bounds s' p51 p51 p51 p51 (pow2 64)
    /\ Hacl.Spec.Bignum.Bigint.seval s' = Hacl.Spec.Bignum.Bigint.seval input})
let fcontract_first_carry_pass_s s =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  let open Hacl.UInt64 in
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
  let s' = Seq.Create.create_5 t0' t1'' t2'' t3'' t4' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s';
  s'

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private val fcontract_first_carry_pass:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h input)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h0 input)
      /\ Buffer.live h1 input /\ modifies_1 input h0 h1
      /\ as_seq h1 input == fcontract_first_carry_pass_s (as_seq h0 input) ))
let fcontract_first_carry_pass input =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let open Hacl.UInt64 in
  let t1' = t1 +^ (t0 >>^ 51ul) in
  let t0' = t0 &^ Hacl.Spec.EC.Format.mask_51 in
  let t2' = t2 +^ (t1' >>^ 51ul) in
  let t1'' = t1' &^ Hacl.Spec.EC.Format.mask_51 in
  let t3' = t3 +^ (t2' >>^ 51ul) in
  let t2'' = t2' &^ Hacl.Spec.EC.Format.mask_51 in
  let t4' = t4 +^ (t3' >>^ 51ul) in
  let t3'' = t3' &^ Hacl.Spec.EC.Format.mask_51 in
  Hacl.Lib.Create64.make_h64_5 input t0' t1'' t2'' t3'' t4'


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private
val reduce_513_s: input:Hacl.Bignum.Parameters.seqelem{red_5413 input} ->
  GTot (s':Hacl.Bignum.Parameters.seqelem{red_513 s' /\ seval s' = seval input})
let reduce_513_s input =
  let s' = fcontract_first_carry_pass_s input in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ s';
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec s';
  assert_norm(19 * (pow2 64 / pow2 51) + pow2 51 < pow2 52);
  assert_norm(pow2 52 = 0x10000000000000);
  let s'' = Hacl.Spec.Bignum.Modulo.carry_top_spec s' in
  Hacl.Spec.Bignum.Fproduct.carry_0_to_1_spec s''


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
val reduce_513_:
  a:felem ->
  Stack unit
    (requires (fun h -> live h a /\ red_5413 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 a /\ red_5413 (as_seq h0 a)
      /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == reduce_513_s (as_seq h0 a)))
#reset-options "--max_fuel 0 --z3rlimit 500"
let reduce_513_ a =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 63 = 0x8000000000000000);
  fcontract_first_carry_pass a;
  assert_norm(19 * (pow2 64 / pow2 51) + pow2 51 < pow2 63);
  let h = ST.get() in
  Hacl.Bignum.Modulo.carry_top a;
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ (as_seq h a);
  Hacl.Bignum.Fproduct.carry_0_to_1 a

inline_for_extraction
let reduce_513 a =
  reduce_513_ a

inline_for_extraction
let fdifference_reduced a b =
  fdifference a b;
  reduce_513 a

inline_for_extraction
let fmul out a b =
  let h = ST.get() in
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h a) (as_seq h b);
  Hacl.Bignum.fmul out a b

#reset-options "--max_fuel 0 --z3rlimit 232"

open Hacl.Cast

inline_for_extraction
let times_2 out a =
  let h = ST.get() in
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let open Hacl.UInt64 in
  let o0 = uint64_to_sint64 2uL *^ a0 in
  let o1 = uint64_to_sint64 2uL *^ a1 in
  let o2 = uint64_to_sint64 2uL *^ a2 in
  let o3 = uint64_to_sint64 2uL *^ a3 in
  let o4 = uint64_to_sint64 2uL *^ a4 in
  lemma_times_2 (v a0) (v a1) (v a2) (v a3) (v a4);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h a);
  Hacl.Lib.Create64.make_h64_5 out o0 o1 o2 o3 o4;
  let h' = ST.get() in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h' out)

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let times_d out a =
  assert_norm(pow2 51 = 0x8000000000000);
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let d = Buffer.create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let h1' = ST.get() in
  Hacl.Lib.Create64.make_h64_5 d (uint64_to_sint64 0x00034dca135978a3uL)
                                 (uint64_to_sint64 0x0001a8283b156ebduL)
                                 (uint64_to_sint64 0x0005e7a26001c029uL)
                                 (uint64_to_sint64 0x000739c663a03cbbuL)
                                 (uint64_to_sint64 0x00052036cee2b6ffuL);
  let h2 = ST.get() in
  lemma_modifies_0_1' d h1 h1' h2;
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h2 d);
  assert_norm (0x00034dca135978a3 + pow2 51 * 0x0001a8283b156ebd + pow2 102 * 0x0005e7a26001c029 +
               pow2 153 * 0x000739c663a03cbb + pow2 204 * 0x00052036cee2b6ff
               = Spec.Ed25519.d);
  fmul out d a;
  let h3 = ST.get() in
  lemma_modifies_0_1 out h1 h2 h3;
  pop_frame();
  let h4 = ST.get() in
  modifies_popped_1 out h0 h1 h3 h4


#reset-options "--max_fuel 0 --z3rlimit 100"
inline_for_extraction
let times_2d out a =
  assert_norm(pow2 51 = 0x8000000000000);
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let d2 = Buffer.create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let h1' = ST.get() in
  Hacl.Lib.Create64.make_h64_5 d2 (uint64_to_sint64 0x00069b9426b2f159uL)
                                  (uint64_to_sint64 0x00035050762add7auL)
                                  (uint64_to_sint64 0x0003cf44c0038052uL)
                                  (uint64_to_sint64 0x0006738cc7407977uL)
                                  (uint64_to_sint64 0x0002406d9dc56dffuL);
  let h2 = ST.get() in
  lemma_modifies_0_1' d2 h1 h1' h2;
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h2 d2);
  assert_norm (0x00069b9426b2f159 + pow2 51 * 0x00035050762add7a + pow2 102 * 0x0003cf44c0038052 +
               pow2 153 * 0x0006738cc7407977 + pow2 204 * 0x0002406d9dc56dff
               = (2 * Spec.Ed25519.d) % Spec.Curve25519.prime);
  fmul out a d2;
  let h3 = ST.get() in
  lemma_modifies_0_1 out h1 h2 h3;
  pop_frame();
  let h4 = ST.get() in
  modifies_popped_1 out h0 h1 h3 h4

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let fsquare out a =
  let h = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint128 0uL) 5ul in
  let h1 = ST.get() in
  blit a 0ul out 0ul 5ul;
  let h2 = ST.get() in
  lemma_modifies_0_1 out h0 h1 h2;
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 a);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h2 out);
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h2 out);
  Hacl.Bignum.Fsquare.fsquare_ tmp out;
  let h3 = ST.get() in
  pop_frame();
  let h4 = ST.get() in
  lemma_modifies_1_2'' out tmp h1 h2 h3;
  lemma_modifies_0_2 out tmp h0 h1 h3;
  modifies_popped_1 out h h0 h3 h4


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let fsquare_times out a n =
  let h = ST.get() in
  Hacl.Spec.Bignum.Crecip.lemma_fsquare_times_tot (as_seq h a) (FStar.UInt32.v n);
  Hacl.Spec.Bignum.Crecip.Lemmas.lemma_exp_eq (seval (as_seq h a)) (pow2 (FStar.UInt32.v n));
  Hacl.Bignum.Fsquare.fsquare_times out a n

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let fsquare_times_inplace out n =
  let h = ST.get() in
  Hacl.Spec.Bignum.Crecip.lemma_fsquare_times_tot (as_seq h out) (FStar.UInt32.v n);
  Hacl.Spec.Bignum.Crecip.Lemmas.lemma_exp_eq (seval (as_seq h out)) (pow2 (FStar.UInt32.v n));
  Hacl.Bignum.Fsquare.fsquare_times_inplace out n

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let inverse out a =
  Hacl.Bignum.Crecip.crecip out a

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let reduce out =
  Hacl.EC.Format.reduce out;
  let h = ST.get() in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h out)

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let lemma_reveal_red_51 s =
  assert_norm(pow2 51 = 0x8000000000000)

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let lemma_intro_red_51 s =
  assert_norm (pow2 51 = 0x8000000000000)

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let lemma_reveal_red_513 s =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 13 = 0x2000)

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let lemma_intro_red_513 s =
  assert_norm (pow2 51 = 0x8000000000000);
  assert_norm(pow2 13 = 0x2000)

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let lemma_reveal_seval s =
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s
