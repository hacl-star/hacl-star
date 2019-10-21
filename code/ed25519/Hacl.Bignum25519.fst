module Hacl.Bignum25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer

module S51 = Hacl.Spec.Curve25519.Field51.Definition

module SL51 = Hacl.Spec.Curve25519.Field51.Lemmas

module BN = Hacl.Impl.Curve25519.Field51
module SC = Spec.Curve25519

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let mask_51 = u64 0x7ffffffffffff

let make_u64_5 b s0 s1 s2 s3 s4 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4

let make_u64_10 b s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4;
  b.(5ul) <- s5;
  b.(6ul) <- s6;
  b.(7ul) <- s7;
  b.(8ul) <- s8;
  b.(9ul) <- s9

let make_u128_9 b s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4;
  b.(5ul) <- s5;
  b.(6ul) <- s6;
  b.(7ul) <- s7;
  b.(8ul) <- s8

let make_zero b =
  b.(0ul) <- u64 0;
  b.(1ul) <- u64 0;
  b.(2ul) <- u64 0;
  b.(3ul) <- u64 0;
  b.(4ul) <- u64 0;
  assert_norm (S51.as_nat5 (u64 0, u64 0, u64 0, u64 0, u64 0) % Spec.Curve25519.prime == 0)

let make_one b =
  b.(0ul) <- u64 1;
  b.(1ul) <- u64 0;
  b.(2ul) <- u64 0;
  b.(3ul) <- u64 0;
  b.(4ul) <- u64 0;
  assert_norm (S51.as_nat5 (u64 1, u64 0, u64 0, u64 0, u64 0) % Spec.Curve25519.prime == 1)

let fsum a b =
  BN.fadd a a b

let fdifference a b =
  BN.fsub a b a

#push-options "--z3cliopt smt.arith.nl=false"

private val lemma_carry_local: x:int -> y:int -> n:nat -> Lemma
  (pow2 n * x + pow2 (n+51) * y = pow2 n * (x % (pow2 51)) + pow2 (n+51) * ((x / pow2 51) + y))
private let lemma_carry_local x y n =
  calc (==) {
    pow2 n * x + pow2 (n + 51) * y;
    (==) {  Math.Lemmas.lemma_div_mod x (pow2 51) }
    pow2 n * (pow2 51 * (x / pow2 51) + x % pow2 51) + pow2 (n + 51) * y;
    (==) { Math.Lemmas.distributivity_add_right (pow2 n) (pow2 51 * (x / pow2 51)) (x % pow2 51) }
    pow2 n * (pow2 51 * (x / pow2 51)) + pow2 n * (x % pow2 51) + pow2 (n + 51) * y;
    (==) { Math.Lemmas.paren_mul_right (pow2 n) (pow2 51) (x / pow2 51);
           Math.Lemmas.paren_mul_left (pow2 n) (pow2 51) (x / pow2 51);
           Math.Lemmas.pow2_plus n 51 }
    pow2 (n + 51) * (x / pow2 51) + pow2 n * (x % pow2 51) + pow2 (n + 51) * y;
    (==) { Math.Lemmas.distributivity_add_right (pow2 (n + 51)) (x / pow2 51) y }
    pow2 (n + 51) * (x / pow2 51 + y) + pow2 n * (x % pow2 51);
  }

#pop-options

let lemma_change_as_nat_repr (v0 v1 v2 v3 v4:nat) : Lemma
  (v0 + pow2 51 * v1 + pow2 102 * v2 + pow2 153 * v3 + pow2 204 * v4 ==
  v0 + v1 * pow2 51 + v2 * pow2 51 * pow2 51 + v3 * pow2 51 * pow2 51 * pow2 51 + v4 * pow2 51 * pow2 51 * pow2 51 * pow2 51)
  =
  calc (==) {
    v2 * pow2 51 * pow2 51;
    (==) { FStar.Math.Lemmas.paren_mul_right v2 (pow2 51) (pow2 51); assert_norm (pow2 51 * pow2 51 == pow2 102) }
    pow2 102 * v2;
  };
  calc (==) {
    v3 * pow2 51 * pow2 51 * pow2 51;
    (==) { FStar.Classical.forall_intro_3 FStar.Math.Lemmas.paren_mul_right;
           assert_norm (pow2 51 * pow2 51 * pow2 51== pow2 153) }
    pow2 153 * v3;
  };
  calc (==) {
    v4 * pow2 51 * pow2 51 * pow2 51 * pow2 51 ;
    (==) { FStar.Classical.forall_intro_3 FStar.Math.Lemmas.paren_mul_right;
           assert_norm (pow2 51 * pow2 51 * pow2 51 * pow2 51 == pow2 204) }
    pow2 204 * v4;
  }

#restart-solver
#push-options "--z3rlimit 400 --z3cliopt smt.arith.nl=false"

let lemma_fcontract_first_carry_pass
  (v0 v1 v2 v3 v4 v0' v1' v2' v3' v4':nat) : Lemma
  (requires
    v0' == v0 % pow2 51 /\
    v1' == (v1 + v0 / pow2 51) % pow2 51 /\
    v2' == (v2 + (v1 + v0 / pow2 51) / pow2 51) % pow2 51 /\
    v3' == (v3 + (v2 + (v1 + v0 / pow2 51) / pow2 51) / pow2 51) % pow2 51 /\
    v4' == v4 + (v3 + (v2 + (v1 + v0 / pow2 51) / pow2 51) / pow2 51) / pow2 51)
  (ensures v0 + v1 * pow2 51 + v2 * pow2 51 * pow2 51 + v3 * pow2 51 * pow2 51 * pow2 51 + v4 * pow2 51 * pow2 51 * pow2 51 * pow2 51 ==
           v0' + v1' * pow2 51 + v2' * pow2 51 * pow2 51 + v3' * pow2 51 * pow2 51 * pow2 51 + v4' * pow2 51 * pow2 51 * pow2 51 * pow2 51)
  =
  assert_norm (pow2 0 == 1);
  calc (==) {
    v0 + v1 * pow2 51 + v2 * pow2 51 * pow2 51 + v3 * pow2 51 * pow2 51 * pow2 51 + v4 * pow2 51 * pow2 51 * pow2 51 * pow2 51;
    (==) { lemma_change_as_nat_repr v0 v1 v2 v3 v4 }
    v0 + pow2 51 * v1 + pow2 102 * v2 + pow2 153 * v3 + pow2 204 * v4;
    (==) { lemma_carry_local v0 v1 0 }
    v0' + pow2 51 * ((v0 / pow2 51) + v1) + pow2 102 * v2 + pow2 153 * v3 + pow2 204 * v4;
    (==) { lemma_carry_local ((v0 / pow2 51) + v1) v2 51 }
    v0' + pow2 51 * v1' + pow2 102 * (v2 + (v1 + v0 / pow2 51) / pow2 51) + pow2 153 * v3 + pow2 204 * v4;
    (==) { lemma_carry_local (v2 + (v1 + v0 / pow2 51) / pow2 51) v3 102 }
    v0' + pow2 51 * v1' + pow2 102 * v2' + pow2 153 * (v3 + (v2 + (v1 + v0 / pow2 51) / pow2 51) / pow2 51) + pow2 204 * v4;
    (==) { lemma_carry_local (v3 + (v2 + (v1 + v0 / pow2 51) / pow2 51) / pow2 51) v4 153 }
    v0' + pow2 51 * v1' + pow2 102 * v2' + pow2 153 * v3' + pow2 204 * v4';
    (==) { lemma_change_as_nat_repr v0' v1' v2' v3' v4' }
    v0' + v1' * pow2 51 + v2' * pow2 51 * pow2 51 + v3' * pow2 51 * pow2 51 * pow2 51 + v4' * pow2 51 * pow2 51 * pow2 51 * pow2 51;
  }

#pop-options

inline_for_extraction noextract
val fcontract_first_carry_pass:
  input:felem ->
  Stack unit
    (requires fun h -> live h input /\ F51.mul_inv_t h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1 /\
      F51.as_nat h0 input == F51.as_nat h1 input /\
      (let s = as_seq h1 input in
       let op_String_Access = Seq.index in
       v s.[0] < pow2 51 /\
       v s.[1] < pow2 51 /\
       v s.[2] < pow2 51 /\
       v s.[3] < pow2 51
      )
    )

#push-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=false"

let fcontract_first_carry_pass input =
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let t2':uint64 = t2 +. (t1 >>. 51ul) in
  let t1'':uint64 = t1 &. mask_51 in
  let t3':uint64 = t3 +. (t2' >>. 51ul) in
  let t2'':uint64 = t2' &. mask_51 in
  let t4':uint64 = t4 +. (t3' >>. 51ul) in
  let t3'':uint64 = t3' &. mask_51 in
  assert_norm (v mask_51 == pow2 51 - 1);
  logand_spec t0 mask_51;
  logand_mask t0 mask_51 51;
  logand_spec t1 mask_51;
  logand_mask t1 mask_51 51;
  logand_spec t2' mask_51;
  logand_mask t2' mask_51 51;
  logand_spec t3' mask_51;
  logand_mask t3' mask_51 51;
  shift_right_lemma t0 51ul;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v t2 + v t1 / pow2 51) 51 64;
  shift_right_lemma t1 51ul;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v t3 + v t2' / pow2 51) 51 64;
  shift_right_lemma t2' 51ul;
  shift_right_lemma t3' 51ul;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v t4 + v t3' / pow2 51) 51 64;
  assert_norm (2 * S51.max51 < pow2 52);
  Math.Lemmas.lemma_div_lt_nat (v t1) 52 51;
  Math.Lemmas.small_mod (v t2 + (v t1 / pow2 51)) (pow2 64);
  assert (v t2' <= pow2 51);
  assert (v t2' == (v t2 + (v t1 / pow2 51)));
  Math.Lemmas.lemma_div_lt_nat (v t2') 52 51;
  Math.Lemmas.small_mod (v t3 + (v t2' / pow2 51)) (pow2 64);
  assert (v t3' <= pow2 51);
  assert (v t3' == (v t3 + ((v t2 + (v t1 / pow2 51)) / pow2 51)));
  Math.Lemmas.lemma_div_lt_nat (v t3') 52 51;
  Math.Lemmas.small_mod (v t4 + (v t3' / pow2 51)) (pow2 64);
  Math.Lemmas.small_div (v t0) (pow2 51);
  Math.Lemmas.small_mod (v t0) (pow2 51);
  Math.Lemmas.small_mod (v t1) (pow2 64);
  lemma_fcontract_first_carry_pass (v t0) (v t1) (v t2) (v t3) (v t4)
    (v t0) (v t1'') (v t2'') (v t3'') (v t4');
  make_u64_5 input  t0 t1'' t2'' t3'' t4'

#pop-options

let lemma_change_repr4 (v:nat) : Lemma
  (v * pow2 51 * pow2 51 * pow2 51 * pow2 51 == pow2 204 * v)
  = FStar.Classical.forall_intro_3 Math.Lemmas.paren_mul_right;
  assert_norm (pow2 51 * pow2 51 * pow2 51 * pow2 51 == pow2 204)

let lemma_small_carry_top (v0 v4:nat) : Lemma
  (requires v0 < pow2 51)
  (ensures
    (v0 + 19 * (v4 / pow2 51)) / pow2 51 <> 0 ==> v4 >= pow2 51)
   =
     Math.Lemmas.small_div v0 (pow2 51);
     Classical.move_requires (Math.Lemmas.small_div v4) (pow2 51)

inline_for_extraction noextract
val carry_top:
  b:felem ->
  Stack unit
  (requires fun h -> live h b /\
    (let s = as_seq h b in
     let op_String_Access = Seq.index in
       v s.[0] < pow2 51 /\
       v s.[1] < pow2 51 /\
       v s.[2] < pow2 51 /\
       v s.[3] < pow2 51 /\
       19 * (v s.[4] / pow2 51) + v s.[0] < pow2 64)
  )
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.fevalh h0 b == F51.fevalh h1 b /\
    F51.felem_fits h1 b (2, 1, 1, 1, 1) /\
    Seq.index (as_seq h0 b) 1 == Seq.index (as_seq h1 b) 1 /\
    ((v (Seq.index (as_seq h1 b) 0) / pow2 51) <> 0 ==> v (Seq.index (as_seq h0 b) 4) >= pow2 51)
  )

#push-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=false"

let carry_top b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  let b4' = b4 &. mask_51 in
  let b0' = b0 +. u64 19 *. (b4 >>. 51ul) in
  assert_norm (pow2 51 + 19 * (pow2 64 / pow2 51) <= 2 * S51.max51);
  assert_norm (v mask_51 == pow2 51 - 1);

  logand_spec b4 mask_51;
  logand_mask b4 mask_51 51;
  assert_norm (1 * S51.max51 < pow2 51);
  assert (v b4' <= 1 * S51.max51);
  calc (==) {
              v b0' <: nat;
              (==) { }
              v (b0 +. u64 19 *. (b4 >>. 51ul));
              (==) { add_mod_lemma b0 (u64 19 *. (b4 >>. 51ul));
                     mul_mod_lemma (u64 19) (b4 >>. 51ul);
                     Math.Lemmas.lemma_mod_plus_distr_r (v b0) (19 * v (b4 >>. 51ul)) (pow2 64)}
              (v b0 + (19 * (v (b4 >>. 51ul)))) % pow2 64;
              (==) { shift_right_lemma b4 51ul }
              (v b0 + (19 * (v b4 / pow2 51))) % pow2 64;
              (==) { Math.Lemmas.small_mod (v b0 + 19 * (v b4 / pow2 51)) (pow2 64) }
              v b0 + 19 * (v b4 / pow2 51);
         };
  calc (<) {
    v b0 + 19 * (v b4 / pow2 51);
    (<) { Math.Lemmas.lemma_div_lt_nat (v b4) 64 51 }
    v b0 + 19 * (pow2 13);
    (<=) { }
    pow2 51 + 19 * pow2 13;
    (<=) {assert_norm (pow2 51 + 19 * pow2 13 <= 2 * S51.max51) }
    2 * S51.max51;
  };
  calc (==) {
    (pow2 204 * v b4 + v b0) % Spec.Curve25519.prime;
    (==) {Math.Lemmas.lemma_div_mod (v b4) (pow2 51);
           Math.Lemmas.distributivity_add_right (pow2 204) (pow2 51 * (v b4 / pow2 51))
                                                (v b4 % pow2 51);
           Math.Lemmas.pow2_plus 204 51;
           Math.Lemmas.paren_mul_right (pow2 204) (pow2 51) (v b4 / pow2 51)
     }
    (pow2 255 * (v b4 / pow2 51) + pow2 204 * (v b4 % pow2 51) + v b0) % SC.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (pow2 255 * (v b4 / pow2 51))
         (pow2 204 * (v b4 % pow2 51) + v b0) (SC.prime);
           Math.Lemmas.lemma_mod_mul_distr_l (pow2 255) (v b4 / pow2 51) (SC.prime);
           assert_norm (pow2 255 % SC.prime == 19)
           }
    ((19 * (v b4 / pow2 51)) % SC.prime + (pow2 204 * (v b4 % pow2 51) + v b0)) % SC.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l
      (19 * (v b4 / pow2 51))
      (pow2 204 * (v b4 % pow2 51) + v b0) SC.prime
      }
    (v b0 + 19 * (v b4 / pow2 51) + pow2 204 * (v b4 % pow2 51)) % SC.prime;
    (==) {   }
    (v b0' + pow2 204 * (v b4 % pow2 51)) % SC.prime;
    (==) { logand_mask b4 mask_51 51 }
    (pow2 204 * v b4' + v b0') % SC.prime;
  };
  let h0 = get() in
  b.(4ul) <- b4';
  b.(0ul) <- b0';
  let h1 = get() in
  calc (==) {
    F51.fevalh h0 b;
    (==) { let s = as_seq h0 b in
      let v0 = v (Seq.index s 0) in
      let v1 = v (Seq.index s 1) in
      let v2 = v (Seq.index s 2) in
      let v3 = v (Seq.index s 3) in
      let v4 = v (Seq.index s 4) in
      lemma_change_as_nat_repr v0 v1 v2 v3 v4;
      Math.Lemmas.lemma_mod_plus_distr_l
      (v0 + pow2 204 * v4) (pow2 51 * v1 + pow2 102 * v2 + pow2 153 * v3) SC.prime;
      Math.Lemmas.lemma_mod_plus_distr_l
      (v b0' + pow2 204 * v b4') (pow2 51 * v1 + pow2 102 * v2 + pow2 153 * v3) SC.prime;
      lemma_change_as_nat_repr (v b0') v1 v2 v3 (v b4')
      }

    F51.fevalh h1 b;
  };
  lemma_small_carry_top (v b0) (v b4)

#pop-options

let reduce_513 a =
  BN.fmul1 a a (u64 1)

inline_for_extraction noextract
val fcontract_first_carry_full:
  input:felem ->
  Stack unit
    (requires fun h -> live h input /\ F51.mul_inv_t h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1 /\
      F51.fevalh h0 input == F51.fevalh h1 input /\
      F51.felem_fits h1 input (2, 1, 1, 1, 1)
    )
let fcontract_first_carry_full input =
  fcontract_first_carry_pass input;
  carry_top input

#push-options "--z3cliopt smt.arith.nl=false --z3rlimit 300"

inline_for_extraction noextract
val carry_0_to_1:
  output:felem ->
  Stack unit
    (requires fun h -> live h output /\
      F51.felem_fits h output (2, 1, 1, 1, 1) /\
      (let s = as_seq h output in
       v (Seq.index s 1) + (v (Seq.index s 0) / pow2 51) < pow2 51)
    )
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      F51.fevalh h0 output == F51.fevalh h1 output /\
      F51.felem_fits h1 output (1, 1, 1, 1, 1)
    )

let carry_0_to_1 output =
  let i0 = output.(0ul) in
  let i1 = output.(1ul) in
  let i0' = i0 &. mask_51 in
  let i1' = i1 +. (i0 >>. 51ul) in
  assert_norm (v mask_51 == pow2 51 - 1);
  logand_spec i0 mask_51;
  logand_mask i0 mask_51 51;
  assert_norm (2 * S51.max51 < pow2 52);
  Math.Lemmas.lemma_div_lt_nat (v i0) 52 51;
  assert (v (i0 >>. 51ul) <= 1);
  Math.Lemmas.small_mod (v i1 + (v i0 / pow2 51)) (pow2 64);
  calc (==) {
    v i0' + v i1' * pow2 51;
    (==) { }
    v i0 % pow2 51 + (v i1 + (v i0 / pow2 51)) * pow2 51;
    (==) { Math.Lemmas.distributivity_add_left (v i1) (v i0 / pow2 51) (pow2 51) }
    v i0 % pow2 51 + v i1 * pow2 51 + (v i0 / pow2 51) * pow2 51;
    (==) { Math.Lemmas.euclidean_division_definition (v i0) (pow2 51) }
    v i0 + v i1 * pow2 51;
  };
  output.(0ul) <- i0';
  output.(1ul) <- i1'

inline_for_extraction noextract
val fcontract_second_carry_pass:
  input:felem ->
  Stack unit
    (requires fun h -> live h input /\
      F51.felem_fits h input (2, 1, 1, 1, 1) )
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1 /\
      F51.as_nat h0 input == F51.as_nat h1 input /\
      F51.felem_fits h1 input (1, 1, 1, 1, 2) /\
      (v (Seq.index (as_seq h1 input) 4) = pow2 51 ==> v (Seq.index (as_seq h1 input) 1) < 2) /\
      v (Seq.index (as_seq h1 input) 4) < pow2 51 + 1
    )


let fcontract_second_carry_pass input =
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let t1' = t1 +. (t0 >>. 51ul) in
  let t0' = t0 &. mask_51 in
  let t2' = t2 +. (t1' >>. 51ul) in
  let t1'' = t1' &. mask_51 in
  let t3' = t3 +. (t2' >>. 51ul) in
  let t2'' = t2' &. mask_51 in
  let t4' = t4 +. (t3' >>. 51ul) in
  let t3'' = t3' &. mask_51 in
  assert_norm (v mask_51 == pow2 51 - 1);
  logand_spec t0 mask_51;
  logand_mask t0 mask_51 51;
  logand_spec t1' mask_51;
  logand_mask t1' mask_51 51;
  logand_spec t2' mask_51;
  logand_mask t2' mask_51 51;
  logand_spec t3' mask_51;
  logand_mask t3' mask_51 51;
  shift_right_lemma t0 51ul;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v t2 + v t1' / pow2 51) 51 64;
  shift_right_lemma t1' 51ul;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v t3 + v t2' / pow2 51) 51 64;
  shift_right_lemma t2' 51ul;
  shift_right_lemma t3' 51ul;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v t4 + v t3' / pow2 51) 51 64;
  assert_norm (2 * S51.max51 < pow2 52);
  calc (==) {
    v t1' <: nat;
    (==) { }
    (v t1 + (v (t0 >>. 51ul))) % pow2 64;
    (==) { shift_right_lemma t0 51ul }
    (v t1 + (v t0 / pow2 51)) % pow2 64;
    (==) { calc (<) {
             v t0 / pow2 51;
             (<) { Math.Lemmas.lemma_div_lt_nat (v t0) 52 51; assert_norm (pow2 1 == 2)}
             2;
             };
             assert ( v t0 / pow2 51 <= 1);
             assert_norm (pow2 51 < pow2 64);
             Math.Lemmas.small_mod (v t1 + (v t0 / pow2 51)) (pow2 64) }
    v t1 + (v t0 / pow2 51);
  };
  Math.Lemmas.lemma_div_lt_nat (v t0) 52 51; assert_norm (pow2 1 == 2);
  assert_norm (pow2 51 < pow2 64);
  Math.Lemmas.small_mod (v t1 + (v t0 / pow2 51)) (pow2 64);
  assert (v t1' == (v t1 + v t0 / pow2 51));
  Math.Lemmas.lemma_div_lt_nat (v t1') 52 51;
  Math.Lemmas.small_mod (v t2 + (v t1' / pow2 51)) (pow2 64);
  assert (v t2' <= pow2 51);
  assert (v t2' == (v t2 + (v t1 + (v t0 / pow2 51)) / pow2 51));
  Math.Lemmas.lemma_div_lt_nat (v t2') 52 51;
  Math.Lemmas.small_mod (v t3 + (v t2' / pow2 51)) (pow2 64);
  assert (v t3' <= pow2 51);
  assert (v t3' == (v t3 + ((v t2 + ((v t1 + (v t0 / pow2 51)) / pow2 51)) / pow2 51)));
  Math.Lemmas.lemma_div_lt_nat (v t3') 52 51;
  Math.Lemmas.small_mod (v t4 + (v t3' / pow2 51)) (pow2 64);
  assert (v t4' == (v t4 + (v t3 + ((v t2 + ((v t1 + (v t0 / pow2 51)) / pow2 51)) / pow2 51)) / pow2 51));
  lemma_fcontract_first_carry_pass (v t0) (v t1) (v t2) (v t3) (v t4)
    (v t0') (v t1'') (v t2'') (v t3'') (v t4');
  let lemma_imp () : Lemma
    (requires v t4' == pow2 51)
    (ensures v t1'' < 2)
    =
    Classical.move_requires (Math.Lemmas.small_div (v t3')) (pow2 51);
    assert (v t3' / pow2 51 == 1);
    assert ((v t3 + v t2' / pow2 51) / pow2 51 == 1);
    Classical.move_requires (Math.Lemmas.small_div (v t2')) (pow2 51);
    assert (v t3 + v t2' / pow2 51 == pow2 51);
    assert (v t2' / pow2 51 == 1);
    Classical.move_requires (Math.Lemmas.small_div (v t1')) (pow2 51);
    assert ((v t2 + v t1' / pow2 51) / pow2 51 == 1);
    assert (v t1' / pow2 51 == 1);
    assert (v t1' == pow2 51);
    assert_norm (pow2 51 % pow2 51 == 0)
  in Classical.move_requires lemma_imp ();
  make_u64_5 input t0' t1'' t2'' t3'' t4'

#pop-options

inline_for_extraction noextract
val fcontract_second_carry_full:
  input:felem ->
  Stack unit
    (requires fun h -> live h input /\ F51.felem_fits h input (2, 1, 1, 1, 1))
    (ensures fun h0 _ h1 -> modifies (loc input) h0 h1 /\
      F51.felem_fits h1 input (1, 1, 1, 1, 1) /\
      F51.fevalh h0 input == F51.fevalh h1 input
    )
let fcontract_second_carry_full input =
  fcontract_second_carry_pass input;
  carry_top input;
  carry_0_to_1 input

let lemma_fcontract_trim (a0 a1 a2 a3 a4:uint64) : Lemma
    (requires
      v a0 < pow2 51 /\ v a1 < pow2 51 /\ v a2 < pow2 51 /\ v a3 < pow2 51 /\ v a4 < pow2 51 /\
      (v a0 < pow2 51 - 19 \/ v a1 < pow2 51 - 1 \/ v a2 < pow2 51 - 1 \/ v a3 < pow2 51 - 1 \/ v a4 < pow2 51 - 1))
    (ensures S51.as_nat5 (a0, a1, a2, a3, a4) < SC.prime)
  =
  assert_norm (pow2 51 = 0x8000000000000);
  lemma_change_as_nat_repr (v a0) (v a1) (v a2) (v a3) (v a4);
  assert_norm (S51.as_nat5 (u64 (pow2 51 - 20), u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 1)) < SC.prime);
  assert_norm (S51.as_nat5 (u64 (pow2 51 - 1), u64 (pow2 51 - 2), u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 1)) < SC.prime);
  assert_norm (S51.as_nat5 (u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 2), u64 (pow2 51 - 1), u64 (pow2 51 - 1)) < SC.prime);
  assert_norm (S51.as_nat5 (u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 2), u64 (pow2 51 - 1)) < SC.prime);
  assert_norm (S51.as_nat5 (u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 1), u64 (pow2 51 - 2)) < SC.prime)

#restart-solver
#push-options "--z3rlimit 600"


inline_for_extraction noextract
val fcontract_trim:
  input:felem ->
  Stack unit
    (requires fun h -> live h input /\ F51.felem_fits h input (1, 1, 1, 1, 1))
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1 /\
      F51.felem_fits h1 input (1, 1, 1, 1, 1) /\
      F51.fevalh h0 input == F51.as_nat h1 input
    )

let fcontract_trim input =
  let a0 = input.(0ul) in
  let a1 = input.(1ul) in
  let a2 = input.(2ul) in
  let a3 = input.(3ul) in
  let a4 = input.(4ul) in
  let m0 = gte_mask a0 (u64 0x7ffffffffffed) in
  let m1 = eq_mask a1 (u64 0x7ffffffffffff) in
  let m2 = eq_mask a2 (u64 0x7ffffffffffff) in
  let m3 = eq_mask a3 (u64 0x7ffffffffffff) in
  let m4 = eq_mask a4 (u64 0x7ffffffffffff) in
  let mask = m0 &. m1 &. m2 &. m3 &. m4 in

  assert (v mask == maxint U64 \/ v mask == 0);
  UInt.logand_lemma_1 (UInt.to_uint_t 64 (v m0));
  UInt.logand_lemma_1 (UInt.to_uint_t 64 (v m1));
  UInt.logand_lemma_1 (UInt.to_uint_t 64 (v m2));
  UInt.logand_lemma_1 (UInt.to_uint_t 64 (v m3));
  UInt.logand_lemma_1 (UInt.to_uint_t 64 (v m4));
  UInt.logand_lemma_2 (UInt.to_uint_t 64 (v m0));
  UInt.logand_lemma_2 (UInt.to_uint_t 64 (v m1));
  UInt.logand_lemma_2 (UInt.to_uint_t 64 (v m2));
  UInt.logand_lemma_2 (UInt.to_uint_t 64 (v m3));
  UInt.logand_lemma_2 (UInt.to_uint_t 64 (v m4));

  assert (v mask = UInt.ones 64 ==> (v a0 >= pow2 51 - 19 /\ v a1 = pow2 51 - 1 /\ v a2 = pow2 51 - 1
    /\ v a3 = pow2 51 - 1 /\ v a4 = pow2 51 - 1));
  assert (v mask = UInt.zero 64 ==> (v a0 < pow2 51 - 19 \/ v a1 < pow2 51 - 1 \/ v a2 < pow2 51 - 1
    \/ v a3 < pow2 51 - 1 \/ v a4 < pow2 51 - 1));
  let a0' = a0 -. (u64 0x7ffffffffffed &. mask) in
  let a1' = a1 -. (u64 0x7ffffffffffff &. mask) in
  let a2' = a2 -. (u64 0x7ffffffffffff &. mask) in
  let a3' = a3 -. (u64 0x7ffffffffffff &. mask) in
  let a4' = a4 -. (u64 0x7ffffffffffff &. mask) in
  UInt.logand_lemma_1 (UInt.to_uint_t 64 0x7ffffffffffed);
  UInt.logand_lemma_2 (UInt.to_uint_t 64 0x7ffffffffffed);
  UInt.logand_lemma_1 (UInt.to_uint_t 64 0x7ffffffffffff);
  UInt.logand_lemma_2 (UInt.to_uint_t 64 0x7ffffffffffff);

  assert ((v a0' <= 18 /\ v a1' = 0 /\ v a2' = 0 /\ v a3' = 0 /\ v a4' = 0) \/ (v a0' < pow2 51 - 19 \/ v a1' < pow2 51 - 1 \/ v a2' < pow2 51 - 1 \/ v a3' < pow2 51 - 1 \/ v a4' < pow2 51 - 1));
  assert_norm (S51.as_nat5 (u64 18, u64 0, u64 0, u64 0, u64 0) < SC.prime);
  lemma_fcontract_trim a0' a1' a2' a3' a4';
  FStar.Math.Lemmas.small_mod (S51.as_nat5 (a0', a1', a2', a3', a4')) SC.prime;
  make_u64_5 input a0' a1' a2' a3' a4'

#pop-options


inline_for_extraction noextract
val reduce_:
  out:felem ->
  Stack unit
    (requires fun h -> live h out /\ F51.mul_inv_t h out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.felem_fits h1 out (1, 1, 1, 1, 1) /\
      F51.fevalh h0 out == F51.fevalh h1 out /\
      F51.fevalh h1 out == F51.as_nat h1 out
    )
let reduce_ out =
  fcontract_first_carry_full out;
  fcontract_second_carry_full out;
  fcontract_trim out;
  let h1 = get() in
  Math.Lemmas.small_mod (F51.as_nat h1 out) SC.prime

let fmul output input input2 =
  push_frame();
  let tmp = create 10ul (u128 0) in
  BN.fmul output input input2 tmp;
  pop_frame()

let times_2 out a =
  (**) let h0 = get() in
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let o0 = u64 2 *. a0 in
  let o1 = u64 2 *. a1 in
  let o2 = u64 2 *. a2 in
  let o3 = u64 2 *. a3 in
  let o4 = u64 2 *. a4 in
  make_u64_5 out o0 o1 o2 o3 o4;

  (**) let h1 = get() in
  (**) assert (S51.felem_fits1 a0 1);
  (**) assert (F51.felem_fits h1 out (2, 4, 2, 2, 2));

  calc (==) {
    (2 * (F51.fevalh h0 a)) % SC.prime;
    (==) { calc (==) {
           F51.fevalh h0 a;
           (==) { }
           S51.as_nat5 (a0, a1, a2, a3, a4) % SC.prime;
           }
         }
    (2 * (S51.as_nat5 (a0, a1, a2, a3, a4) % SC.prime)) % SC.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r 2 (S51.as_nat5 (a0, a1, a2, a3, a4)) SC.prime }
    (2 * S51.as_nat5 (a0, a1, a2, a3, a4)) % SC.prime;
    (==) { calc (==) {
           2 * S51.as_nat5 (a0, a1, a2, a3, a4);
           (==) { SL51.lemma_smul_felem5 (u64 2) (a0, a1, a2, a3, a4) }
           2 * v a0 + 2 * v a1 * S51.pow51 + 2 * v a2 * S51.pow51 * S51.pow51 +
           2 * v a3 * S51.pow51 * S51.pow51 * S51.pow51 +
           2 * v a4 * S51.pow51 * S51.pow51 * S51.pow51 * S51.pow51;
           (==) {
             assert_norm (2 * S51.pow51 < pow2 64);
             assert_norm (4 * S51.pow51 < pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a0) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a1) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a2) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a3) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a4) (pow2 64)
           }
           S51.as_nat5 (u64 2 *. a0, u64 2 *. a1, u64 2 *. a2, u64 2 *. a3, u64 2 *. a4);
           }
         }
    S51.as_nat5 (u64 2 *. a0, u64 2 *. a1, u64 2 *. a2, u64 2 *. a3, u64 2 *. a4) % SC.prime;
    (==) { }
    F51.fevalh h1 out;
  }

let times_d out a =
  push_frame();
  let d = create 5ul (u64 0) in
  d.(0ul) <- u64 0x00034dca135978a3;
  d.(1ul) <- u64 0x0001a8283b156ebd;
  d.(2ul) <- u64 0x0005e7a26001c029;
  d.(3ul) <- u64 0x000739c663a03cbb;
  d.(4ul) <- u64 0x00052036cee2b6ff;
  assert_norm (S51.as_nat5 (u64 0x00034dca135978a3, u64 0x0001a8283b156ebd,
    u64 0x0005e7a26001c029, u64 0x000739c663a03cbb, u64 0x00052036cee2b6ff) %
      Spec.Curve25519.prime == Spec.Ed25519.d);
  fmul out d a;
  pop_frame()

let times_2d out a =
  push_frame();
  let d2 = create 5ul (u64 0) in
  d2.(0ul) <- u64 0x00069b9426b2f159;
  d2.(1ul) <- u64 0x00035050762add7a;
  d2.(2ul) <- u64 0x0003cf44c0038052;
  d2.(3ul) <- u64 0x0006738cc7407977;
  d2.(4ul) <- u64 0x0002406d9dc56dff;
  fmul out d2 a;
  assert_norm (S51.as_nat5 (u64 0x00069b9426b2f159, u64 0x00035050762add7a,
    u64  0x0003cf44c0038052, u64 0x0006738cc7407977, u64  0x0002406d9dc56dff) %
      Spec.Curve25519.prime == 2 `SC.fmul` Spec.Ed25519.d);
  pop_frame()

let fsquare out a =
  push_frame();
  let tmp = create 5ul (u128 0) in
  BN.fsqr out a tmp;
  pop_frame()

inline_for_extraction noextract
val fsquare_times_:
    output:felem
  -> input:felem
  -> tmp:lbuffer uint128 5ul
  -> count:size_t{v count > 0} ->
  Stack unit
    (requires fun h ->
      live h output /\ live h input /\ live h tmp /\
      (disjoint output input \/ output == input) /\
      disjoint input tmp /\ disjoint output tmp /\
      F51.felem_fits h input (1, 2, 1, 1, 1)
      )
    (ensures  fun h0 _ h1 -> modifies (loc output |+| loc tmp) h0 h1 /\
      F51.felem_fits h1 output (1, 2, 1, 1, 1) /\
      F51.fevalh h1 output == Hacl.Spec.Curve25519.Finv.pow (F51.fevalh h0 input) (pow2 (v count))
    )
let fsquare_times_ output input tmp count =
  Hacl.Curve25519.Finv.Field51.fsquare_times_51 output input tmp count

let fsquare_times output input count =
  push_frame();
  let tmp = create 5ul (u128 0) in
  fsquare_times_ output input tmp count;
  pop_frame()

let fsquare_times_inplace output count =
  push_frame();
  let tmp = create 5ul (u128 0) in
  fsquare_times_ output output tmp count;
  pop_frame()

let inverse out a =
  push_frame();
  let tmp = create 10ul (u128 0) in
  Hacl.Curve25519.Finv.Field51.finv_51 out a tmp;
  pop_frame()

let reduce out = reduce_ out

#push-options "--z3rlimit 100"

let lemma_split_nat_from_bytes_le (n:size_nat) (k:lbytes n) (i:nat{i <= n}) : Lemma
  (nat_from_bytes_le (slice k 0 i) == nat_from_bytes_le k % pow2 (i * 8) /\
   nat_from_bytes_le (slice k i n) == nat_from_bytes_le k / pow2 (i * 8))
  =
  nat_from_intseq_le_slice_lemma k i;
  assert (nat_from_bytes_le (slice k 0 i) + nat_from_bytes_le (slice k i n) * pow2 (i * 8) == nat_from_bytes_le k);
  FStar.Math.Lemmas.cancel_mul_div (nat_from_bytes_le (slice k i n)) (pow2 (i * 8));
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (nat_from_bytes_le (slice k 0 i))
    (nat_from_bytes_le (slice k i n) * pow2 (i * 8)) (pow2 (i * 8));
  FStar.Math.Lemmas.cancel_mul_mod (nat_from_bytes_le (slice k i n)) (pow2 (i * 8));
  FStar.Math.Lemmas.small_mod (nat_from_bytes_le (slice k 0 i)) (pow2 (i * 8))

let lemma_partial_nat_from_bytes_le (k:lbytes 32) (i:nat) (j:nat{i <= j /\ j <= 32})
  : Lemma (nat_from_bytes_le (slice k i j) == (nat_from_bytes_le k / pow2 (i * 8)) % pow2 ((j - i) * 8))
  =
  nat_from_intseq_le_slice_lemma k i;
  lemma_split_nat_from_bytes_le 32 k i;
  nat_from_intseq_le_slice_lemma (slice k i 32) (j - i);
  let k' = slice k i 32 in
  lemma_split_nat_from_bytes_le (32 - i) k' (j - i);
  assert (Seq.equal (slice k i j) (slice (slice k i 32) 0 (j - i)))

let lemma_combine_div_mod_pow2 (x:nat) (d:pos) (d':pos{d' <= 12}) : Lemma
  ((((x / pow2 d) % pow2 64) / pow2 d') % pow2 51 == (x / pow2 (d + d')) % pow2 51)
  =
  Math.Lemmas.pow2_modulo_division_lemma_1 (x / pow2 d) d' 64;
  Math.Lemmas.division_multiplication_lemma (x) (pow2 d) (pow2 d');
  Math.Lemmas.pow2_plus d d';
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (x / pow2 (d+d')) 51 (64-d')

val lemma_load_51: k:lbytes 32 -> Lemma
  (let i0 = nat_from_bytes_le (slice k 0 8) % pow2 51 in
   let i1 = (nat_from_bytes_le (slice k 6 14) / pow2 3) % pow2 51 in
   let i2 = (nat_from_bytes_le (slice k 12 20) / pow2 6) % pow2 51 in
   let i3 = (nat_from_bytes_le (slice k 19 27) / pow2 1) % pow2 51 in
   let i4 = (nat_from_bytes_le (slice k 24 32) / pow2 12) % pow2 51 in
   i0 + i1 * pow2 51 + i2 * pow2 51 * pow2 51 + i3 * pow2 51 * pow2 51 * pow2 51 + i4 * pow2 51 * pow2 51 * pow2 51 * pow2 51 == nat_from_bytes_le k % pow2 255)

#pop-options

#push-options "--z3cliopt smt.arith.nl=false --z3rlimit 200"


let lemma_load_51 k =
  let i0 = nat_from_bytes_le (slice k 0 8) % pow2 51 in
  let i1 = (nat_from_bytes_le (slice k 6 14) / pow2 3) % pow2 51 in
  let i2 = (nat_from_bytes_le (slice k 12 20) / pow2 6) % pow2 51 in
  let i3 = (nat_from_bytes_le (slice k 19 27) / pow2 1) % pow2 51 in
  let i4 = (nat_from_bytes_le (slice k 24 32) / pow2 12) % pow2 51 in
  calc (==) {
    i0;
    (==) { assert_norm (pow2 (0 * 8) == 1); lemma_partial_nat_from_bytes_le k 0 8 }
    (nat_from_bytes_le k % pow2 64) % pow2 51;
    (==) { FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (nat_from_bytes_le k) 51 64 }
    nat_from_bytes_le k % pow2 51;
  };
  calc (==) {
    i1;
    (==) { lemma_partial_nat_from_bytes_le k 6 14 }
    (((nat_from_bytes_le k / pow2 48) % pow2 64) / pow2 3) % pow2 51;
    (==) { lemma_combine_div_mod_pow2 (nat_from_bytes_le k) 48 3 }
    (nat_from_bytes_le k / pow2 51) % pow2 51;
  };
  calc (==) {
    i2;
    (==) { lemma_partial_nat_from_bytes_le k 12 20 }
    (((nat_from_bytes_le k / pow2 96) % pow2 64) / pow2 6) % pow2 51;
    (==) { lemma_combine_div_mod_pow2 (nat_from_bytes_le k) 96 6 }
     (nat_from_bytes_le k / pow2 102) % pow2 51;
  };
  calc (==) {
    i3;
    (==) { lemma_partial_nat_from_bytes_le k 19 27 }
    (((nat_from_bytes_le k / pow2 152) % pow2 64) / pow2 1) % pow2 51;
    (==) { lemma_combine_div_mod_pow2 (nat_from_bytes_le k) 152 1 }
    (nat_from_bytes_le k / pow2 153) % pow2 51;
  };
  calc (==) {
    i4;
    (==) { lemma_partial_nat_from_bytes_le k 24 32 }
    (((nat_from_bytes_le k / pow2 192) % pow2 64) / pow2 12) % pow2 51;
    (==) { lemma_combine_div_mod_pow2 (nat_from_bytes_le k) 192 12 }
    (nat_from_bytes_le k / pow2 204) % pow2 51;
  };
  let n = nat_from_bytes_le k in
  calc (==) {
    n % pow2 255;
    (==) {   Math.Lemmas.lemma_div_mod (n % pow2 255) (pow2 204);
             Math.Lemmas.pow2_modulo_modulo_lemma_1 n 204 255;
             Math.Lemmas.pow2_modulo_division_lemma_1 n 204 255
      }
    pow2 204 * ((n / pow2 204) % pow2 51) + (n % pow2 204);
    (==) {   Math.Lemmas.lemma_div_mod (n % pow2 204) (pow2 153);
             Math.Lemmas.pow2_modulo_modulo_lemma_1 n 153 204;
             Math.Lemmas.pow2_modulo_division_lemma_1 n 153 204
         }
    pow2 204 * ((n / pow2 204) % pow2 51) +
    pow2 153 * ((n / pow2 153) % pow2 51) + (n % pow2 153);
    (==) {   Math.Lemmas.lemma_div_mod (n % pow2 153) (pow2 102);
             Math.Lemmas.pow2_modulo_modulo_lemma_1 n 102 153;
             Math.Lemmas.pow2_modulo_division_lemma_1 n 102 153 }
    pow2 204 * ((n / pow2 204) % pow2 51) +
    pow2 153 * ((n / pow2 153) % pow2 51) +
    pow2 102 * ((n / pow2 102) % pow2 51) + (n % pow2 102);
    (==) {   Math.Lemmas.lemma_div_mod (n % pow2 102) (pow2 51);
             Math.Lemmas.pow2_modulo_modulo_lemma_1 n 51 102;
             Math.Lemmas.pow2_modulo_division_lemma_1 n 51 102 }
    pow2 204 * ((n / pow2 204) % pow2 51) +
    pow2 153 * ((n / pow2 153) % pow2 51) +
    pow2 102 * ((n / pow2 102) % pow2 51) +
    pow2 51 * ((n / pow2 51) % pow2 51) +
    n % pow2 51;
    (==) {
      calc (==) {
        ((n / pow2 204) % pow2 51) * pow2 51 * pow2 51 * pow2 51 * pow2 51;
        (==) { Classical.forall_intro_3 (FStar.Math.Lemmas.paren_mul_right) }
        ((n / pow2 204) % pow2 51) * (pow2 51 * pow2 51 * pow2 51 * pow2 51);
        (==) { assert_norm (pow2 51 * pow2 51 * pow2 51 * pow2 51 == pow2 204);
               FStar.Math.Lemmas.swap_mul (pow2 204) ((n / pow2 204) % pow2 51) }
        pow2 204 * ((n / pow2 204) % pow2 51);
      };
      calc (==) {
        ((n / pow2 153) % pow2 51) * pow2 51 * pow2 51 * pow2 51;
        (==) { Classical.forall_intro_3 (FStar.Math.Lemmas.paren_mul_right) }
        ((n / pow2 153) % pow2 51) * (pow2 51 * pow2 51 * pow2 51);
        (==) { assert_norm (pow2 51 * pow2 51 * pow2 51 == pow2 153);
               FStar.Math.Lemmas.swap_mul (pow2 153) ((n / pow2 153) % pow2 51) }
        pow2 153 * ((n / pow2 153) % pow2 51);
      };
      calc (==) {
        ((n / pow2 102) % pow2 51) * pow2 51 * pow2 51;
        (==) { FStar.Math.Lemmas.paren_mul_right  ((n / pow2 102) % pow2 51) (pow2 51) (pow2 51);
               assert_norm (pow2 51 * pow2 51 == pow2 102);
               FStar.Math.Lemmas.swap_mul (pow2 102) ((n / pow2 102) % pow2 51) }
        pow2 102 * ((n / pow2 102) % pow2 51);
      };
      calc (==) {
        ((n / pow2 51) % pow2 51) * pow2 51;
        (==) { FStar.Math.Lemmas.swap_mul (pow2 51) ((n / pow2 51) % pow2 51) }
        pow2 51 * ((n / pow2 51) % pow2 51);
      }
    }
    n % pow2 51 +
    ((n / pow2 51) % pow2 51) * pow2 51 +
    ((n / pow2 102) % pow2 51) * pow2 51 * pow2 51 +
    ((n / pow2 153) % pow2 51) * pow2 51 * pow2 51 * pow2 51 +
    ((n / pow2 204) % pow2 51) * pow2 51 * pow2 51 * pow2 51 * pow2 51;
  }

#pop-options

#push-options "--z3rlimit 1000"

let load_51 output input =
  let i0 = uint_from_bytes_le (sub input 0ul 8ul) in
  let i1 = uint_from_bytes_le (sub input 6ul 8ul) in
  let i2 = uint_from_bytes_le (sub input 12ul 8ul) in
  let i3 = uint_from_bytes_le (sub input 19ul 8ul) in
  let i4 = uint_from_bytes_le (sub input 24ul 8ul) in
  let output0 = (i0         ) &. mask_51 in
  let output1 = (i1 >>. 3ul ) &. mask_51 in
  let output2 = (i2 >>. 6ul ) &. mask_51 in
  let output3 = (i3 >>. 1ul ) &. mask_51 in
  let output4 = (i4 >>. 12ul) &. mask_51 in
  (**) assert_norm (0x7ffffffffffff == pow2 51 - 1);
  (**) logand_spec i0 mask_51;
  (**) logand_le i0 mask_51;
  (**) UInt.logand_mask (UInt.to_uint_t 64 (v i0)) 51;
  (**) logand_spec (i1 >>. 3ul) mask_51;
  (**) logand_le (i1 >>. 3ul) mask_51;
  (**) UInt.logand_mask (UInt.to_uint_t 64 (v (i1 >>. 3ul))) 51;
  (**) logand_spec (i2 >>. 6ul) mask_51;
  (**) logand_le (i2 >>. 6ul) mask_51;
  (**) UInt.logand_mask (UInt.to_uint_t 64 (v (i2 >>. 6ul))) 51;
  (**) logand_spec (i3 >>. 1ul) mask_51;
  (**) logand_le (i3 >>. 1ul) mask_51;
  (**) UInt.logand_mask (UInt.to_uint_t 64 (v (i3 >>. 1ul))) 51;
  (**) logand_spec (i4 >>. 12ul) mask_51;
  (**) logand_le (i4 >>. 12ul) mask_51;
  (**) UInt.logand_mask (UInt.to_uint_t 64 (v (i4 >>. 12ul))) 51;
  (**) let h0 = get() in
  make_u64_5 output output0 output1 output2 output3 output4;
  (**) shift_right_lemma i1 3ul;
  (**) shift_right_lemma i2 6ul;
  (**) shift_right_lemma i3 1ul;
  (**) shift_right_lemma i4 12ul;
  (**) lemma_reveal_uint_to_bytes_le #U64 (slice (as_seq h0 input) 0 8);
  (**) lemma_reveal_uint_to_bytes_le #U64 (slice (as_seq h0 input) 6 14);
  (**) lemma_reveal_uint_to_bytes_le #U64 (slice (as_seq h0 input) 12 20);
  (**) lemma_reveal_uint_to_bytes_le #U64 (slice (as_seq h0 input) 19 27);
  (**) lemma_reveal_uint_to_bytes_le #U64 (slice (as_seq h0 input) 24 32);
  (**) lemma_load_51 (as_seq h0 input)

#pop-options

#push-options "--z3rlimit 500"

let lemma_uints_to_bytes_le_split (v1 v2 v3 v4:uint64) : Lemma
  (Seq.equal
    (Lib.ByteSequence.uints_to_bytes_le #U64 #SEC #4
                                        (Seq.append (Seq.create 1 v1)
                                        (Seq.append (Seq.create 1 v2)
                                        (Seq.append (Seq.create 1 v3) (Seq.create 1 v4)))))

    (Seq.append
      (Lib.ByteSequence.uint_to_bytes_le v1)
      (Seq.append (Lib.ByteSequence.uint_to_bytes_le v2)
        (Seq.append (Lib.ByteSequence.uint_to_bytes_le v3)
                    (Lib.ByteSequence.uint_to_bytes_le v4))
      )))
  =
  let s_uints:lseq uint64 4 = Seq.append (Seq.create 1 v1)
                (Seq.append (Seq.create 1 v2)
                (Seq.append (Seq.create 1 v3) (Seq.create 1 v4))) in
  let s1 = Lib.ByteSequence.uints_to_bytes_le #U64 #SEC #4 s_uints in
  let s2 =     (Seq.append
      (Lib.ByteSequence.uint_to_bytes_le v1)
      (Seq.append (Lib.ByteSequence.uint_to_bytes_le v2)
        (Seq.append (Lib.ByteSequence.uint_to_bytes_le v3)
                    (Lib.ByteSequence.uint_to_bytes_le v4))
      )) in
  // Classical.forall_intro does not work here
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 0;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 1;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 2;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 3;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 4;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 5;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 6;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 7;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 8;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 9;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 10;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 11;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 12;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 13;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 14;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 15;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 16;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 17;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 18;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 19;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 20;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 21;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 22;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 23;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 24;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 25;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 26;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 27;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 28;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 29;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 30;
  index_uints_to_bytes_le #U64 #SEC #4 s_uints 31

#pop-options

val store_4:
  output:lbuffer uint8 32ul ->
  v1:uint64 -> v2:uint64 -> v3:uint64 -> v4:uint64 ->
  Stack unit
    (requires fun h -> live h output)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      Seq.equal (as_seq h1 output)
        (Lib.ByteSequence.uints_to_bytes_le #U64 #SEC #4
        (Seq.append (Seq.create 1 v1)
          (Seq.append (Seq.create 1 v2)
            (Seq.append (Seq.create 1 v3) (Seq.create 1 v4)))))
    )
let store_4 output v0 v1 v2 v3 =
  let b0 = sub output 0ul  8ul in
  let b1 = sub output 8ul  8ul in
  let b2 = sub output 16ul 8ul in
  let b3 = sub output 24ul 8ul in
  lemma_uints_to_bytes_le_split v0 v1 v2 v3;
  uint_to_bytes_le b0 v0;
  uint_to_bytes_le b1 v1;
  uint_to_bytes_le b2 v2;
  uint_to_bytes_le b3 v3

let store_51 output input =
  let h0 = get() in
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let (o0, o1, o2, o3) = Hacl.Spec.Curve25519.Field51.store_felem5 (t0, t1, t2, t3, t4) in
  store_4 output o0 o1 o2 o3;
  Hacl.Impl.Curve25519.Lemmas.lemma_nat_from_uints64_le_4
        (Seq.append (Seq.create 1 o0)
          (Seq.append (Seq.create 1 o1)
            (Seq.append (Seq.create 1 o2) (Seq.create 1 o3))));
  assert_norm (pow2 255 - 19 < pow2 (64 * 32));
  lemma_nat_from_to_intseq_le_preserves_value 4
    ((Seq.append (Seq.create 1 o0)
      (Seq.append (Seq.create 1 o1)
        (Seq.append (Seq.create 1 o2) (Seq.create 1 o3)))));
  uints_to_bytes_le_nat_lemma #U64 #SEC 4 (F51.fevalh h0 input)
