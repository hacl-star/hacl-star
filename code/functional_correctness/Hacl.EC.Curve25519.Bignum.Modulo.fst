module Hacl.EC.Curve25519.Bignum.Modulo

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib
open FStar.Math.Lemmas

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils

open Hacl.EC.Curve25519.Bignum.Modulo.Lemmas

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val times_wide_19: x:s128{19 * H128.v x < pow2 platform_wide} -> Tot (y:s128{H128.v y = 19 * H128.v x})
let times_wide_19 x =
  let open Hacl.UInt128 in
  assert_norm (pow2 128 = 340282366920938463463374607431768211456);
  assert_norm (pow2 4 = 16);
  assert_norm (pow2 1 = 2);
  let y = x <<^ 4ul in
  modulo_lemma (pow2 4 * v x) (pow2 128);
  let z = x <<^ 1ul in
  modulo_lemma (pow2 1 * v x) (pow2 128);
  x +^ y +^ z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val freduce_degree_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> satisfiesModuloConstraints h b))
    (ensures (fun h0 _ h1 -> isDegreeReduced h0 h1 b /\ modifies_1 b h0 h1))
let freduce_degree_ b =
  let h0 = ST.get() in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  let b8 = b.(8ul) in
  lemma_freduce_degree_0 h0 b;
  let open Hacl.UInt128 in
  let b0' = b0 +^ times_wide_19 b5 in
  let b1' = b1 +^ times_wide_19 b6 in
  let b2' = b2 +^ times_wide_19 b7 in
  let b3' = b3 +^ times_wide_19 b8 in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3'


val freduce_degree:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> satisfiesModuloConstraints h b))
    (ensures (fun h0 _ h1 -> modifies_1 b h0 h1
      /\ satisfiesModuloConstraints h0 b
      /\ bound127 h1 b
      /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b =
  let h0 = ST.get() in
  freduce_degree_ b;
  let h1 = ST.get() in
  lemma_freduce_degree h0 h1 b

val mod_wide_2_51: a:s128 -> Tot (b:s128{H128.v b = H128.v a % pow2 51})
let mod_wide_2_51 a =
  let open Hacl.UInt128 in
  let mask = (Hacl.Cast.uint64_to_sint128 0x7ffffffffffffuL) in
  assert_norm(v mask = pow2 51 - 1);
  let res = a &^ mask in
  UInt.logand_mask #128 (v a) 51;
  res


private val div_wide_2_51: x:s128 -> Tot (y:s128{H128.v y = H128.v x / pow2 51 /\ H128.v y <= pow2 77})
let div_wide_2_51 x = 
  let open Hacl.UInt128 in
  pow2_minus 128 51; lemma_div_mod (H128.v x) (pow2 51);
  lemma_div_lt (v x) 128 51;
  (x >>^ 51ul)


let isCarriedWide_
  (h1:mem)
  (b0:H128.t) (b1:H128.t) (b2:H128.t) (b3:H128.t) (b4:H128.t)
  (b:bigint_wide) : GTot Type0 =
  live h1 b /\ length b >= norm_length+1
  /\ (
      let open Hacl.UInt128 in
      let r0  = v b0 / pow2 51 in
      let r1  = (v b1 + r0) / pow2 51 in
      let r2  = (v b2 + r1) / pow2 51 in
      let r3  = (v b3 + r2) / pow2 51 in
      v (get h1 b 5) = (v b4 + r3) / pow2 51
      /\ v (get h1 b 0) = v b0 % pow2 51
      /\ v (get h1 b 1) = (v b1 + r0)  % pow2 51
      /\ v (get h1 b 2) = (v b2 + r1)  % pow2 51
      /\ v (get h1 b 3) = (v b3 + r2)  % pow2 51
      /\ v (get h1 b 4) = (v b4 + r3)  % pow2 51
    )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val carry_wide_1_0:
  b:bigint_wide{length b >= norm_length+1} ->
  b0:u127 -> b1:u127 -> b2:u127 -> b3:u127 -> b4:u127 ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ isCarriedWide_ h1 b0 b1 b2 b3 b4 b ))
let carry_wide_1_0 b b0 b1 b2 b3 b4 =
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 77 = 151115727451828646838272);
  pow2_lt_compat 78 77; pow2_lt_compat 127 78; pow2_double_sum 127;
  assert(forall x y. {:pattern (v x + v y)}(v x < pow2 127 /\ v y <= pow2 77)
    ==> v x + v y < pow2 128);
  let b0' = mod_wide_2_51 b0 in
  let r0  = div_wide_2_51 b0 in
  let open Hacl.UInt128 in
  let b1' = mod_wide_2_51 (b1 +^ r0) in
  let r1  = div_wide_2_51 (b1 +^ r0) in
  let b2' = mod_wide_2_51 (b2 +^ r1) in
  let r2  = div_wide_2_51 (b2 +^ r1) in
  let b3' = mod_wide_2_51 (b3 +^ r2) in
  let r3  = div_wide_2_51 (b3 +^ r2) in
  let b4' = mod_wide_2_51 (b4 +^ r3) in
  let b5' = div_wide_2_51 (b4 +^ r3) in
  update_wide_6 b b0' b1' b2' b3' b4' b5'


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val carry_wide_1_:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ isCarried h0 h1 b))
let carry_wide_1_ b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  carry_wide_1_0 b b0 b1 b2 b3 b4


val carry_wide_1:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length /\ carried_1 h1 b))
let carry_wide_1 b =
  let h0 = ST.get() in
  carry_wide_1_ b;
  let h1 = ST.get() in
  lemma_carry_1 h0 h1 b


val carry_wide_2_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_2 h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ isCarried h0 h1 b))
let carry_wide_2_ b =
  pow2_lt_compat 127 83; pow2_lt_compat 127 51;
  carry_wide_1_ b


val carry_wide_2:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_2 h b))
    (ensures (fun h0 _ h1 -> carried_2 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
	  /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length
	  /\ carried_3 h1 b))
let carry_wide_2 b =
  let h0 = ST.get() in
  carry_wide_2_ b;
  let h1 = ST.get() in
  lemma_carry_2 h0 h1 b


val carry_wide_top_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      /\ (let open Hacl.UInt128 in v (get h b 0) + 19 * v (get h b 5) < pow2 128 )))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ carriedTopBottom h0 h1 b))
let carry_wide_top_ b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- H128.(b0 +^ times_wide_19 b5)


val carry_wide_top_1:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_1 h b))
    (ensures  (fun h0 _ h1 -> carried_1 h0 b /\ carried_2 h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime))
let carry_wide_top_1 b =
  let h0 = ST.get() in
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 77 = 151115727451828646838272);
  assert_norm (pow2 128 = 340282366920938463463374607431768211456);
  carry_wide_top_ b;
  let h1 = ST.get() in
  lemma_carry_top_1 h0 h1 b


val carry_wide_top_2:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_3 h b))
    (ensures  (fun h0 _ h1 -> carried_3 h0 b /\ carried_4 h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime))
let carry_wide_top_2 b =
  let h0 = ST.get() in
  assert_norm (pow2 5 = 32);
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 77 = 151115727451828646838272);
  assert_norm (pow2 128 = 340282366920938463463374607431768211456);
  carry_wide_top_ b;
  let h1 = ST.get() in
  lemma_carry_top_2 h0 h1 b


private val carry_wide_0_to_1_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_4 h b))
    (ensures  (fun h0 _ h1 -> isCarried01 h0 h1 b /\ modifies_1 b h0 h1))
let carry_wide_0_to_1_ b =
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 77 = 151115727451828646838272);
  assert_norm (pow2 128 = 340282366920938463463374607431768211456);
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod_wide_2_51 b0 in
  let r0  = div_wide_2_51 b0 in
  b.(0ul) <- b0';
  b.(1ul) <- H128.(b1 +^ r0)


val carry_wide_0_to_1:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_4 h b))
    (ensures  (fun h0 _ h1 -> carried_4 h0 b /\ modifies_1 b h0 h1 /\ norm_wide h1 b
      /\ eval_wide h1 b norm_length = eval_wide h0 b norm_length))
let carry_wide_0_to_1 b =
  let h0 = ST.get() in
  carry_wide_0_to_1_ b;
  let h1 = ST.get() in
  lemma_carry_0_to_1 h0 h1 b


val freduce_coefficients_wide:
  b:bigint_wide{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b norm_length % reveal prime))
let freduce_coefficients_wide b =
  carry_wide_1 b;
  carry_wide_top_1 b;
  carry_wide_2 b;
  carry_wide_top_2 b;
  carry_wide_0_to_1 b


(*******************************************************************************)

open Hacl.EC.Curve25519.Bignum.Modulo.Lemmas2

val times_19: x:s64{19 * v x < pow2 64} -> Tot (y:s64{v y = 19 * v x})
let times_19 x =
  assert_norm (pow2 64 = 18446744073709551616);
  assert_norm (pow2 4 = 16);
  assert_norm (pow2 1 = 2);
  let y = x <<^ 4ul in
  modulo_lemma (pow2 4 * v x) (pow2 64);
  let z = x <<^ 1ul in
  modulo_lemma (pow2 1 * v x) (pow2 64);
  x +^ y +^ z



val mod_2_51: a:s64 -> Tot (b:s64{H64.v b = H64.v a % pow2 51})
let mod_2_51 a =
  let open Hacl.UInt64 in
  let mask = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffffuL) in
  assert_norm(v mask = pow2 51 - 1);
  let res = a &^ mask in
  UInt.logand_mask #64 (v a) 51;
  res


private val div_2_51: x:s64 -> Tot (y:s64{H64.v y = H64.v x / pow2 51 /\ H64.v y <= pow2 13})
let div_2_51 x =
  let open Hacl.UInt64 in
  pow2_minus 64 51; lemma_div_mod (H64.v x) (pow2 51);
  lemma_div_lt (v x) 64 51;
  (x >>^ 51ul)


let isCarried_'
  (h1:mem)
  (b0:H64.t) (b1:H64.t) (b2:H64.t) (b3:H64.t) (b4:H64.t)
  (b:bigint) : GTot Type0 =
  live h1 b /\ length b >= norm_length+1
  /\ (
      let r0  = v b0 / pow2 51 in
      let r1  = (v b1 + r0) / pow2 51 in
      let r2  = (v b2 + r1) / pow2 51 in
      let r3  = (v b3 + r2) / pow2 51 in
      v (get h1 b 5) = (v b4 + r3) / pow2 51
      /\ v (get h1 b 0) = v b0 % pow2 51
      /\ v (get h1 b 1) = (v b1 + r0)  % pow2 51
      /\ v (get h1 b 2) = (v b2 + r1)  % pow2 51
      /\ v (get h1 b 3) = (v b3 + r2)  % pow2 51
      /\ v (get h1 b 4) = (v b4 + r3)  % pow2 51
    )

let u633 = x:s64{H64.v x < pow2 63}

private val carry_1_0':
  b:bigint{length b >= norm_length+1} ->
  b0:u633 -> b1:u633 -> b2:u633 -> b3:u633 -> b4:u633 ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ isCarried_ h1 b0 b1 b2 b3 b4 b ))
let carry_1_0' b b0 b1 b2 b3 b4 =
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 13 = 8192);
  assert_norm (pow2 63 = 9223372036854775808);
  pow2_double_sum 63;
  (* pow2_lt_compat 14 13; pow2_lt_compat 63 14; pow2_double_sum 63; *)
  assert(forall x y. {:pattern (v x + v y)}(v x < pow2 63 /\ v y <= pow2 13)
    ==> v x + v y < pow2 64);
  let b0' = mod_2_51 b0 in
  let r0  = div_2_51 b0 in
  let b1' = mod_2_51 (b1 +^ r0) in
  let r1  = div_2_51 (b1 +^ r0) in
  let b2' = mod_2_51 (b2 +^ r1) in
  let r2  = div_2_51 (b2 +^ r1) in
  let b3' = mod_2_51 (b3 +^ r2) in
  let r3  = div_2_51 (b3 +^ r2) in
  let b4' = mod_2_51 (b4 +^ r3) in
  let b5' = div_2_51 (b4 +^ r3) in
  update_6 b b0' b1' b2' b3' b4' b5'


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val carry_1_':
  b:bigint{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ isCarried h0 h1 b))
let carry_1_' b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  carry_1_0' b b0 b1 b2 b3 b4

val carry_1':
  b:bigint{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b (norm_length+1) = eval h0 b norm_length /\ carried_1 h1 b))
let carry_1' b =
  let h0 = ST.get() in
  carry_1_' b;
  let h1 = ST.get() in
  lemma_carry_1 h0 h1 b

val carry_2_':
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_2 h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ isCarried h0 h1 b))
let carry_2_' b =
  pow2_lt_compat 63 52; pow2_lt_compat 63 51;
  carry_1_' b

val carry_2':
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_2 h b))
    (ensures (fun h0 _ h1 -> carried_2 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_3 h1 b))
let carry_2' b =
  let h0 = ST.get() in
  carry_2_' b;
  let h1 = ST.get() in
  lemma_carry_2 h0 h1 b

val carry_top_':
  b:bigint ->
  Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      /\ v (get h b 0) + 19 * v (get h b 5) < pow2 64 ))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ carriedTopBottom h0 h1 b))
let carry_top_' b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- b0 +^ times_19 b5


val carry_top_1':
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_1 h b))
    (ensures  (fun h0 _ h1 -> carried_1 h0 b /\ carried_2 h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let carry_top_1' b =
  let h0 = ST.get() in
  assert_norm (pow2 13 = 8192);
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 63 = 9223372036854775808);
  pow2_double_sum 51; pow2_double_sum 64;
  carry_top_' b;
  let h1 = ST.get() in
  lemma_carry_top_1 h0 h1 b

val carry_top_2':
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_3 h b))
    (ensures  (fun h0 _ h1 -> carried_3 h0 b /\ carried_4 h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let carry_top_2' b =
  let h0 = ST.get() in
  assert_norm (pow2 13 = 8192);
  assert_norm (pow2 51 = 2251799813685248);
  assert_norm (pow2 63 = 9223372036854775808);
  pow2_double_sum 51; pow2_double_sum 64;
  carry_top_' b;
  let h1 = ST.get() in
  lemma_carry_top_2 h0 h1 b


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val carry_0_to_1_':
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_4 h b))
    (ensures  (fun h0 _ h1 -> isCarried01 h0 h1 b /\ modifies_1 b h0 h1))
let carry_0_to_1_' b =
  assert_norm (pow2 0 = 1); assert_norm (pow2 1 = 2); assert_norm (pow2 2 = 4);
  assert_norm (pow2 3 = 8); assert_norm (pow2 5 = 32);
  pow2_lt_compat 63 5; pow2_lt_compat 63 51; pow2_double_sum 63;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod_2_51 b0 in
  let r0  = div_2_51 b0 in
  b.(0ul) <- b0';
  b.(1ul) <- b1 +^ r0


val carry_0_to_1':
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_4 h b))
    (ensures  (fun h0 _ h1 -> carried_4 h0 b /\ modifies_1 b h0 h1 /\ norm h1 b
      /\ eval h1 b norm_length = eval h0 b norm_length))
let carry_0_to_1' b =
  let h0 = ST.get() in
  carry_0_to_1_' b;
  let h1 = ST.get() in
  lemma_carry_0_to_1 h0 h1 b


val freduce_coefficients:
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
let freduce_coefficients b =
  carry_1' b;
  carry_top_1' b;
  carry_2' b;
  carry_top_2' b;
  carry_0_to_1' b

#reset-options "--initial_fuel 0 --max_fuel 9 --z3rlimit 20"

open Hacl.EC.Curve25519.Bignum.Modulo.Lemmas3


private val lemma_2_255m19_val: n:nat ->
  Lemma (requires (n = 255))
        (ensures  (pow2 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949))
        [SMTPat (pow2 n - 19)]
let lemma_2_255m19_val n = assert_norm (pow2 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949)

#reset-options "--initial_fuel 0 --max_fuel 9 --z3rlimit 100"

val normalize:
  b:bigint ->
  Stack unit
    (requires (fun h -> norm h b))
    (ensures (fun h0 _ h1 -> norm h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b 5 = eval h0 b 5 % (pow2 255 - 19) ))
let normalize b =
  let h0 = ST.get() in
  let two51m1 = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffffuL) in
  let two51m19 = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffeduL) in
  assert_norm (v two51m1 = pow2 51 - 1); assert_norm(v two51m19 = pow2 51 - 19);
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let mask = H64.eq_mask b4 two51m1 in
  let mask4 = H64.eq_mask b4 two51m1 in
  let mask3 = H64.eq_mask b3 two51m1 in
  let mask2 = H64.eq_mask b2 two51m1 in
  let mask1 = H64.eq_mask b1 two51m1 in
  let mask0 = H64.gte_mask b0 two51m19 in
  UInt.logand_lemma_1 (v mask4); UInt.logand_lemma_2 (v mask4);
  UInt.logand_lemma_1 (v mask3); UInt.logand_lemma_2 (v mask3);
  UInt.logand_lemma_1 (v mask2); UInt.logand_lemma_2 (v mask2);
  UInt.logand_lemma_1 (v mask1); UInt.logand_lemma_2 (v mask1);
  UInt.logand_lemma_1 (v mask0); UInt.logand_lemma_2 (v mask0);
  let mask  = mask4 &^ mask3 &^ mask2 &^ mask1 &^ mask0 in
  cut (maskPrime mask b0 b1 b2 b3 b4);
  UInt.logand_lemma_1 (v two51m19); UInt.logand_lemma_2 (v two51m19);
  UInt.logand_lemma_1 (v b1); UInt.logand_lemma_2 (v b1);
  UInt.logand_lemma_1 (v b2); UInt.logand_lemma_2 (v b2);
  UInt.logand_lemma_1 (v b3); UInt.logand_lemma_2 (v b3);
  UInt.logand_lemma_1 (v b4); UInt.logand_lemma_2 (v b4);
  let b0' = (b0 -^ (two51m19 &^ mask)) in
  let b1' = (b1 -^ (b1 &^ mask)) in
  let b2' = (b2 -^ (b2 &^ mask)) in
  let b3' =  (b3 -^ (b3 &^ mask)) in
  let b4' =  (b4 -^ (b4 &^ mask)) in
  cut(masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4');
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3';
  b.(4ul) <- b4';
  let h1 = ST.get() in
  lemma_finalize h0 b h1 b mask
