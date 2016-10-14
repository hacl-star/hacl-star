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

val times_wide_19: x:s128(* {19 * v x < pow2 platform_wide} *) -> Tot (y:s128(* {v y = 19 * v x} *))
let times_wide_19 x =
  let open Hacl.UInt128 in
  let y = x <<^ 4ul in
  let z = x <<^ 1ul in
  x +%^ y +%^ z

let satisfiesModuloConstraints (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= 2*norm_length-1
  /\ maxValue_wide h b (2*norm_length-1) * 20 < pow2 63

let isDegreeReduced (h0:mem) (h1:mem) (b:bigint_wide) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ (let open Hacl.UInt128 in
  v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1) + 19 * v (get h0 b 6)
  /\ v (get h1 b 2) = v (get h0 b 2) + 19 * v (get h0 b 7)
  /\ v (get h1 b 3) = v (get h0 b 3) + 19 * v (get h0 b 8)
  /\ v (get h1 b 4) = v (get h0 b 4))

val freduce_degree_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> satisfiesModuloConstraints h b))
    (ensures (fun h0 _ h1 -> isDegreeReduced h0 h1 b /\ modifies_1 b h0 h1))
let freduce_degree_ b =
  let h0 = HST.get() in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  let b8 = b.(8ul) in
  (* lemma_freduce_degree_0 h0 b; *)
  let open Hacl.UInt128 in
  let b0' = b0 +^ times_wide_19 b5 in
  let b1' = b1 +^ times_wide_19 b6 in
  let b2' = b2 +^ times_wide_19 b7 in
  let b3' = b3 +^ times_wide_19 b8 in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3'

let bound127 (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ (let open Hacl.UInt128 in
    v (get h b 0) < pow2 127 /\ v (get h b 1) < pow2 127 /\ v (get h b 2) < pow2 127
    /\ v (get h b 3) < pow2 127 /\ v (get h b 4) < pow2 127)

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
  freduce_degree_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_freduce_degree h0 h1 b *)

val mod_wide_2_51: a:s128 -> Tot (b:s128(* {v b = v a % pow2 51} *))
let mod_wide_2_51 a =
  let open Hacl.UInt128 in
  let mask = (Hacl.Cast.uint64_to_sint128 1uL) <<^ 51ul in
  (* cut (v mask = pow2 51 % pow2 platform_wide /\ pow2 51 >= 1);  *)
  (* Math.Lemmas.pow2_increases_1 platform_wide 51;  *)
  (* mod_lemma_1 (pow2 51) (pow2 platform_wide); *)
  let mask = mask -%^ (Hacl.Cast.uint64_to_sint128 1uL) in
  let res = a &^ mask in
  (* log_and_wide_lemma_3 a mask 51; *)
  res

private val div_wide_2_51: x:s128 -> Tot (y:s128{H128.v y = H128.v x / pow2 51 /\ H128.v y <= pow2 77})
let div_wide_2_51 x = pow2_minus 128 51; H128 (x >>^ 51ul)


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

let isCarriedWide (h0:mem) (h1:mem) (b:bigint_wide) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ (
      let open Hacl.UInt128 in
      let b0 = v (get h0 b 0) in
      let b1 = v (get h0 b 1) in
      let b2 = v (get h0 b 2) in
      let b3 = v (get h0 b 3) in
      let b4 = v (get h0 b 4) in
      let r0  = b0 / pow2 51 in
      let r1  = (b1 + r0) / pow2 51 in
      let r2  = (b2 + r1) / pow2 51 in
      let r3  = (b3 + r2) / pow2 51 in
      v (get h1 b 5) = (b4 + r3) / pow2 51
      /\ v (get h1 b 0) = b0 % pow2 51
      /\ v (get h1 b 1) = (b1 + r0)  % pow2 51
      /\ v (get h1 b 2) = (b2 + r1)  % pow2 51
      /\ v (get h1 b 3) = (b3 + r2)  % pow2 51
      /\ v (get h1 b 4) = (b4 + r3)  % pow2 51
    )

let u127 = x:s128{H128.v x < pow2 127}

private val carry_wide_1_0:
  b:bigint_wide{length b >= norm_length+1} ->
  b0:u127 -> b1:u127 -> b2:u127 -> b3:u127 -> b4:u127 ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ isCarriedWide_ h1 b0 b1 b2 b3 b4 b ))
let carry_wide_1_0 b b0 b1 b2 b3 b4 =
  pow2_lt_compat 39 38; pow2_lt_compat 63 39; pow2_double_sum 63;
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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val carry_wide_1_:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ isCarriedWide h0 h1 b))
let carry_wide_1_ b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  carry_wide_1_0 b b0 b1 b2 b3 b4

let carried_wide_1 (h:mem) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ (let open Hacl.UInt128 in
      v (get h b 0) < pow2 51
      /\ v (get h b 1) < pow2 51
      /\ v (get h b 2) < pow2 51
      /\ v (get h b 3) < pow2 51
      /\ v (get h b 4) < pow2 51
      /\ v (get h b 5) <= pow2 77)

val carry_wide_1:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound127 h b))
    (ensures (fun h0 _ h1 -> bound127 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length /\ carried_wide_1 h1 b))
let carry_wide_1 b =
  let h0 = HST.get() in
  carry_wide_1_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_1 h0 h1 b *)


let carried_wide_2 (h:mem) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ (let open Hacl.UInt128 in
      v (get h b 0) < pow2 84
      /\ v (get h b 1) < pow2 51
      /\ v (get h b 2) < pow2 51
      /\ v (get h b 3) < pow2 51
      /\ v (get h b 4) < pow2 51)

val carry_wide_2_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_wide_2 h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
      /\ isCarriedWide h0 h1 b))
let carry_wide_2_ b =
  pow2_lt_compat 63 42; pow2_lt_compat 63 26;
  carry_wide_1_ b


let carried_wide_3 (h:mem) (b:bigint_wide) : GTot Type0 =
  norm_wide h b /\ length b >= norm_length+1
  /\ (let open Hacl.UInt128 in // TODO fix constants
      v (get h b 5) <= 1
      /\ (v (get h b 5) = 1
      ==> (v (get h b 1) < pow2 16 /\ v (get h b 2) < pow2 16  /\ v (get h b 3) < pow2 16
	  /\ v (get h b 4) < pow2 16)))

val carry_wide_2:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_wide_2 h b))
    (ensures (fun h0 _ h1 -> carried_wide_2 h0 b /\ norm_wide h1 b /\ modifies_1 b h0 h1
	  /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length
	  /\ carried_wide_3 h1 b))
let carry_wide_2 b =
  let h0 = HST.get() in
  carry_wide_2_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_2 h0 h1 b *)


let carriedTopBottomWide (h0:mem) (h1:mem) (b:bigint_wide) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ (let open Hacl.UInt128 in
      v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b 5)
      /\ v (get h1 b 1) = v (get h0 b 1)
      /\ v (get h1 b 2) = v (get h0 b 2)
      /\ v (get h1 b 3) = v (get h0 b 3)
      /\ v (get h1 b 4) = v (get h0 b 4))

val carry_wide_top_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      /\ (let open Hacl.UInt128 in v (get h b 0) + 5 * v (get h b 5) < pow2 64 )))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ carriedTopBottomWide h0 h1 b))
let carry_wide_top_ b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- H128 (b0 +^ times_wide_19 b5)


val carry_wide_top_1:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_wide_1 h b))
    (ensures  (fun h0 _ h1 -> carried_wide_1 h0 b /\ carried_wide_2 h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime))
let carry_wide_top_1 b =
  let h0 = HST.get() in
  pow2_double_sum 38; pow2_double_sum 39;  pow2_double_sum 40;
  pow2_lt_compat 63 26;  pow2_lt_compat 63 41;
  carry_wide_top_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_top_1 h0 h1 b *)


let carried_wide_4 (h:mem) (b:bigint_wide) : GTot Type0 =
  live h b
  /\ (let open Hacl.UInt128 in
      v (get h b 0) < pow2 51 + 19
      /\ v (get h b 1) < pow2 51
      /\ (v (get h b 0) >= pow2 51 ==> v (get h b 1) < pow2 16 // TODO: fix constant)
      /\ v (get h b 2) < pow2 51
      /\ v (get h b 3) < pow2 51
      /\ v (get h b 4) < pow2 51))

val carry_wide_top_2:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_wide_3 h b))
    (ensures  (fun h0 _ h1 -> carried_wide_3 h0 b /\ carried_wide_4 h1 b /\ modifies_1 b h0 h1
      /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime))
let carry_wide_top_2 b =
  let h0 = HST.get() in
  pow2_double_sum 0; pow2_double_sum 1;  pow2_double_sum 2;
  pow2_lt_compat 63 26;  pow2_lt_compat 63 3;
  carry_wide_top_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_top_2 h0 h1 b *)


let isCarriedWide01 (h0:mem) (h1:mem) (b:bigint_wide) =
  live h0 b /\ live h1 b
  /\ (let open Hacl.UInt128 in
      v (get h1 b 0) = v (get h0 b 0) % pow2 51
      /\ v (get h1 b 1) = v (get h0 b 1) + (v (get h0 b 0) / pow2 51)
      /\ v (get h1 b 2) = v (get h0 b 2)
      /\ v (get h1 b 3) = v (get h0 b 3)
      /\ v (get h1 b 4) = v (get h0 b 4))

private val carry_wide_0_to_1_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_wide_4 h b))
    (ensures  (fun h0 _ h1 -> isCarriedWide01 h0 h1 b /\ modifies_1 b h0 h1))
let carry_wide_0_to_1_ b =
  pow2_lt_compat 63 38; pow2_lt_compat 63 26; pow2_double_sum 63;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod_wide_2_51 b0 in
  let r0  = div_wide_2_51 b0 in
  b.(0ul) <- b0';
  b.(1ul) <- H128 (b1 +^ r0)

val carry_wide_0_to_1:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> carried_wide_4 h b))
    (ensures  (fun h0 _ h1 -> carried_wide_4 h0 b /\ modifies_1 b h0 h1 /\ norm_wide h1 b
      /\ eval_wide h1 b norm_length = eval_wide h0 b norm_length))
let carry_wide_0_to_1 b =
  let h0 = HST.get() in
  carry_wide_0_to_1_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_0_to_1 h0 h1 b *)


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

val times_19: x:s64(* {19 * v x < pow2 platform_wide} *) -> Tot (y:s64(* {v y = 19 * v x} *))
let times_19 x =
  let y = x <<^ 4ul in
  let z = x <<^ 1ul in
  x +%^ y +%^ z

val mod_2_51: a:s64 -> Tot (b:s64(* {v b = v a % pow2 51} *))
let mod_2_51 a =
  let open Hacl.UInt64 in
  let mask = (Hacl.Cast.uint64_to_sint64 1uL) <<^ 51ul in
  (* cut (v mask = pow2 51 % pow2 platform /\ pow2 51 >= 1);  *)
  (* Math.Lemmas.pow2_increases_1 platform 51;  *)
  (* mod_lemma_1 (pow2 51) (pow2 platform); *)
  let mask = mask -%^ (Hacl.Cast.uint64_to_sint64 1uL) in
  let res = a &^ mask in
  (* log_and_lemma_3 a mask 51; *)
  res

private val div_2_51: x:s64 -> Tot (y:s64{H64.v y = H64.v x / pow2 51 /\ H64.v y <= pow2 77})
let div_2_51 x = pow2_minus 64 51; H64 (x >>^ 51ul)


let isCarried_
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

let isCarried (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ (
      let b0 = v (get h0 b 0) in
      let b1 = v (get h0 b 1) in
      let b2 = v (get h0 b 2) in
      let b3 = v (get h0 b 3) in
      let b4 = v (get h0 b 4) in
      let r0  = b0 / pow2 51 in
      let r1  = (b1 + r0) / pow2 51 in
      let r2  = (b2 + r1) / pow2 51 in
      let r3  = (b3 + r2) / pow2 51 in
      v (get h1 b 5) = (b4 + r3) / pow2 51
      /\ v (get h1 b 0) = b0 % pow2 51
      /\ v (get h1 b 1) = (b1 + r0)  % pow2 51
      /\ v (get h1 b 2) = (b2 + r1)  % pow2 51
      /\ v (get h1 b 3) = (b3 + r2)  % pow2 51
      /\ v (get h1 b 4) = (b4 + r3)  % pow2 51
    )

let u633 = x:s64{H64.v x < pow2 63}

let bound63 (h:heap) (b:bigint) : GTot Type0 =
  live h b
  /\ v (get h b 0) < pow2 63 /\ v (get h b 1) < pow2 63 /\ v (get h b 2) < pow2 63
  /\ v (get h b 3) < pow2 63 /\ v (get h b 4) < pow2 63

private val carry_1_0:
  b:bigint{length b >= norm_length+1} ->
  b0:u633 -> b1:u633 -> b2:u633 -> b3:u633 -> b4:u633 ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ isCarried_ h1 b0 b1 b2 b3 b4 b ))
let carry_1_0 b b0 b1 b2 b3 b4 =
  pow2_lt_compat 39 38; pow2_lt_compat 63 39; pow2_double_sum 63;
  assert(forall x y. {:pattern (v x + v y)}(v x < pow2 127 /\ v y <= pow2 77)
    ==> v x + v y < pow2 128);
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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val carry_1_:
  b:bigint{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ isCarried h0 h1 b))
let carry_1_ b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  carry_1_0 b b0 b1 b2 b3 b4

let carried_1 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 51
  /\ v (get h b 1) < pow2 51
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51
  /\ v (get h b 5) <= pow2 77

val carry_1:
  b:bigint{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b (norm_length+1) = eval h0 b norm_length /\ carried_1 h1 b))
let carry_1 b =
  let h0 = HST.get() in
  carry_1_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_1 h0 h1 b *)


let carried_2 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 84
  /\ v (get h b 1) < pow2 51
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51

val carry_2_:
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_2 h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ isCarried h0 h1 b))
let carry_2_ b =
  pow2_lt_compat 63 42; pow2_lt_compat 63 26;
  carry_1_ b


let carried_3 (h:mem) (b:bigint) : GTot Type0 =
  norm h b /\ length b >= norm_length+1
  /\ v (get h b 5) <= 1
  /\ (v (get h b 5) = 1
      ==> (v (get h b 1) < pow2 16 /\ v (get h b 2) < pow2 16  /\ v (get h b 3) < pow2 16
	  /\ v (get h b 4) < pow2 16))

val carry_2:
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_2 h b))
    (ensures (fun h0 _ h1 -> carried_2 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_3 h1 b))
let carry_2 b =
  let h0 = HST.get() in
  carry_2_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_2 h0 h1 b *)


let carriedTopBottom (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)

val carry_top_:
  b:bigint ->
  Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      /\ v (get h b 0) + 5 * v (get h b 5) < pow2 64 ))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ carriedTopBottom h0 h1 b))
let carry_top_ b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- b0 +^ times_19 b5


val carry_top_1:
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_1 h b))
    (ensures  (fun h0 _ h1 -> carried_1 h0 b /\ carried_2 h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let carry_top_1 b =
  let h0 = HST.get() in
  pow2_double_sum 38; pow2_double_sum 39;  pow2_double_sum 40;
  pow2_lt_compat 63 26;  pow2_lt_compat 63 41;
  carry_top_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_top_1 h0 h1 b *)


let carried_4 (h:mem) (b:bigint) : GTot Type0 =
  live h b
  /\ v (get h b 0) < pow2 51 + 19
  /\ v (get h b 1) < pow2 51
  /\ (v (get h b 0) >= pow2 51 ==> v (get h b 1) < pow2 16 // TODO: fix constant)
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51)

val carry_top_2:
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_3 h b))
    (ensures  (fun h0 _ h1 -> carried_3 h0 b /\ carried_4 h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let carry_top_2 b =
  let h0 = HST.get() in
  pow2_double_sum 0; pow2_double_sum 1;  pow2_double_sum 2;
  pow2_lt_compat 63 26;  pow2_lt_compat 63 3;
  carry_top_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_top_2 h0 h1 b *)


let isCarried01 (h0:mem) (h1:mem) (b:bigint) =
  live h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) % pow2 51
  /\ v (get h1 b 1) = v (get h0 b 1) + (v (get h0 b 0) / pow2 51)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)

private val carry_0_to_1_:
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_4 h b))
    (ensures  (fun h0 _ h1 -> isCarried01 h0 h1 b /\ modifies_1 b h0 h1))
let carry_0_to_1_ b =
  pow2_lt_compat 63 38; pow2_lt_compat 63 26; pow2_double_sum 63;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod_2_51 b0 in
  let r0  = div_2_51 b0 in
  b.(0ul) <- b0';
  b.(1ul) <- b1 +^ r0

val carry_0_to_1:
  b:bigint ->
  Stack unit
    (requires (fun h -> carried_4 h b))
    (ensures  (fun h0 _ h1 -> carried_4 h0 b /\ modifies_1 b h0 h1 /\ norm h1 b
      /\ eval h1 b norm_length = eval h0 b norm_length))
let carry_0_to_1 b =
  let h0 = HST.get() in
  carry_0_to_1_ b(* ; *)
  (* let h1 = HST.get() in *)
  (* lemma_carry_0_to_1 h0 h1 b *)


val freduce_coefficients:
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> bound63 h b))
    (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
let freduce_coefficients b =
  carry_1 b;
  carry_top_1 b;
  carry_2 b;
  carry_top_2 b;
  carry_0_to_1 b


(* Not verified *)
val normalize:
  b:bigint ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let normalize b =
  let two51m1 = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffffuL) in // pow2 51 - 1
  let two51m19 = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffeduL) in // pow2 51 - 19
  let b4 = b.(4ul) in
  let b3 = b.(3ul) in
  let b2 = b.(2ul) in
  let b1 = b.(1ul) in
  let b0 = b.(0ul) in
  let mask = eq_mask b4 two51m1 in
  let mask = mask &^ (eq_mask b3 two51m1) in
  let mask = mask &^ (eq_mask b2 two51m1) in
  let mask = mask &^ (eq_mask b1 two51m1) in
  let mask = mask &^ (gte_mask b0 two51m19) in
  let sub_mask = mask &^ two51m1 in
  let sub_mask2 = mask &^ two51m19 in
  // Conditionally substract 2^255 - 19
  b.(4ul) <- (b4 -%^ sub_mask);
  b.(3ul) <- (b3 -%^ sub_mask);
  b.(2ul) <- (b2 -%^ sub_mask);
  b.(1ul) <- (b1 -%^ sub_mask);
  b.(0ul) <- (b0 -%^ sub_mask2)

(* val freduce_coefficients: b:bigint{length b >= norm_length + 1} -> Stack unit *)
(*   (requires (fun h -> bound63 h b)) *)
(*   (ensures (fun h0 _ h1 -> bound63 h0 b /\ norm h1 b /\ modifies_1 b h0 h1 *)
(*     /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime *)
(*     )) *)
(* let freduce_coefficients b = *)
(*   carry_1 b; *)
(*   carry_top_1 b; *)
(*   carry_2 b; *)
(*   carry_top_2 b; *)
(*   carry_0_to_1 b *)


(* val modulo: b:bigint -> Stack unit *)
(*   (requires (fun h -> live h b /\ satisfiesModuloConstraints h b)) *)
(*   (ensures (fun h0 _ h1 -> live h0 b /\ satisfiesModuloConstraints h0 b /\ norm h1 b /\ modifies_1 b h0 h1 *)
(*     /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime)) *)
(* let modulo b = *)
(*   freduce_degree b; *)
(*   freduce_coefficients_wide b *)

(*
val carry:
  b:bigint_wide -> ctr:u32{U32.v ctr <= norm_length} -> Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      (* carriable h b (w ctr) /\ carried h b (w ctr) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* /\ carried h1 b norm_length /\ untouched_2 h0 h1 b (w ctr) *)
      (* /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b (norm_length+1) *)
      (* /\ modifies_1 b h0 h1 *)
    ))
let rec carry b i =
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  let open Hacl.UInt128 in
  if U32 (i =^ nlength) then ()
  else begin
    let bi = b.(i) in
    let ri = mod2_51 bi in
    (* assert(v ri < pow2 (templ (w i)));  *)
    b.(i) <- ri;
    (* let h1 = ST.get() in *)
    (* upd_lemma h0 h1 b i ri;  *)
    let c = bi >>^ 51ul in
    // In the spec of >>
    (* admitP(True /\ v c < pow2 (platform_wide - 51));  *)
    let bip1 = b.(U32 (i +^ 1ul)) in
    (* assert(v bip1 = v (get h1 b (w i+1)));  *)
    (* assert(v bip1 < pow2 (platform_wide - 1));  *)
    (* auxiliary_lemma_1 bip1 c;  *)
    (* let z = bip1 + c in *)
    b.(U32 (i +^1ul)) <- (bip1 +%^ c)(* ; *)
    (* let h2 = ST.get() in *)
    (* upd_lemma h1 h2 b (i+|1ul) z;  *)
    (* eval_carry_lemma h0 b h2 b (w i);  *)
    (* cut (forall (j:nat). (j > w i+1 /\ j <= norm_length) ==> v (get h2 b j) < pow2 (platform_wide - 1)); *)
    (* carry b (i+|1ul) *)
  end

val carry_top_to_0: b:bigint_wide -> Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      (* carried h b norm_length /\  *)
      (* /\ v (get h b 0) + 19 * v (get h b norm_length) < pow2 (platform_wide-1) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* /\ carried h0 b norm_length /\ carried' h1 b 1 *)
      (* /\ eval_wide h1 b norm_length % (reveal prime) = eval_wide h0 b (norm_length+1) % (reveal prime) *)
      (* /\ v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b norm_length) *)
      (* /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==>  *)
	  (* v (get h1 b i) = v (get h0 b i))  *)
    ))
let carry_top_to_0 b =
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  let open Hacl.UInt128 in
  let b0 = b.(0ul) in
  let btop = b.(nlength) in
  let btop_19 = times_19 btop in
  b.(0ul) <- (b0 +%^ btop_19)(* ; *)
  (* let h1 = ST.get() in *)
  (* freduce_degree_lemma h0 h1 b 0 *)

val carry2:
  b:bigint_wide -> ctr:u32{U32.v ctr <= norm_length} -> Stack unit
  (requires (fun h -> live h b /\ length b >= norm_length+1
    (* carriable2 h b (w ctr) *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* carriable2 h0 b (w ctr) /\ carriable2 h1 b norm_length *)
    (* /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b (norm_length+1) *)
    (* /\ modifies_1 b h0 h1 *)
  ))
let rec carry2 b i =
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  let open Hacl.UInt128 in
  if U32 (i =^ nlength) then ()
  else begin
    let bi = b.(i) in
    let ri = mod2_51 bi in
    (* assert(v ri < pow2 (templ (w i))); *)
    b.(i) <- ri;
    (* let h1 = ST.get() in *)
    (* upd_lemma h0 h1 b i ri;  *)
    let bip1 = b.(U32 (i +^ 1ul)) in
    let c = bi >>^ 51ul in
    (* helper_lemma_21 bi; *)
    (* helper_lemma_20 bip1 c;  *)
    (* // In the spec of >> *)
    (* admitP(True /\ v c < pow2 (platform_wide - 51));  *)
    (* assert(v bip1 = v (get h1 b (i+1)));  *)
    (* pow2_increases_lemma (platform_wide-1) 51; *)
    (* assert(v bip1 < pow2 (platform_wide - 1));  *)
    (* auxiliary_lemma_1 bip1 c;  *)
    (* let z = bip1 |+ c in  *)
    (* cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 51);  *)
    (* cut (v z >= pow2 51 ==> v c = 1);  *)
    (* cut (v c > 0 ==> v (get h0 b (w i)) / (pow2 51) > 0 ==> v (get h0 b (w i)) >= pow2 51);  *)
    (* cut (v z >= pow2 51 ==> v (get h1 b (w i)) < pow2 32);  *)
    b.(U32 (i +^ 1ul)) <- (bip1 +%^ c);
    (* let h2 = ST.get() in *)
    (* (\* upd_lemma h1 h2 b (i+|1ul) z;  *\) *)
    (* cut (v z >= pow2 51 ==> v c = 1 /\ True);  *)
    (* eval_carry_lemma h0 b h2 b (w i); *)
    carry2 b (U32 (i+^1ul))
  end

val last_carry: b:bigint_wide -> Stack unit
  (requires (fun h -> live h b /\ length b >= norm_length+1
    (* carriable2 h b norm_length *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
  (* carriable2 h0 b norm_length /\ norm_wide h1 b *)
  (*   /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime *)
  (*   /\ modifies_1 b h0 h1 *)
  ))
let last_carry b =
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  let open Hacl.UInt128 in
  let b0 = b.(0ul) in
  let btop = b.(nlength) in
  (* cut (v b0 < pow2 51 /\ v btop < 2);  *)
  (* pow2_5_lemma (); *)
  (* cut (19 * v btop < pow2 5 /\ True); *)
  (* pow2_increases_lemma 51 5; *)
  (* Math.Lemmas.pow2_double_sum 51; *)
  (* pow2_increases_lemma platform_wide 52; *)
  (* pow2_increases_lemma platform_wide 51; *)
  (* cut (v b0 + 19 * v btop < pow2 52 /\ True);  *)
  let btop_19 = times_19 btop in
  (* let bi = (b0 |+ btop_19) in *)
  (* upd_wide b 0 (b0 |+ btop_19);  *)
  b.(0ul) <- (b0 +%^ btop_19);
  (* let h1 = ST.get() in *)
  (* freduce_degree_lemma h0 h1 b 0;  *)
  b.(nlength) <- (Hacl.Cast.uint64_to_sint128 0uL);
  (* let h2 = ST.get() in *)
  (* eval_eq_lemma h1 h2 b b norm_length;  *)
  (* cut (eval_wide h2 b (norm_length+1) = eval_wide h1 b norm_length /\ True);  *)
  let bi = b.(0ul) in
  let ri = mod2_51 bi in
  b.(0ul) <- ri;
  (* let h3 = ST.get() in *)
  let c = bi >>^ 51ul in
  (* Math.Lemmas.pow2_exp_1 32 5; *)
  (* cut (v bi < pow2 51 + 19 /\ True);  *)
  (* cut (v bi >= pow2 51 ==> v (get h3 b 1) < pow2 32);  *)
  (* helper_lemma_30 b0 btop_19;  *)
  (* helper_lemma_32 bi; *)
  let bip1 = b.(1ul) in
  (* cut (v bi >= pow2 51 ==> v bip1 < pow2 32);  *)
  (* cut (v c = 1 ==> v bip1 < pow2 32);  *)
  (* cut (v c = (v b0 + v btop_19) / pow2 51 /\ v bip1 < pow2 51);  *)
  (* helper_lemma_33 bip1 c;  *)
  (* let z = bip1 |+ c in *)
  b.(1ul) <- (bip1 +%^ c)(* ; *)
  (* let h4 = ST.get() in *)
  (* eval_carry_lemma h2 b h4 b 0;  *)
  (* cut (True /\ v (get h4 b 1) < pow2 51); *)
  (* cut (norm_wide h4 b) *)

val freduce_coefficients:
  b:bigint_wide -> Stack unit
  (requires (fun h -> live h b /\ length b >= norm_length+1
    (* /\ carriable h b 0 *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* carriable h0 b 0 /\ norm_wide h1 b *)
    (* /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b norm_length % reveal prime *)
  ))
let freduce_coefficients b =
  (* let h = ST.get() in *)
  let open Hacl.UInt128 in
  b.(nlength) <- (Hacl.Cast.uint64_to_sint128 0uL);
  (* let h' = ST.get() in *)
  (* eval_eq_lemma h h' b b norm_length; *)
  (* eval_wide_def h' b (norm_length+1); *)
  (* cut (True /\ eval_wide h' b (norm_length+1) = eval_wide h b norm_length); *)
  carry b 0ul;
  (* let h = ST.get() in *)
  (* lemma_helper_40 h b; *)
  carry_top_to_0 b;
  (* let h1 = ST.get() in *)
  b.(nlength) <- (Hacl.Cast.uint64_to_sint128 0uL);
  let h2 = ST.get() in
  (* eval_eq_lemma h1 h2 b b norm_length; *)
  (* eval_wide_def h2 b (norm_length+1); *)
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let r0 = mod2_51 b0 in
  let c0 = b0 >>^ 51ul in
  (* lemma_helper_41 b0;  *)
  (* lemma_helper_42 b1 c0; *)
  (* let h = ST.get() in *)
  b.(0ul) <- r0;
  b.(1ul) <- b1 +%^ c0;
  (* let h' = ST.get() in *)
  (* eval_carry_lemma h b h' b 0;  *)
  carry2 b 1ul;
  last_carry b
