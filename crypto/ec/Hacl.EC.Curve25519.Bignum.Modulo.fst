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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

inline_for_extraction val times_wide_19: s128 -> Tot (s128)
inline_for_extraction let times_wide_19 x =
  let open Hacl.UInt128 in
  let y = x <<^ 4ul in
  let z = x <<^ 1ul in
  x +%^ y +%^ z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val freduce_degree_:
  b:bigint_wide{length b >= 2*norm_length-1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
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
  let open Hacl.UInt128 in
  let b0' = b0 +%^ times_wide_19 b5 in
  let b1' = b1 +%^ times_wide_19 b6 in
  let b2' = b2 +%^ times_wide_19 b7 in
  let b3' = b3 +%^ times_wide_19 b8 in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3'


val freduce_degree:
  b:bigint_wide{length b >= 2*norm_length - 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let freduce_degree b =
  freduce_degree_ b

inline_for_extraction val mod_wide_2_51: a:s128 -> Tot s128
inline_for_extraction let mod_wide_2_51 a =
  let mask = (Hacl.Cast.uint64_to_sint128 0x7ffffffffffffuL) in
  H128 (a &^ mask)


inline_for_extraction private val div_wide_2_51: x:s128 -> Tot (s128)
inline_for_extraction private let div_wide_2_51 x = 
  let open Hacl.UInt128 in
  (x >>^ 51ul)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private val carry_wide_1_0:
  b:bigint_wide{length b >= norm_length+1} ->
  b0:H128.t -> b1:H128.t -> b2:H128.t -> b3:H128.t -> b4:H128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_1_0 b b0 b1 b2 b3 b4 =
  let b0' = mod_wide_2_51 b0 in
  let r0  = div_wide_2_51 b0 in
  let open Hacl.UInt128 in
  let b1' = mod_wide_2_51 (b1 +%^ r0) in
  let r1  = div_wide_2_51 (b1 +%^ r0) in
  let b2' = mod_wide_2_51 (b2 +%^ r1) in
  let r2  = div_wide_2_51 (b2 +%^ r1) in
  let b3' = mod_wide_2_51 (b3 +%^ r2) in
  let r3  = div_wide_2_51 (b3 +%^ r2) in
  let b4' = mod_wide_2_51 (b4 +%^ r3) in
  let b5' = div_wide_2_51 (b4 +%^ r3) in
  update_wide_6 b b0' b1' b2' b3' b4' b5'


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val carry_wide_1_:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
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
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_1 b =
  carry_wide_1_ b


val carry_wide_2_:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_2_ b =
  carry_wide_1_ b


val carry_wide_2:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_2 b =
  carry_wide_2_ b

val carry_wide_top_:
  b:bigint_wide ->
  Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_top_ b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- H128 (b0 +%^ times_wide_19 b5)


val carry_wide_top_1:
  b:bigint_wide{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_top_1 b =
  carry_wide_top_ b


val carry_wide_top_2:
  b:bigint_wide{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_top_2 b =
  carry_wide_top_ b


private val carry_wide_0_to_1_:
  b:bigint_wide{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_wide_0_to_1_ b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod_wide_2_51 b0 in
  let r0  = div_wide_2_51 b0 in
  b.(0ul) <- b0';
  b.(1ul) <- H128 (b1 +%^ r0)


val carry_wide_0_to_1:
  b:bigint_wide{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let carry_wide_0_to_1 b =
  carry_wide_0_to_1_ b


val freduce_coefficients_wide:
  b:bigint_wide{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let freduce_coefficients_wide b =
  carry_wide_1 b;
  carry_wide_top_1 b;
  carry_wide_2 b;
  carry_wide_top_2 b;
  carry_wide_0_to_1 b


(*******************************************************************************)

inline_for_extraction val times_19: x:s64 -> Tot s64
inline_for_extraction let times_19 x =
  let y = x <<^ 4ul in
  let z = x <<^ 1ul in
  x +%^ y +%^ z


inline_for_extraction val mod_2_51: a:s64 -> Tot s64
inline_for_extraction let mod_2_51 a =
  let open Hacl.UInt64 in
  let mask = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffffuL) in
  a &^ mask


inline_for_extraction private val div_2_51: x:s64 -> Tot s64
inline_for_extraction private let div_2_51 x =
  let open Hacl.UInt64 in
  (x >>^ 51ul)


private val carry_1_0':
  b:bigint{length b >= norm_length+1} ->
  b0:H64.t -> b1:H64.t -> b2:H64.t -> b3:H64.t -> b4:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_1_0' b b0 b1 b2 b3 b4 =
  let b0' = mod_2_51 b0 in
  let r0  = div_2_51 b0 in
  let b1' = mod_2_51 (b1 +%^ r0) in
  let r1  = div_2_51 (b1 +%^ r0) in
  let b2' = mod_2_51 (b2 +%^ r1) in
  let r2  = div_2_51 (b2 +%^ r1) in
  let b3' = mod_2_51 (b3 +%^ r2) in
  let r3  = div_2_51 (b3 +%^ r2) in
  let b4' = mod_2_51 (b4 +%^ r3) in
  let b5' = div_2_51 (b4 +%^ r3) in
  update_6 b b0' b1' b2' b3' b4' b5'


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val carry_1_':
  b:bigint{length b >= norm_length+1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
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
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_1' b =
  carry_1_' b


val carry_2_':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_2_' b =
  carry_1_' b


val carry_2':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_2' b =
  carry_2_' b


val carry_top_':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_top_' b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- b0 +%^ times_19 b5


val carry_top_1':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_top_1' b =
  carry_top_' b


val carry_top_2':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_top_2' b =
  carry_top_' b



#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val carry_0_to_1_':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_0_to_1_' b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod_2_51 b0 in
  let r0  = div_2_51 b0 in
  b.(0ul) <- b0';
  b.(1ul) <- b1 +%^ r0


val carry_0_to_1':
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let carry_0_to_1' b =
  carry_0_to_1_' b


val freduce_coefficients:
  b:bigint{length b >= norm_length + 1} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let freduce_coefficients b =
  carry_1' b;
  carry_top_1' b;
  carry_2' b;
  carry_top_2' b;
  carry_0_to_1' b


#reset-options "--initial_fuel 0 --max_fuel 9 --z3timeout 100"

val normalize:
  b:bigint ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let normalize b =
  let two51m1 = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffffuL) in
  let two51m19 = (Hacl.Cast.uint64_to_sint64 0x7ffffffffffeduL) in
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
  let mask  = mask4 &^ mask3 &^ mask2 &^ mask1 &^ mask0 in
  let b0' = (b0 -%^ (two51m19 &^ mask)) in
  let b1' = (b1 -%^ (b1 &^ mask)) in
  let b2' = (b2 -%^ (b2 &^ mask)) in
  let b3' =  (b3 -%^ (b3 &^ mask)) in
  let b4' =  (b4 -%^ (b4 &^ mask)) in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3';
  b.(4ul) <- b4'

