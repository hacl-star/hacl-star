(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --lax;
    other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst seq.fsi seqproperties.fst arr.fst ghost.fst axiomatic.fst intlib.fsti lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst
  --*)

module Modulo

(* 32/64 bits *)

open Parameters
open UInt
open Bigint

let op_Bar_Amp x y = log_and_wide x y
let op_Bar_Greater_Greater x y = shift_right_wide x y
let op_Bar_Plus x y = add_wide x y
let op_Bar_Star x y = mul_wide x y

val freduce_degree: b:biginteger (2*platform_size) -> ctr:nat -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let rec freduce_degree b ctr =
  match norm_length - 1 - ctr with
  | 0 -> ()
  | _ -> 
    let b1 = index b ctr in let b2 = index b (ctr+norm_length) in
    upd b ctr (2*platform_size) (b1 |+ (b2 |* (to_wide "19")));
    freduce_degree b (ctr+1)
  
val carry: 
  b:biginteger (2*platform_size) -> ctr:nat -> ST unit
  (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let rec carry b ctr =
  match 5 - ctr with
  | 0 -> ()
  | _ -> 
    let i = 2 * ctr in
    let bi = index b i in
    let ri = bi |& (to_wide "0x3ffffff") in
    upd b i (2*platform_size) (ri);
    let c = (bi |>> 26) in
    let bip1 = index b (i+1) in
    upd b (i+1) (2*platform_size) (bip1 |+ c);
    let bip1 = index b (i+1) in
    let rip1 = bip1 |& (to_wide "0x1ffffff") in
    upd b (i+1) (2*platform_size) (rip1);
    let c = (bip1 |>> 25) in
    let bip2 = index b (i+2) in
    upd b (i+2) (2*platform_size) (bip2 |+ c);
    carry b (ctr+1)

val carry_top_to_0:
  b:biginteger (2*platform_size) -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let carry_top_to_0 b =
  let btop = index b norm_length in
  let b0 = index b 0 in
  upd b 0 (2*platform_size) (b0 |+ (btop |* (to_wide "19")))


val normalize:
  b:biginteger platform_size -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let normalize b =
  let two26m1 = to_limb "0x3ffffff" in
  let two25m1 = to_limb "0x1ffffff" in
  let two26m19 = to_limb "0x3ffffed" in
  let mask = eq_limb (index #platform_size b 9) two25m1 in
  let mask = log_and_std mask (eq_limb (index #platform_size b 8) two26m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 7) two25m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 6) two26m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 5) two25m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 4) two26m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 3) two25m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 2) two26m1) in
  let mask = log_and_std mask (eq_limb (index #platform_size b 1) two25m1) in
  let mask = log_and_std mask (gte_limb (index #platform_size b 0) two26m19) in
  
  let sub_mask26 = log_and_std mask two26m1 in
  let sub_mask25 = log_and_std mask two25m1 in
  // Conditionally substract 2^255 - 19 
  let b9 = index #platform_size b 9 in
  upd #platform_size b 9 platform_size (sub_std b9 sub_mask25);
  let b8 = index #platform_size b 8 in
  upd #platform_size b 8 platform_size (sub_std b8 sub_mask26);
  let b7 = index #platform_size b 7 in
  upd #platform_size b 7 platform_size (sub_std b7 sub_mask25);
  let b6 = index #platform_size b 6 in
  upd #platform_size b 6 platform_size (sub_std b6 sub_mask26);
  let b5 = index #platform_size b 5 in
  upd #platform_size b 5 platform_size (sub_std b5 sub_mask25);
  let b4 = index #platform_size b 4 in
  upd #platform_size b 4 platform_size (sub_std b4 sub_mask26);
  let b3 = index #platform_size b 3 in
  upd #platform_size b 3 platform_size (sub_std b3 sub_mask25);
  let b2 = index #platform_size b 2 in
  upd #platform_size b 2 platform_size (sub_std b2 sub_mask26);
  let b1 = index #platform_size b 1 in
  upd #platform_size b 1 platform_size (sub_std b1 sub_mask25);
  let b0 = index #platform_size b 0 in
  upd #platform_size b 0 platform_size (sub_std b0 (log_and_std mask two26m19))


val add_big_zero:
  output:biginteger platform_size -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let add_big_zero b =
  let two27m38 = to_limb "0x7ffffda" in
  let two27m2 =  to_limb "0x7fffffe" in
  let two26m2 =  to_limb "0x3fffffe" in
  let b0 = index b 0 in
  upd b 0 platform_size (add_std b0 two27m38);
  let b1 = index b 1 in
  upd b 1 platform_size (add_std b1 two26m2); 
  let b2 = index b 2 in
  upd b 2 platform_size (add_std b2 two27m2); 
  let b3 = index b 3 in
  upd b 3 platform_size (add_std b3 two26m2); 
  let b4 = index b 4 in
  upd b 4 platform_size (add_std b4 two27m2); 
  let b5 = index b 5 in
  upd b 5 platform_size (add_std b5 two26m2); 
  let b6 = index b 6 in
  upd b 6 platform_size (add_std b6 two27m2); 
  let b7 = index b 7 in
  upd b 7 platform_size (add_std b7 two26m2); 
  let b8 = index b 8 in
  upd b 8 platform_size (add_std b8 two27m2); 
  let b9 = index b 9 in
  upd b 9 platform_size (add_std b9 two26m2)
