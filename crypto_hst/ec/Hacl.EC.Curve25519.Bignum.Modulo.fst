module Hacl.EC.Curve25519.Bignum.Modulo

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64
open Hacl.SBuffer
open Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint


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

val times_19: x:s128(* {19 * v x < pow2 platform_wide} *) -> Tot (y:s128(* {v y = 19 * v x} *))
let times_19 x =
  let open Hacl.UInt128 in
  let y = x <<^ 4ul in
  let z = x <<^ 1ul in
  x +%^ y +%^ z

val freduce_degree': b:bigint_wide -> ctr:u32{U32.v ctr < norm_length - 1} -> Stack unit
    (requires (fun h -> live h b /\ length b >= 2*norm_length-1
      (* /\ reducible' h b (w ctr) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* untouched' h0 h1 b (w ctr) /\ times19' h0 h1 b (w ctr) *)
      (* /\ eval_wide h1 b (norm_length) % reveal prime = eval_wide h0 b (norm_length+1+w ctr) % reveal prime *)
      (* /\ modifies_1 b h0 h1 *)
    ))
let rec freduce_degree' b ctr' =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  let open Hacl.UInt128 in
  if U32 (ctr' =^ 0ul) then begin
    let b5ctr = index b (nlength) in
    let bctr = index b 0ul in
    let b5ctr = times_19 b5ctr in
    let bctr = bctr +%^ b5ctr in
    b.(0ul) <- bctr(* ; *)
    (* let h1 = HST.get() in *)
    (* upd_lemma h0 h1 b 0ul bctr; *)
    (* freduce_degree_lemma h0 h1 b 0; *)
    (* cut (True /\ eval_wide h0 b (norm_length+1+0) % reveal prime = eval_wide h1 b (norm_length+0) % reveal prime); *)
    (* cut (True /\ eval_wide h0 b (norm_length+1) % reveal prime = eval_wide h1 b (norm_length+0) % reveal prime) *)
  end
  else begin
    let ctr = ctr' in
    let b5ctr = b.(U32 (ctr +^ nlength)) in
    let bctr = b.(ctr) in
    let b5ctr = times_19 b5ctr in
    let bctr = bctr +%^ b5ctr in
    b.(ctr) <- bctr;
    (* let h1 = HST.get() in *)
    (* upd_lemma h0 h1 b ctr bctr; *)
    (* freduce_degree_lemma h0 h1 b (w ctr);  *)
    (* cut (True /\ eval_wide h0 b (norm_length+1+w ctr) % reveal prime = eval_wide h1 b (norm_length+w ctr) % reveal prime); *)
    (* cut(reducible' h1 b (w ctr-1));  *)
    freduce_degree' b (U32 (ctr -^ 1ul))(* ; *)
    (* let h2 = HST.get() in  *)
    (* cut (forall (i:nat). {:pattern (v (get h1 b i))} (i > w ctr /\ i < 2*norm_length-1) ==> *)
    (* 	   v (get h1 b i) = v (get h0 b i));  *)
    (* cut(untouched' h0 h2 b (w ctr)); *)
    (* cut (times19' h0 h2 b (w ctr))  *)
  end

val freduce_degree: b:bigint_wide -> Stack unit
  (requires (fun h -> live h b /\ length b >= 2*norm_length-1
    (* /\ satisfies_modulo_constraints h b *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* live h0 b /\ live h1 b /\ satisfies_modulo_constraints h0 b *)
    (* /\ length b >= 2*norm_length - 1 *)
    (* /\ length b = length b /\ modifies_1 b h0 h1 /\ length b >= norm_length+1 *)
    (* /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==>  *)
    (* 	v (get h1 b i) < pow2 (platform_wide - 1)) *)
    (* /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (2*norm_length-1) % reveal prime *)
  ))
let freduce_degree b =
  (* let h0 = HST.get() in *)
  (* aux_lemma_4 h0 b;  *)
  freduce_degree' b (U32 (nlength -^2ul))
  (* let h1 = HST.get() in *)
  (* aux_lemma_5 h0 h1 b *)

val mod2_51: a:s128 -> Tot (b:s128(* {v b = v a % pow2 51} *))
let mod2_51 a =
  let open Hacl.UInt128 in
  let mask = (of_string "1") <<^ 51ul in
  (* cut (v mask = pow2 51 % pow2 platform_wide /\ pow2 51 >= 1);  *)
  (* Math.Lemmas.pow2_increases_1 platform_wide 51;  *)
  (* mod_lemma_1 (pow2 51) (pow2 platform_wide); *)
  let mask = mask -%^ (of_string "1") in
  let res = a &^ mask in
  (* log_and_wide_lemma_3 a mask 51; *)
  res

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
  (* let h0 = HST.get() in *)
  let open Hacl.UInt128 in
  if U32 (i =^ nlength) then ()
  else begin
    let bi = b.(i) in
    let ri = mod2_51 bi in
    (* assert(v ri < pow2 (templ (w i)));  *)
    b.(i) <- ri;
    (* let h1 = HST.get() in *)
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
    (* let h2 = HST.get() in *)
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
  (* let h0 = HST.get() in *)
  let open Hacl.UInt128 in
  let b0 = b.(0ul) in
  let btop = b.(nlength) in
  let btop_19 = times_19 btop in
  b.(0ul) <- (b0 +%^ btop_19)(* ; *)
  (* let h1 = HST.get() in *)
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
  (* let h0 = HST.get() in *)
  let open Hacl.UInt128 in
  if U32 (i =^ nlength) then ()
  else begin
    let bi = b.(i) in
    let ri = mod2_51 bi in
    (* assert(v ri < pow2 (templ (w i))); *)
    b.(i) <- ri;
    (* let h1 = HST.get() in *)
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
    (* let h2 = HST.get() in *)
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
  (* let h0 = HST.get() in *)
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
  (* let h1 = HST.get() in *)
  (* freduce_degree_lemma h0 h1 b 0;  *)
  b.(nlength) <- (of_string "0");
  (* let h2 = HST.get() in *)
  (* eval_eq_lemma h1 h2 b b norm_length;  *)
  (* cut (eval_wide h2 b (norm_length+1) = eval_wide h1 b norm_length /\ True);  *)
  let bi = b.(0ul) in
  let ri = mod2_51 bi in
  b.(0ul) <- ri;
  (* let h3 = HST.get() in *)
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
  (* let h4 = HST.get() in *)
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
  (* let h = HST.get() in *)
  let open Hacl.UInt128 in
  b.(nlength) <- (of_string "0");
  (* let h' = HST.get() in *)
  (* eval_eq_lemma h h' b b norm_length; *)
  (* eval_wide_def h' b (norm_length+1); *)
  (* cut (True /\ eval_wide h' b (norm_length+1) = eval_wide h b norm_length); *)
  carry b 0ul;
  (* let h = HST.get() in *)
  (* lemma_helper_40 h b; *)
  carry_top_to_0 b;
  (* let h1 = HST.get() in *)
  b.(nlength) <- (of_string "0");
  let h2 = HST.get() in
  (* eval_eq_lemma h1 h2 b b norm_length; *)
  (* eval_wide_def h2 b (norm_length+1); *)
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let r0 = mod2_51 b0 in
  let c0 = b0 >>^ 51ul in
  (* lemma_helper_41 b0;  *)
  (* lemma_helper_42 b1 c0; *)
  (* let h = HST.get() in *)
  b.(0ul) <- r0;
  b.(1ul) <- b1 +%^ c0;
  (* let h' = HST.get() in *)
  (* eval_carry_lemma h b h' b 0;  *)
  carry2 b 1ul;
  last_carry b

val add_big_zero_core: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\norm h b *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ norm h0 b /\ live h1 b /\ length b = length b *)
    (* 			 /\ filled h1 b *)
    (* 			 /\ vv (get h1 b 0) = vv (get h0 b 0) + (pow2 52 - 38) *)
    (* 			 /\ vv (get h1 b 1) = vv (get h0 b 1) + (pow2 52 - 2) *)
    (* 			 /\ vv (get h1 b 2) = vv (get h0 b 2) + (pow2 52 - 2) *)
    (* 			 /\ vv (get h1 b 3) = vv (get h0 b 3) + (pow2 52 - 2) *)
    (* 			 /\ vv (get h1 b 4) = vv (get h0 b 4) + (pow2 52 - 2) *)
    (* 			 /\ modifies_1 b h0 h1 *)
    ))
let add_big_zero_core b =
  (* let h0 = HST.get() in *)
  let two52m38 = (Hacl.Cast.uint64_to_sint64 0xfffffffffffdauL) in // pow2 52 - 38
  let two52m2 =  (Hacl.Cast.uint64_to_sint64 0xffffffffffffeuL) in // pow2 52 - 2
  (* admitP(vv two52m38 = pow2 52 - 38 /\ vv two52m2 = pow2 52 - 2);  *)
  let b0 = b.(0ul) in
  (* cut(True /\ vv b0 = vv (get h0 b 0)); *)
  (* cut(forall (i:nat). {:pattern (vv (get h0 b i))} i < norm_length ==> (vv (get h0 b i)) < pow2 (templ i));  *)
  (* cut(forall (i:nat). i < norm_length ==> vv (get h0 b i) < pow2 (templ i));  *)
  (* cut (vv b0 < pow2 51 /\ vv two52m38 < pow2 52);  *)
  (* addition_lemma b0 51 two52m38 52; *)
  (* Math.Lemmas.pow2_increases_1 platform_size 53;  *)
  b.(0ul) <- (b0 +%^ two52m38);
  (* let h1 = HST.get() in *)
  (* upd_lemma h0 h1 b 0ul (S64.add b0 two52m38);  *)
  let b1 = b.(1ul) in
  (* cut (vv b1 = vv (get h0 b 1) /\ vv b1 < pow2 51 /\ vv two52m2 < pow2 52);  *)
  (* addition_lemma b1 51 two52m2 52; *)
  (* Math.Lemmas.pow2_increases_1 platform_size 53;  *)
  b.(1ul) <-(b1 +%^ two52m2);
  (* let h2 = HST.get() in *)
  (* upd_lemma h1 h2 b 1ul (S64.add b1 two52m2);  *)
  let b2 = b.(2ul) in
  (* cut (vv b2 = vv (get h1 b 2) /\ vv (get h1 b 2) = vv (get h0 b 2) /\ vv b2 < pow2 51); *)
  (* addition_lemma b2 51 two52m2 52; *)
  (* Math.Lemmas.pow2_increases_1 platform_size 53;  *)
  b.(2ul) <- (b2 +%^ two52m2);
  (* let h3 = HST.get() in *)
  (* upd_lemma h2 h3 b 2ul (S64.add b2 two52m2);  *)
  let b3 = index b 3ul in
  (* cut (vv b3 = vv (get h2 b 3) /\ vv (get h2 b 3) = vv (get h1 b 3) /\ vv (get h1 b 3) = vv (get h0 b 3) /\ vv b3 < pow2 51); *)
  (* addition_lemma b3 51 two52m2 52; *)
  (* Math.Lemmas.pow2_increases_1 platform_size 53;  *)
  b.(3ul) <- (b3 +%^ two52m2);
  (* let h4 = HST.get() in *)
  (* upd_lemma h3 h4 b 3ul (S64.add b3 two52m2);  *)
  let b4 = b.(4ul) in
  (* cut (vv b4 = vv (get h3 b 4) /\ vv (get h3 b 4) = vv (get h2 b 4) /\ vv (get h2 b 4) = vv (get h1 b 4) /\ vv (get h1 b 4) = vv (get h0 b 4) /\ vv b4 < pow2 51); *)
  (* addition_lemma b4 51 two52m2 52; *)
  (* Math.Lemmas.pow2_increases_1 platform_size 53;  *)
  b.(4ul) <- (b4 +%^ two52m2)
  (* let h5 = HST.get() in  *)
  (* upd_lemma h4 h5 b 4ul (S64.add b4 two52m2); *)
  (* cut (vv (get h5 b 0) = vv (get h0 b 0) + (pow2 52 - 38) /\ True);  *)
  (* cut (vv (get h5 b 1) = vv (get h0 b 1) + (pow2 52 - 2) /\ True);  *)
  (* cut (vv (get h5 b 2) = vv (get h0 b 2) + (pow2 52 - 2) /\ True);  *)
  (* cut (vv (get h5 b 3) = vv (get h0 b 3) + (pow2 52 - 2) /\ True);  *)
  (* cut (vv (get h5 b 4) = vv (get h0 b 4) + (pow2 52 - 2) /\ True);  *)
  (* cut (forall (i:nat). {:pattern (v (get h5 b i))} i < 5 ==> v (get h5 b i) < pow2 ndiff);  *)
  (* aux_lemma_1 ();  *)
  (* cut (forall (i:nat). {:pattern (v (get h5 b i))} i < 5 ==> v (get h5 b i) >= pow2 ndiff');  *)
  (* cut (norm_length = 5 /\ True);  *)
  (* cut(filled h5 b) *)

val add_big_zero: b:bigint -> Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let add_big_zero b =
  (* let h0 = HST.get() in *)
  add_big_zero_core b(* ; *)
  (* let h1 = HST.get() in *)
  (* add_big_zero_lemma h0 h1 b *)


(* Not verified *)
val normalize: b:bigint -> Stack unit
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
