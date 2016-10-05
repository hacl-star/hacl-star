module Hacl.Symmetric.Poly1305.Bignum

open FStar.Mul
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.Buffer
open Math.Axioms
open Math.Lib
open Math.Lemmas
open Hacl.UInt64
open Hacl.Cast
(* open Hacl.SBuffer *)
open FStar.Buffer
open Hacl.Symmetric.Poly1305.Parameters
open Hacl.Symmetric.Poly1305.Bigint
open Hacl.Symmetric.Poly1305.Bignum.Lemmas

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module H8   = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

#reset-options "--initial_fuel 0 --max_fuel 0"

val fsum_index: a:bigint -> a_idx:u32 -> b:bigint{disjoint a b} -> b_idx:u32 -> len:u32 ->
  ctr:u32{U32.v ctr<=U32.v len} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ U32.v a_idx+U32.v len <= length a
      /\ U32.v b_idx+U32.v len <= length b
	(* /\ willNotOverflow h (U32.v a_idx) (U32.v b_idx) (U32.v len) (U32.v ctr) a b)) *)
	))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a /\ live h1 b
      /\ U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+U32.v len <= length b /\ modifies_1 a h0 h1
      (* TODO: restore the functional correctness bits *)
      (* /\ isNotModified h0 h1 (w a_idx) (w len) (w ctr) a *)
      (* /\ isSum h0 h1 (w a_idx) (w b_idx) (w len) (w ctr) a b *)
    ))
let rec fsum_index a a_idx b b_idx len ctr =
  if U32 (len =^ ctr) then ()
  else begin
      let i = ctr in
      let (ai:Hacl.UInt64.t) = U32 a.(i+^a_idx) in
      let (bi:Hacl.UInt64.t) = U32 b.(i+^b_idx) in
      let z = ai +%^ bi in
      a.(U32 (a_idx +^ i)) <- z;
      fsum_index a a_idx b b_idx len (U32 (ctr +^ 1ul));
      ()
  end

val fsum': a:bigint -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b
      (* norm h a /\ norm h b *)
    ))
    (ensures (fun h0 u h1 -> live h0 a /\ live h0 b /\ live h1 a /\ modifies_1 a h0 h1
      (* /\ norm h0 a /\ norm h0 b /\  *)
      (* /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length *)
      (* /\ isNotModified h0 h1 0 norm_length 0 a *)
      (* /\ isSum h0 h1 0 0 norm_length 0 a b *)
    ))
let fsum' a b =
  fsum_index a 0ul b 0ul nlength 0ul;
  ()

(* Scalar multiplication *)

val scalar_multiplication_aux: res:bigint -> a:bigint{disjoint res a} -> s:s64 -> ctr:u32 -> Stack unit
  (requires (fun h -> live h res /\ live h a /\ U32.v ctr <= norm_length
    (* /\ (forall (i:nat). {:pattern (v (get h a i))} i < U32.v ctr ==> v (get h a i) * v s < poU32.v2 64)  *)
  ))
  (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1
    (* /\ scalarProduct h0 h1 (U32.v ctr) a s res  *)
    (* /\ equal h0 a h1 a  *)
    (* /\ equalSub h0 res (U32.v ctr) h1 res (U32.v ctr) (length res - U32.v ctr)  *)
  ))
let rec scalar_multiplication_aux res a s ctr =
  let open FStar.UInt32 in
  if ctr =^ 0ul then ()
  else begin
    let i = ctr -^ 1ul in
    let ai = a.(i) in
    let resi = H64 (ai *%^ s) in
    res.(i) <- resi;
    scalar_multiplication_aux res a s i;
    ()
  end

val scalar_multiplication: res:bigint -> a:bigint{disjoint res a} -> s:s64 -> Stack unit
  (requires (fun h -> live h res /\ live h a
    (* /\ (forall (i:nat). {:pattern (v (get h a i))} i < norm_length ==> v (get h a i) * v s < pow2 64)  *)
  ))
  (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1
    (* /\ scalarProduct h0 h1 norm_length a s res  *)
    (* /\ equal h0 a h1 a  *)
    (* /\ equalSub h0 res norm_length h1 res norm_length (length res - norm_length) *)
    (* /\ eval h1 res norm_length = eval h0 a norm_length * v s  *)
  ))
let scalar_multiplication res a s =
  scalar_multiplication_aux res a s nlength;
  ()

(* Multiplication *)

val multiplication_step_0: a:bigint -> b:bigint -> ctr:u32{U32.v ctr<norm_length} -> c:bigint{disjoint a c /\ disjoint b c} -> tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c /\ live h tmp
       (* /\ bound27 h a /\ norm h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length -1 *)
       (* /\ maxValue h c (length c) <= w ctr * pow2 53 *)
     ))
     (ensures (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1
       (* /\ bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h0 tmp /\ length c >= 2*norm_length-1 *)
       (* /\ scalarProduct h0 h1 norm_length a (get h0 b (w ctr)) tmp *)
       (* /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b (w ctr)) *)
     ))
let multiplication_step_0 a b ctr c tmp =
  let s = b.(ctr) in
  scalar_multiplication tmp a s

val multiplication_step_p1: a:bigint -> b:bigint -> ctr:u32{U32.v ctr<norm_length} ->
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} ->
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c /\ live h tmp
	(* /\ bound27 h a /\ norm h b *)
        (* /\ (maxValue h c (length c) <= U32.v ctr * pow2 53) *)
	(* /\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (U32.v ctr)) *)
     ))
     (ensures (fun h0 u h1 -> live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       (* (bound27 h0 a) /\ (norm h0 b) /\ (live h0 c) /\ (live h0 tmp) *)
       (* /\ (bound27 h1 a) /\ (norm h1 b) *)
       (* /\ (maxValue h0 c (length c) <= U32.v ctr * pow2 53) *)
       (* /\ (maxValue h1 c (length c) <= (U32.v ctr+1) * pow2 53) *)
       (* /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (U32.v ctr)) *)
       (* /\ (eval h1 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ (U32.v ctr)) * eval h0 a norm_length * v (get h0 b (U32.v ctr))) *)
     ))
let multiplication_step_p1 a b ctr c tmp =
  multiplication_step_0 a b ctr c tmp;
  fsum_index c ctr tmp 0ul nlength 0ul

val multiplication_step: a:bigint -> b:bigint -> ctr:u32{U32.v ctr < norm_length} ->
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} ->
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Stack unit
     (requires (fun h ->  live h a  /\ live h b /\ live h c /\ live h tmp
        (* /\ bound27 h a /\ norm h b *)
	(* /\ maxValue h c (length c) <= U32.v ctr * pow2 53 *)
	(* /\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (U32.v ctr) *)
     ))
     (ensures (fun h0 u h1 -> live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       (* /\ bound27 h0 a /\ bound27 h1 a /\ norm h0 b /\ norm h1 b *)
       (* /\ live h0 c /\ live h1 c  /\ live h0 tmp *)
       (* /\ maxValue h0 c (length c) <= U32.v ctr * pow2 53 *)
       (* /\ maxValue h1 c (length c) <= (U32.v ctr+1) * pow2 53 *)
       (* /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (U32.v ctr) *)
       (* /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (U32.v ctr)) * pow2 (bitweight templ (U32.v ctr)) + eval h0 c (2*norm_length-1) *)
     ))
let multiplication_step a b ctr c tmp =
  multiplication_step_p1 a b ctr c tmp

val multiplication_aux: a:bigint -> b:bigint -> ctr:u32{U32.v ctr<=norm_length} ->
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} ->
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Stack unit
     (requires (fun h -> live h a /\ live h b  /\ live h c /\ live h tmp
        (* /\ bound27 h a /\ norm h b *)
	(* /\ maxValue h c (length c) <= (norm_length - U32.v ctr) * pow2 53 *)
	(* /\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - U32.v ctr) *)
     ))
     (ensures (fun h0 u h1 -> live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       (* /\ bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h0 tmp *)
       (* /\ bound27 h1 a /\ norm h1 b *)
       (* /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) *)
       (* /\ maxValue h1 c (length c) <= norm_length * pow2 53 *)
     ))
let rec multiplication_aux a b ctr c tmp =
  let open FStar.UInt32 in
  if ctr =^ 0ul then ()
  else begin
    multiplication_step a b (nlength -^ ctr) c tmp;
    multiplication_aux a b (ctr -^ 1ul) c tmp
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

(* Code : core multiplication function *)
val multiplication: c:bigint{length c >= 2*norm_length-1} -> a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} -> Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c
       (* bound27 h a /\ norm h b /\ live h c /\ null h c *)
     ))
     (ensures (fun h0 u h1 -> live h1 c /\ modifies_1 c h0 h1
       (* /\ bound27 h0 a /\ norm h0 b /\ live h0 c /\ bound27 h1 a /\ norm h1 b *)
       (* /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) *)
       (* /\ maxValue h1 c (length c) <= norm_length * pow2 53 *)
     ))
let multiplication c a b =
  let h_init = HST.get() in
  push_frame ();
  let h0 = HST.get() in
  let tmp = create (uint64_to_sint64 0UL) nlength in
  let h1 = HST.get() in
  multiplication_aux a b nlength c tmp;
  let h2 = HST.get() in
  lemma_modifies_0_2' c tmp h0 h1 h2;
  assert(modifies_2_1 c h0 h2);
  pop_frame ();
  let hfin = HST.get() in
  ()


(*** Modulo ***)

#reset-options "--initial_fuel 4 --max_fuel 4"

val times_5: x:s64{5 * v x < pow2 64} -> Tot (y:s64{v y = 5 * v x})
let times_5 x =
  Math.Lib.pow2_increases_lemma 64 2;
  let z = x <<^ 2ul in
  x +^ z

#reset-options "--initial_fuel 0 --max_fuel 0"

val freduce_degree':
  b:bigint -> ctr:u32{U32.v ctr < norm_length - 1} -> Stack unit
    (requires (fun h -> live h b /\ length b >= 2*norm_length - 1
      (* /\ reducible h b (U32.v ctr) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* /\ untouched h0 h1 b (U32.v ctr) /\ times5 h0 h1 b (U32.v ctr) *)
      (* /\ eval h1 b (norm_length) % reveal prime = eval h0 b (norm_length+1+U32.v ctr) % reveal prime *)
      (* /\ modifies_1 b h0 h1 *)
    ))
let rec freduce_degree' b ctr' =
  (* let h0 = HST.get() in *)
  if U32 (ctr' =^ 0ul) then begin
    let b5ctr = b.(nlength) in
    let bctr = b.(0ul) in
    let b5ctr = uint64_to_sint64 5uL *%^ b5ctr in
    let bctr = bctr +%^ b5ctr in
    (* let b5ctr = times_5 b5ctr in *)
    (* let bctr = bctr +^ b5ctr in  *)
    b.(0ul) <- bctr(* ; *)
    (* let h1 = HST.get() in *)
    (* freduce_degree_lemma h0 h1 b 0; *)
    (* cut (eval h0 b (norm_length+1+0) % reveal prime = eval h1 b (norm_length+0) % reveal prime); *)
    (* cut (eval h0 b (norm_length+1) % reveal prime = eval h1 b (norm_length+0) % reveal prime) *)
    end
  else begin
    let ctr = ctr' in
    let b5ctr = index b (U32 (ctr +^ nlength)) in
    let bctr = b.(ctr) in
    let b5ctr = uint64_to_sint64 5uL *%^ b5ctr in
    let bctr = bctr +%^ b5ctr in
    (* let b5ctr = times_5 b5ctr in *)
    (* let bctr = bctr +^ b5ctr in  *)
    b.(ctr) <- bctr;
    (* let h1 = HST.get() in *)
    (* freduce_degree_lemma h0 h1 b (U32.v ctr);  *)
    (* cut (eval h0 b (norm_length+1+U32.v ctr) % reveal prime = eval h1 b (norm_length+U32.v ctr) % reveal prime); *)
    (* cut(reducible h1 b (U32.v ctr-1));  *)
    freduce_degree' b (U32 (ctr -^ 1ul));
    (* let h2 = HST.get() in  *)
    (* cut (forall (i:nat). {:pattern (v (get h1 b i))} (i > U32.v ctr /\ i < 2*norm_length-1) ==> *)
    (* 	   v (get h1 b i) = v (get h0 b i));  *)
    (* cut(untouched h0 h2 b (U32.v ctr)); *)
    (* cut (times5 h0 h2 b (U32.v ctr)) ; *)
    ()
  end

val freduce_degree: b:bigint -> Stack unit
  (requires (fun h -> live h b /\ length b >= 2*norm_length - 1
    (* /\ satisfiesModuloConstraints h b *)
    ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ live h0 b *)
    (* /\ satisfiesModuloConstraints h0 b *)
    (* /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==> *)
    (* 	v (get h1 b i) < pow2 62) *)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime *)
  ))
let freduce_degree b =
  (* let h0 = HST.get() in *)
  (* aux_lemma_4' h0 b; *)
  freduce_degree' b (U32 (nlength -^ 2ul))
  (* let h1 = HST.get() in *)
  (* aux_lemma_5' h0 h1 b *)

val mod2_26: a:s64 -> Tot (b:s64(* {v b = v a % pow2 26} *))
let mod2_26 a =
  let mask = shift_left (uint64_to_sint64 1UL) 26ul in
  Math.Lib.pow2_increases_lemma 64 26;
  let mask = mask -^ (uint64_to_sint64 1UL) in
  let res = a &^ mask in
  (* SInt.ulogand_lemma_4 #64 a 26 mask; *)
  res

val carry: b:bigint -> ctr:u32{U32.v ctr <= norm_length} -> Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length+1
      (* carriable h b (w ctr) /\ carried h b (w ctr) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* /\ carried h1 b norm_length /\ untouched_2 h0 h1 b (w ctr) *)
      (* /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1) *)
      (* /\ modifies_1 b h0 h1 *)
    ))
let rec carry b i =
  (* let h0 = HST.get() in *)
  if U32( i =^ nlength) then ()
  else begin
    let bi = b.(i) in
    let ri = mod2_26 bi in
    b.(i) <- ri;
    (* let h1 = HST.get() in *)
    let c = (bi >>^ 26ul) in
    (* cut (v c = (v bi) / (pow2 26)); *)
    (* Math.Lib.pow2_div_lemma 64 26; *)
    (* (\* TODO *\) *)
    (* assume (v c < pow2 (64 - 26)); *)
    (* assert(live h1 b); *)
    (* assert(w i + 1 < length b);  *)
    let bip1 = b.(U32 (i +^ 1ul)) in
    (* auxiliary_lemma_1' bip1 c; *)
    let z = bip1 +%^ c in
    b.(U32 (i +^ 1ul)) <- z;
    (* let h2 = HST.get() in *)
    (* eval_carry_lemma h0 b h2 b (w i); *)
    carry b (U32 (i +^ 1ul))
  end

val carry_top_to_0: b:bigint -> Stack unit
    (requires (fun h -> live h b /\ length b >= norm_length + 1
      (* /\ carried h b norm_length /\ length b >= 2*norm_length-1 *)
      (* /\ v (get h b 0) + 5 * v (get h b norm_length) < pow2 63 *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* /\ carried h0 b norm_length /\ carried' h1 b 1 *)
      (* /\ eval h1 b norm_length % (reveal prime) = eval h0 b (norm_length+1) % (reveal prime) *)
      (* /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b norm_length) *)
      (* /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==> *)
      (* 	  v (get h1 b i) = v (get h0 b i)) *)
      (* /\ modifies_1 b h0 h1 *)
    ))
let carry_top_to_0 b =
  (* Math.Lib.pow2_increases_lemma 64 63; *)
  (* let h0 = HST.get() in *)
  let b0 = b.(0ul) in
  let btop = b.(nlength) in
  let btop_5 = uint64_to_sint64 5uL *%^ btop in
  (* let btop_5 = times_5 btop in *)
  b.(0ul) <- (b0 +%^ btop_5)(* ; *)
  (* let h1 = HST.get() in *)
  (* freduce_degree_lemma h0 h1 b 0 *)

val carry2_aux: b:bigint -> ctr:u32{U32.v ctr > 0 /\ U32.v ctr <= norm_length} -> Stack unit
  (requires (fun h -> live h b /\ length b >= norm_length + 1
    (* carriable2 h b (w ctr) *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* carriable2 h0 b (w ctr) /\ carriable2 h1 b norm_length *)
    (* /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1) *)
    (* /\ modifies_1 b h0 h1 *)
  ))
let rec carry2_aux b i =
  (* let h0 = HST.get() in *)
  if U32 (i =^ nlength) then ()
  else begin
    let bi = b.(i) in
    let ri = mod2_26 bi in
    (* lemma_aux_2 bi; *)
    (* cut (v ri < pow2 (templ (w i)));  *)
    b.(i) <- ri;
    (* let h1 = HST.get() in *)
    let c = bi >>^ 26ul in
    // In the spec of >>, TODO
    (* assume(v c < 2);  *)
    let bip1 = b.(U32 (i +^ 1ul)) in
    (* auxiliary_lemma_2 bip1 c; *)
    (* Math.Lib.pow2_increases_lemma 64 27; *)
    (* Math.Lemmas.pow2_double_sum 26; *)
    (* Math.Lib.pow2_increases_lemma 26 15; *)
    let z = bip1 +%^ c in
    (* cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 26); *)
    (* cut (v z >= pow2 26 ==> v c = 1);  *)
    (* cut (v c > 0 ==> v (get h0 b (w i)) / (pow2 26) > 0 ==> v (get h0 b (w i)) >= pow2 26); *)
    (* cut (v z >= pow2 26 ==> v (get h1 b (w i)) < pow2 15);  *)
    upd b (U32 (i +^ 1ul)) z;
    (* let h2 = HST.get() in *)
    (* cut (v z >= pow2 26 ==> v c = 1);  *)
    (* eval_carry_lemma h0 b h2 b (w i);  *)
    carry2_aux b (U32 (i +^ 1ul))
  end

val carry2: b:bigint -> Stack unit
  (requires (fun h -> live h b /\ length b >= norm_length + 1
    (* carried h b norm_length /\ length b >= 2*norm_length-1 *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ carried h0 b norm_length /\ carriable2 h1 b norm_length *)
    (* /\ eval h1 b (norm_length+1) % reveal prime = eval h0 b (norm_length+1) % reveal prime *)
    (* /\ modifies_1 b h0 h1 *)
  ))
let rec carry2 b =
  (* let h0 = HST.get() in *)
  (* pow2_3_lemma (); *)
  (* Math.Lib.pow2_exp_lemma 3 37; *)
  (* Math.Lib.pow2_increases_lemma 40 37; *)
  (* Math.Lib.pow2_increases_lemma 40 26; *)
  (* Math.Lemmas.pow2_double_sum 40; *)
  (* Math.Lib.pow2_increases_lemma 63 41; *)
  carry_top_to_0 b;
  (* let h1 = HST.get() in *)
  b.(nlength) <- (uint64_to_sint64 0UL);
  (* let h2 = HST.get() in *)
  (* eval_eq_lemma h1 h2 b b norm_length; *)
  (* cut ( eval h2 b (norm_length+1) = eval h1 b (norm_length));  *)
  let bi = b.(0ul) in
  let ri = mod2_26 bi in
  (* cut (v ri < pow2 26); *)
  b.(0ul) <- ri;
  (* let h3 = HST.get() in *)
  let c = bi >>^ 26ul in
  (* cut (v bi < pow2 41);  *)
  // In the spec of >>, TODO
  (* assume (v c < pow2 15);  *)
  let bip1 = b.(1ul) in
  (* auxiliary_lemma_2 bip1 c;  *)
  (* Math.Lib.pow2_increases_lemma 64 27; *)
  (* Math.Lemmas.pow2_double_sum 26; *)
  (* Math.Lib.pow2_increases_lemma 26 15; *)
  let z = bip1 +%^ c in
  b.(1ul) <- z;
  (* let h4 = HST.get() in *)
  (* eval_carry_lemma h2 b h4 b 0;  *)
  (* cut(carriable2 h4 b 1); *)
  carry2_aux b 1ul

val last_carry: b:bigint -> Stack unit
  (requires (fun h -> live h b /\ length b >= norm_length + 1
    (* carriable2 h b norm_length /\ length b >= 2*norm_length-1 *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ carriable2 h0 b norm_length /\ norm h1 b *)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime *)
  ))
let last_carry b =
  (* let h0 = HST.get() in *)
  let b0 = index b 0ul in
  let btop = b.(nlength) in
  (* cut (v b0 < pow2 26 /\ v btop < 2);  *)
  (* pow2_3_lemma (); *)
  (* cut (5 * v btop < pow2 3 /\ True);  *)
  (* Math.Lib.pow2_increases_lemma 26 3; *)
  (* Math.Lemmas.pow2_double_sum 26; *)
  (* Math.Lib.pow2_increases_lemma 64 27; *)
  (* cut(v b0 + 5 * v btop < pow2 27 /\ True);  *)
  let btop_5 = uint64_to_sint64 5uL *%^ btop in
  (* let btop_5 = times_5 btop in *)
  b.(0ul) <- (b0 +%^ btop_5);
  (* let h1 = HST.get() in *)
  (* freduce_degree_lemma h0 h1 b 0; *)
  b.(nlength) <- (uint64_to_sint64 0UL);
  (* let h2 = HST.get() in *)
  (* eval_eq_lemma h1 h2 b b norm_length; *)
  (* cut (eval h2 b (norm_length+1) = eval h1 b norm_length); *)
  let bi = b.(0ul) in
  let ri = mod2_26 bi in
  (* assert(v ri < pow2 26); *)
  b.(0ul) <- ri;
  (* let h3 = HST.get() in *)
  let c = bi >>^ 26ul in
  (* cut (v bi < pow2 26 + 5); *)
  (* cut (v bi >= pow2 26 ==> v (get h3 b 1) < pow2 15); *)
  (* // In the spec of >>, TODO *)
  (* assume (v bi >= pow2 26 ==> v c = 1); *)
  let bip1 = b.(1ul) in
  (* auxiliary_lemma_2 bip1 c; *)
  (* Math.Lib.pow2_increases_lemma 64 27; *)
  (* Math.Lemmas.pow2_double_sum 26; *)
  (* Math.Lib.pow2_increases_lemma 26 15; *)
  let z = bip1 +%^ c in
  b.(1ul) <- z;
  (* let h4 = HST.get() in *)
  (* eval_carry_lemma h2 b h4 b 0; *)
  (* cut (v (get h4 b 1) < pow2 26); *)
  (* cut (norm h4 b); *)
  ()

val modulo: b:bigint -> Stack unit
  (requires (fun h -> live h b /\ length b >= 2*norm_length-1
    (* /\ satisfiesModuloConstraints h b *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ satisfiesModuloConstraints h0 b /\ norm h1 b *)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime *)
  ))
let modulo b =
  (* let h0 = HST.get() in *)
  freduce_degree b;
  (* let h1 = HST.get() in *)
  b.(nlength) <- (uint64_to_sint64 0UL);
  (* let h2 = HST.get() in *)
  (* eval_eq_lemma h1 h2 b b norm_length; *)
  (* cut (eval h2 b (norm_length+1) = eval h1 b norm_length); *)
  carry b 0ul;
  (* let h3 = HST.get() in *)
  carry2 b;
  (* let h4 = HST.get() in *)
  last_carry b

val freduce_coefficients: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 62) *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ live h0 b /\ norm h1 b *)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime *)
    (* /\ modifies_1 b h0 h1 *)
  ))
let freduce_coefficients b =
  push_frame();
  (* let h0 = HST.get() in *)
  let tmp = create (uint64_to_sint64 0UL) (U32 (2ul *^ nlength -^ 1ul)) in
  (* let h1 = HST.get() in *)
  (* eq_lemma_0 h0 h1 b; *)
  (* eval_eq_lemma h0 h1 b b norm_length; *)
  blit b 0ul tmp 0ul nlength;
  (* let h2 = HST.get() in *)
  (* eval_eq_lemma h1 h2 b tmp norm_length; *)
  (* cut (forall (i:nat). {:pattern (v (get h2 tmp i))} i < norm_length ==> v (get h2 tmp i) = v (get h0 b i));  *)
  carry tmp 0ul;
  carry2 tmp;
  last_carry tmp;
  (* let h = HST.get() in *)
  blit tmp 0ul b 0ul nlength;
  (* let h' = HST.get() in *)
  (* eval_eq_lemma h h' tmp b norm_length; *)
  (* cut (forall (i:nat). {:pattern (v (get h tmp i))} i < norm_length ==> v (get h tmp i) < pow2 26);  *)
  (* cut (forall (i:nat). {:pattern (v (get h' b i))} i < norm_length ==> v (get h' b (0+i)) = v (get h tmp (0+i))) *)
  pop_frame()

(*** Finalization ***)

val finalize: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\ norm h b *)
  ))
  (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    (* /\ norm h0 b /\ norm h1 b *)
    (* /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime *)
  ))
let finalize b =
  let mask_26 = ((uint64_to_sint64 1UL) <<^ 26ul) -%^ (uint64_to_sint64 1UL) in
  let mask2_26m5 = mask_26 -%^ (uint64_to_sint64 1UL <<^ 2ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let mask = Hacl.UInt64.eq_mask b4 mask_26 in
  let mask = Hacl.UInt64.eq_mask b3 mask_26 &^ mask in
  let mask = Hacl.UInt64.eq_mask b2 mask_26 &^ mask in
  let mask = Hacl.UInt64.eq_mask b1 mask_26 &^ mask in
  let mask = Hacl.UInt64.gte_mask b0 mask2_26m5 &^ mask in
  b.(0ul) <- (b0 -%^ (mask &^ mask2_26m5));
  b.(1ul) <- (b1 -%^ (b1 &^ mask));
  b.(2ul) <- (b2 -%^ (b2 &^ mask));
  b.(3ul) <- (b3 -%^ (b3 &^ mask));
  b.(4ul) <- (b4 -%^ (b4 &^ mask));
  ()
