module Curve.Modulo

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open Hacl.Cast
open Hacl.UInt128
open Hacl.SBuffer
open Math.Lib
open Math.Field
open Curve.Parameters
open Curve.Bigint

module U32 = FStar.UInt32
module S64 = Hacl.UInt64
module S128 = Hacl.UInt128
module HS = FStar.HyperStack

let w: u32 -> Tot int = U32.v
let vv: s64 -> GTot int = S64.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

let heap = HS.mem

let op_Bar_Amp (x:s128) (y:s128) : Tot s128 = Hacl.UInt128.logand x y
let op_Bar_Greater_Greater (x:s128) (y:u32) : Tot s128 = Hacl.UInt128.shift_right x y
let op_Bar_Less_Less (x:s128) (y:u32) : Tot s128 = Hacl.UInt128.shift_left x y
let op_Bar_Plus (x:s128) (y:s128) : Tot s128 = Hacl.UInt128.add x y
let op_Bar_Star (x:s128) (y:s128) : Tot s128 = Hacl.UInt128.mul x y

(* let satisfies_modulo_constraints h b = *)
(*   length b >= 2*norm_length-1 && getTemplate b = templ *)
(*   && maxValue h b < pow2 (platform_wide - 3) *)

(* val lemma_satisfies: h:heap -> b:bigint_wide -> n:nat -> Lemma *)
(*   (requires (live h b /\ (forall (i:nat). i < length b ==> v (get h b i) < pow2 n))) *)
(*   (ensures  (live h b /\ maxValue h b < pow2 n)) *)
(* let lemma_satisfies h b n = ()   *)

let sum_satisfies_constraints h0 h1 cpy a b : Lemma (True) = ()
(*   //@@ *)
(*   pow2_double_sum 56; *)
(*   cut (forall (i:nat). {:pattern (v (get h1 cpy i))} i < norm_length  *)
(* 	    ==> v (get h1 cpy i) < pow2 57); *)
(*   cut (forall (i:nat). {:pattern (v (get h1 cpy i))} (i >= norm_length /\ i < getLength h1 cpy) *)
(* 	    ==> v (get h1 cpy i) = 0); *)
(*   cut(forall (i:nat). {:pattern (v (get h1 cpy i))} i < getLength h1 cpy *)
(* 	   ==> v (get h1 cpy i) < pow2 57); *)
(*   lemma_satisfies h1 cpy 57; *)
(*   pow2_increases_lemma (platform_wide - 3) 57 *)

(* let n0 = ndiff' *)
(* let n1 = ndiff *)

let difference_satisfies_constraints h0 h1 cpy a b : Lemma (True) = ()
(*   //@@ *)
(*   cut(forall (i:nat). {:pattern (v (get h1 cpy i))} i < getLength h1 cpy *)
(* 	   ==> v (get h1 cpy i) < pow2 58); *)
(*   lemma_satisfies h1 cpy 58; *)
(*   pow2_increases_lemma (platform_wide - 3) 58   *)

(* val lemma_satisfies_2: h:heap -> b:bigint -> Lemma  *)
(*   (requires (Standardized h b)) *)
(*   (ensures  (Standardized h b /\ maxValueNorm h b < pow2 56)) *)
(* let lemma_satisfies_2 h b = () *)

(* val lemma_satisfies_4: a:nat -> b:nat -> c:pos -> d:pos -> Lemma (requires (a < c /\ b < d)) *)
(* 							    (ensures (a * b < c * d)) *)
(* let lemma_satisfies_4 a b c d = () *)

(* val lemma_satisfies_3: b:nat -> c:nat -> Lemma *)
(*   (requires (b < pow2 56 /\ c < pow2 56)) *)
(*   (ensures (norm_length * b * c <= pow2 115)) *)
(* let lemma_satisfies_3 b c =  *)
(*   cut (True /\ 8 = pow2 3); *)
(*   pow2_exp_lemma 56 56; *)
(*   pow2_exp_lemma 3 112; *)
(*   Axiomatic.paren_mul_right norm_length b c; *)
(*   lemma_satisfies_4 b c (pow2 56) (pow2 56) *)

let mul_satisfies_constraints h0 h1 res a b : Lemma (True) = ()
(*   lemma_satisfies_2 h0 a; *)
(*   lemma_satisfies_2 h0 b; *)
(*   lemma_satisfies_3 (maxValueNorm h0 a) (maxValueNorm h0 b); *)
(*   pow2_increases_lemma (platform_wide - 3) 115 *)

let updated (h0:heap) (h1:heap) (b:bigint_wide) (len:nat) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= len

(* val lemma_helper_000: ctr:nat{ctr>=2} -> Lemma (ctr-1+norm_length = ctr+norm_length-1  *)
(* 					   /\ ctr+norm_length-1 = (ctr-1) + norm_length *)
(* 					   /\ (ctr+norm_length-1)-1=ctr+norm_length-2) *)
(* let lemma_helper_000 ctr = ()					    *)

(* val lemma_helper_001: ctr:nat{ctr>=2} -> Lemma  *)
(*   (bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 56) *)
(* let lemma_helper_001 ctr =  *)
(*   bitweight_definition templ (ctr+norm_length-2) *)

(* val lemma_helper_002: a:nat -> b:nat -> Lemma (bitweight templ (a+b) = bitweight templ a + bitweight templ b) *)
(* let rec lemma_helper_002 a b = match a with | 0 -> () | _ -> lemma_helper_002 (a-1) b *)

(* val lemma_helper_003: ctr:nat{ctr>=2} -> Lemma (pow2 56 * pow2 (bitweight templ (ctr-2)) = pow2 (bitweight templ (ctr-1))) *)
(* let lemma_helper_003 ctr =  *)
(*   bitweight_definition templ 1; *)
(*   lemma_helper_002 1 (ctr-2);  *)
(*   Lemmas.pow2_exp_1 56 (bitweight templ (ctr-2)) *)

(* val lemma_helper_004: ctr:nat{ctr>=2} -> Lemma *)
(*   (requires (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 56 * pow2 (bitweight templ (ctr+norm_length-2)))) *)
(*   (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length))) *)
(* let lemma_helper_004 ctr = *)
(*   //@@ long *)
(*   lemma_helper_002 (ctr-2) norm_length; *)
(*   Lemmas.pow2_exp_1 (bitweight templ (ctr-2)) (bitweight templ norm_length); *)
(*   Axiomatic.paren_mul_right (pow2 56) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length)); *)
(*   lemma_helper_003 ctr *)

(* val pow2_bitweight_lemma_1: ctr:pos ->  *)
(*   Lemma *)
(*     (requires (True)) *)
(*     (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length))) *)
(* let rec pow2_bitweight_lemma_1 ctr = *)
(*   //@@ *)
(*   match ctr with *)
(*   | 1 -> () *)
(*   | _ ->  *)
(*     lemma_helper_000 ctr; *)
(*     pow2_bitweight_lemma_1 (ctr-1); *)
(*     lemma_helper_001 ctr; *)
(*     bitweight_definition templ (ctr+norm_length-2); *)
(*     Lemmas.pow2_exp_1 56 (bitweight templ (ctr+norm_length-2));  *)
(*     lemma_helper_004 ctr *)

(* val bitweight_norm_length_lemma: unit -> Lemma (requires (True)) (ensures (bitweight templ norm_length = 448)) *)
(* let bitweight_norm_length_lemma () =  *)
(*   //@@ *)
(*   bitweight_definition templ (norm_length-1); *)
(*   bitweight_definition templ (norm_length-2); *)
(*   bitweight_definition templ (norm_length-3); *)
(*   bitweight_definition templ (norm_length-4); *)
(*   bitweight_definition templ (norm_length-5); *)
(*   bitweight_definition templ (norm_length-6); *)
(*   bitweight_definition templ (norm_length-7); *)
(*   bitweight_definition templ (norm_length-8) *)

(* (\*  *)
(*    P_448 = 2^448 - 2^224 - 1, hence  *)
(*      a[i+0] + 2^56*a[i+1] + 2^112*a[i+2] + 2^168*a[i+3] + 2^224*a[i+4]  *)
(*             + 2^280*a[i+5] + 2^336*a[i+6] + 2^392*a[i+7] + 2^448*a[i+8] *)
(*   = (a[i+0]+a[i+8]) + 2^56*a[i+1] + 2^112*a[i+2] + 2^168*a[i+3] + 2^224*(a[i+4]+a[i+8]) *)
(* 		    + 2^280*a[i+5] + 2^336*a[i+6] + 2^392*a[i+7]  *)
(*  *\) *)
(* assume val freduce_degree_lemma_0: h0:heap -> h1:heap -> b:bigint_wide -> ctr:nat{ctr < norm_length-1 /\ updated h0 h1 b (norm_length+1+ctr)} -> Lemma *)
(*   (requires (forall (i:nat). {:pattern (v (get h1 b i))} (i < lengthb /\ i <> ctr /\ i <> ctr+4) ==> *)
(* 				(v (get h1 b i) = v (get h0 b i) *)
(* 				/\ v (get h1 b ctr) = v (get h0 b ctr) + v (get h0 b (ctr+8)) *)
(* 				/\ v (get h1 b (ctr+4)) = v (get h0 b (ctr+4)) + v (get h0 b (ctr+8))) )) *)
(*   (ensures (eval h0 b (9+ctr) % reveal prime = eval h1 b (8+ctr) % reveal prime)) *)

(* val lemma_helper_0: x:wide -> y:wide -> Lemma  *)
(*   (requires (v x < pow2 (platform_wide - 3) /\ v y < pow2 (platform_wide - 3) )) *)
(*   (ensures (v x + v y < pow2 platform_wide)) *)
(* let lemma_helper_0 x y =  *)
(*   //@@ *)
(*   () *)

let reducible h b : GTot Type0 = 
  live h b /\ length b >= 2 * norm_length - 1
  /\ v (get h b 0 ) < pow2 (platform_wide-3)  /\ v (get h b 1 ) < pow2 (platform_wide-3)
  /\ v (get h b 2 ) < pow2 (platform_wide-3)  /\ v (get h b 3 ) < pow2 (platform_wide-3)
  /\ v (get h b 4 ) < pow2 (platform_wide-3)  /\ v (get h b 5 ) < pow2 (platform_wide-3)
  /\ v (get h b 6 ) < pow2 (platform_wide-3)  /\ v (get h b 7 ) < pow2 (platform_wide-3)
  /\ v (get h b 8 ) < pow2 (platform_wide-3)  /\ v (get h b 9 ) < pow2 (platform_wide-3)
  /\ v (get h b 10) < pow2 (platform_wide-3)  /\ v (get h b 11) < pow2 (platform_wide-3)
  /\ v (get h b 12) < pow2 (platform_wide-3)  /\ v (get h b 13) < pow2 (platform_wide-3)
  /\ v (get h b 14) < pow2 (platform_wide-3)

let reduced h0 h1 (b:bigint_wide) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b >= 2*norm_length-1
  /\ v (get h1 b 0 ) = v (get h0 b 0 ) 
  /\ v (get h1 b 1 ) = v (get h0 b 1)
  /\ v (get h1 b 2 ) = v (get h0 b 2 ) 
  /\ v (get h1 b 3 ) = v (get h0 b 3 ) + v (get h0 b 11)
  /\ v (get h1 b 4 ) = v (get h0 b 4 ) + v (get h0 b 12)
  /\ v (get h1 b 5 ) = v (get h0 b 5 ) + v (get h0 b 13)
  /\ v (get h1 b 6 ) = v (get h0 b 6 ) + v (get h0 b 14)
  /\ v (get h1 b 7 ) = v (get h0 b 7 ) + v (get h0 b 11)
  /\ v (get h1 b 8 ) = v (get h0 b 8 ) + v (get h0 b 12)
  /\ v (get h1 b 9 ) = v (get h0 b 9 ) + v (get h0 b 13)
  /\ v (get h1 b 10) = v (get h0 b 10) + v (get h0 b 14)

val freduce_degree_1: b:bigint_wide -> STL unit
  (requires (fun h -> reducible h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (2*norm_length-1)
    /\ reduced h0 h1 b
    /\ eval_wide h1 b 11 % reveal prime = eval_wide h0 b 15 % reveal prime))
let freduce_degree_1 b =
  //@@
  let b14 = index b 14ul in 
  let b13 = index b 13ul in
  let b12 = index b 12ul in
  let b11 = index b 11ul in
  let b10 = index b 10ul in
  let b9  = index b 9ul  in
  let b8  = index b 8ul  in
  let b7  = index b 7ul  in
  let b6  = index b 6ul  in
  let b5  = index b 5ul  in
  let b4  = index b 4ul  in
  let b3  = index b 3ul  in
  let h0 = HST.get() in
  (* lemma_helper_0 b10 b14; *)
  (* lemma_helper_0 b6  b14; *)
  upd b 10ul (b10 |+ b14);
  upd b 6ul  (b6  |+ b14);
  (* let h1 = ST.get() in  *)
  (* freduce_degree_lemma_0 h0 h1 b 6;  *)
  (* lemma_helper_0 b9  b13; *)
  (* lemma_helper_0 b5  b13; *)
  upd b 9ul  (b9  |+ b13);
  upd b 5ul  (b5  |+ b13);
  let h2 = HST.get() in 
  (* freduce_degree_lemma_0 h1 h2 b 5;  *)
  (* lemma_helper_0 b8 b12; *)
  (* lemma_helper_0 b4 b12; *)
  upd b 8ul  (b8  |+ b12);
  upd b 4ul  (b4  |+ b12);
  (* let h3 = HST.get() in  *)
  (* freduce_degree_lemma_0 h2 h3 b 4;  *)
  (* lemma_helper_0 b7 b11; *)
  (* lemma_helper_0 b3 b11; *)
  upd b 7ul  (b7  |+ b11);
  upd b 3ul  (b3  |+ b11)
  (* let h4 = HST.get() in *)
  (* freduce_degree_lemma_0 h3 h4 b 3 *)

val lemma_helper_1: x:s128 -> y:s128 -> Lemma 
  (requires (v x < pow2 (platform_wide - 2) /\ v y < pow2 (platform_wide - 2) ))
  (ensures (v x + v y < pow2 platform_wide))
let lemma_helper_1 x y = ()

type reducible2 (h:heap) (b:bigint_wide) =
  live h b /\ length b >= 2 * norm_length - 1
  /\ v (get h b 0) < pow2 (platform_wide - 2)
  /\ v (get h b 1) < pow2 (platform_wide - 2)
  /\ v (get h b 2) < pow2 (platform_wide - 2)
  /\ v (get h b 3) < pow2 (platform_wide - 2)
  /\ v (get h b 4) < pow2 (platform_wide - 2)
  /\ v (get h b 5) < pow2 (platform_wide - 2)
  /\ v (get h b 6) < pow2 (platform_wide - 2)
  /\ v (get h b 7) < pow2 (platform_wide - 2)
  /\ v (get h b 8) < pow2 (platform_wide - 2)
  /\ v (get h b 9) < pow2 (platform_wide - 2)
  /\ v (get h b 10) < pow2 (platform_wide - 2)

type reduced2 (h0:heap) (h1:heap) (b:bigint_wide) = 
  live h0 b /\ length b >= 2 * norm_length - 1 /\ live h1 b /\ length b >= 2 * norm_length - 1
  /\ v (get h1 b 0 ) = v (get h0 b 0 ) + v (get h0 b 8 )
  /\ v (get h1 b 1 ) = v (get h0 b 1 ) + v (get h0 b 9 )
  /\ v (get h1 b 2 ) = v (get h0 b 2 ) + v (get h0 b 10) 
  /\ v (get h1 b 3 ) = v (get h0 b 3 )
  /\ v (get h1 b 4 ) = v (get h0 b 4 ) + v (get h0 b 8)
  /\ v (get h1 b 5 ) = v (get h0 b 5 ) + v (get h0 b 9)
  /\ v (get h1 b 6 ) = v (get h0 b 6 ) + v (get h0 b 10)
  /\ v (get h1 b 7 ) = v (get h0 b 7 )

val freduce_degree_2: b:bigint_wide -> STL unit
  (requires (fun h -> reducible2 h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (2*norm_length-1)
    /\ reduced2 h0 h1 b
    /\ eval_wide h1 b 8 % reveal prime = eval_wide h0 b 11 % reveal prime))
let freduce_degree_2 b =
  //@@
  let b11 = index b 11ul in
  let b10 = index b 10ul in
  let b9  = index b 9ul  in
  let b8  = index b 8ul  in
  let b6  = index b 6ul  in
  let b5  = index b 5ul  in
  let b4  = index b 4ul  in
  let b2  = index b 2ul  in
  let b1  = index b 1ul  in
  let b0  = index b 0ul  in
  (* let h0 = HST.get() in *)
  (* lemma_helper_1 b6 b10; *)
  (* lemma_helper_1 b2 b10; *)
  upd b 6ul (b6 |+ b10);
  upd b 2ul (b2 |+ b10);
  (* let h1 = HST.get() in *)
  (* freduce_degree_lemma_0 h0 h1 b 2;  *)
  (* lemma_helper_1 b5 b9; *)
  (* lemma_helper_1 b1 b9; *)
  upd b 5ul (b5 |+ b9);
  upd b 1ul (b1 |+ b9);
  (* let h2 = HST.get() in *)
  (* freduce_degree_lemma_0 h1 h2 b 1;  *)
  (* lemma_helper_1 b4 b8; *)
  (* lemma_helper_1 b0 b8; *)
  upd b 4ul  (b4  |+ b8);
  upd b 0ul  (b0  |+ b8)
  (* let h3 = HST.get() in *)
  (* freduce_degree_lemma_0 h2 h3 b 0 *)

#reset-options

val trim_2_56:x:s128 -> Tot (y:s128{v y = v x % pow2 56})
let trim_2_56 x = 
  let mask = Hacl.UInt128.shift_left (Hacl.UInt128.of_string "1") 56ul in
  cut (v mask = pow2 56 % pow2 platform_wide /\ pow2 56 >= 1); 
  (* Lemmas.pow2_increases_1 platform_wide 56;  *)
  (* ModuloLemmas.mod_lemma_1 (pow2 56) (pow2 platform_wide); *)
  let mask = Hacl.UInt128.sub mask (Hacl.UInt128.of_string "1") in
  let res = x |& mask in
  (* log_and_wide_lemma_3 x mask 56; *)
  res

(* val lemma_helper_2: bip1:wide -> c:wide ->  *)
(*   Lemma *)
(*     (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 56))) *)
(*     (ensures (v bip1 + v c < pow2 platform_wide)) *)
(* let lemma_helper_2 bip1 c =  *)
(*   coerce  *)
(*     (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 56))) *)
(*     (ensures (v bip1 + v c < pow2 platform_wide)) *)
(*     (fun _ -> ModuloLemmas.helper_lemma_4 (v bip1) (v c) 56 platform_wide) *)

(* val pow2_bitweight_lemma: ctr:nat ->  *)
(*   Lemma *)
(*     (requires (True)) *)
(*     (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr))) *)
(* let pow2_bitweight_lemma ctr = *)
(*   bitweight_definition templ ctr; *)
(*   Lemmas.pow2_exp_1 (bitweight templ ctr) (templ ctr) *)

(* val eval_carry_lemma: *)
(*   ha:heap -> a:bigint_wide{live ha a /\ getLength ha a >= norm_length+1} ->  *)
(*   hb:heap -> b:bigint_wide{live hb b /\ getLength hb b >= norm_length+1} -> *)
(*   ctr:nat{ctr < norm_length} ->  *)
(*   Lemma *)
(*     (requires ( *)
(*       v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr) *)
(*       /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr) *)
(*       /\ (forall (i:nat). {:pattern (v (get hb b i))} *)
(* 	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i)) *)
(*     )) *)
(*     (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1))) *)
(* let eval_carry_lemma ha a hb b ctr = *)
(*   coerce  *)
(*     (requires ( *)
(*       v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr) *)
(*       /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr) *)
(*       /\ (forall (i:nat). {:pattern (v (get hb b i))} *)
(* 	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i)) *)
(*     )) *)
(*     (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1))) *)
(*     (fun _ ->  *)
(*       //@@ *)
(*       eval_eq_lemma ha hb a b ctr; *)
(*       assert(eval ha a ctr = eval hb b ctr); *)
(*       eval_definition ha a (ctr+2); *)
(*       eval_definition ha a (ctr+1); *)
(*       eval_definition hb b (ctr+2); *)
(*       eval_definition hb b (ctr+1); *)
(*       ModuloLemmas.helper_lemma_0 ctr; ModuloLemmas.helper_lemma_1 ctr; *)
(*       assert(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + eval hb b (ctr+1));  *)
(*       assert(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (get hb b ctr) + eval hb b ctr));   *)
(*       assert(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));  *)
(*       Axiomatic.distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (get ha a (ctr+1))) (v (get ha a ctr) / pow2 (templ ctr)); *)
(*       cut(True /\ eval hb b (ctr+2) =  *)
(* 	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) *)
(* 	      + pow2 (bitweight templ (ctr+1)) * v (get ha a ctr) / pow2 (templ ctr)  *)
(* 	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));  *)
(*       pow2_bitweight_lemma ctr;  *)
(*       cut(True /\ eval hb b (ctr+2) =  *)
(* 	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1))  *)
(* 	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (get ha a ctr) / pow2 (templ ctr)  *)
(* 	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));   *)
(*       ModuloLemmas.helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (get ha a ctr)) (eval hb b ctr);  *)
(*       cut(True /\ eval hb b (ctr+2) =  *)
(* 	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1))  *)
(* 	      + (pow2 (bitweight templ ctr) * v (get ha a ctr) + eval hb b ctr));   *)
(*       cut(True /\ eval hb b (ctr+2) = eval ha a (ctr+2));  *)
(*       eval_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1); *)
(*       ModuloLemmas.helper_lemma_3 (eval ha a (norm_length+1)) (eval hb b (norm_length+1)) (eval ha a (ctr+2)) (eval hb b (ctr+2)) ) *)

abstract let carriable (h:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h b i))}
      (i > ctr /\ i <= norm_length) ==> v (get h b i) < pow2 (platform_wide - 1))

abstract let carried (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (get h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h1 b norm_length) < pow2 72)

abstract let untouched_2 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ (forall (i:nat). {:pattern (get h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < length b) ==> v (get h0 b i) = v (get h1 b i))

(* val freduce_lemma_0: h0:heap -> h1:heap -> h2:heap -> b:bigint_wide -> Lemma *)
(*   (requires (reducible h0 b /\ reduced h0 h1 b /\ reduced2 h1 h2 b /\ v (get h2 b 8) = 0)) *)
(*   (ensures (carriable h2 b 0)) *)
(* let freduce_lemma_0 h0 h1 h2 b =  *)
(*   pow2_double_sum (platform_wide-3); *)
(*   pow2_double_sum (platform_wide-2); *)
(*   pow2_increases_lemma (platform_wide-1) (platform_wide-3); () *)

val carry: b:bigint_wide -> ctr:u32(* {ctr <= norm_length} *) -> STL unit
  (requires (fun h -> True (* carriable h b ctr /\ carried h b ctr *)))
  (ensures (fun h0 _ h1 -> True (* updated h0 h1 b (norm_length+1) *)
    (* /\ carried h1 b norm_length *)
    (* /\ untouched_2 h0 h1 b ctr *)
    (* /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1) *)
    (* /\ modifies !{getRef b} h0 h1 *)
    ))
let rec carry b i =
  admit();
  let h0 = HST.get() in
  if UInt32.eq nlength i then ()
  else begin 
    let bi = index b i in
    let ri = trim_2_56 bi in
    (* assert(v ri < pow2 (templ i));  *)
    upd b i ri; 
    (* let h1 = HST.get() in *)
    let c = (bi |>> 56ul) in
    (* upd_lemma h0 h1 b i ri;  *)
    (* admitP (True /\ v c < pow2 (platform_wide - 56)); // From the spec of >> on wides, to add *)
    let bip1 = index b (i+|1ul) in 
    (* lemma_helper_2 bip1 c; *)
    let z = bip1 |+ c in 
    upd b (i+|1ul) z;
    (* let h2 = HST.get() in *)
    (* upd_lemma h1 h2 b (i+|1ul) z; *)
    (* eval_carry_lemma h0 b h2 b i; *)
    carry b (i+|1ul)
  end
  
#reset-options

abstract let carried2 (h1:heap) (b:bigint_wide) =
  live h1 b /\ length b >= norm_length + 1
  /\ v (get h1 b 1) < pow2 56 /\ v (get h1 b 2) < pow2 56 /\ v (get h1 b 3) < pow2 56
  /\ v (get h1 b 5) < pow2 56 /\ v (get h1 b 6) < pow2 56 /\ v (get h1 b 7) < pow2 56
  /\ v (get h1 b 0) < pow2 73 /\ v (get h1 b 4) < pow2 73
  /\ v (get h1 b norm_length) < pow2 72

(* val lemma_helper_3: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 56 /\ v y < pow2 72)) *)
(*   (ensures (v x + v y < pow2 platform_wide /\ v x + v y < pow2 73)) *)
(* let lemma_helper_3 x y =  *)
(*   pow2_increases_lemma 72 57; *)
(*   pow2_increases_lemma platform_wide 73 *)

val carry_top_to_0:
  b:bigint_wide -> STL unit 
    (requires (fun h -> carried h b norm_length /\ length b >= norm_length+1)) 
    (ensures (fun h0 _ h1 -> updated h0 h1 b (2*norm_length-1)
      /\ carried h0 b norm_length /\ carried2 h1 b
      (* /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime *)
      /\ v (get h1 b 0) = v (get h0 b 0) + v (get h0 b 8)
      /\ v (get h1 b 4) = v (get h0 b 4) + v (get h0 b 8)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i < norm_length+1 /\ i <> 0 /\ i <> 4)
			   ==> v (get h1 b i) = v (get h0 b i))
      ))
let carry_top_to_0 b =
  //@@
  let h0 = HST.get() in
  let btop = index b 8ul in
  let b0 = index b 0ul in
  let b4 = index b 4ul in
  (* lemma_helper_3 b0 btop; *)
  (* lemma_helper_3 b4 btop; *)
  upd b 0ul (b0 |+ btop);
  upd b 4ul (b4 |+ btop)
  (* let h1 = HST.get() in *)
  (* freduce_degree_lemma_0 h0 h1 b 0 *)

#reset-options

(* Comes from the specification of the % function, missing in Z3 theory. Must go to axioms *)
(* assume val lemma_helper_6: x:wide -> Lemma  *)
(*  ((v x < pow2 56 + pow2 18 /\ v x >= pow2 56) ==> v x % pow2 56 < pow2 18) *)

(* val lemma_helper_7: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 56 /\ v y < pow2 17)) *)
(*   (ensures (v x + v y < pow2 57 /\ v x + v y < pow2 128)) *)
(* let lemma_helper_7 x y = pow2_increases_lemma 56 18; pow2_increases_lemma 128 57 *)

(* val lemma_helper_8: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 73 /\ v y < 2)) *)
(*   (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 74)) *)
(* let lemma_helper_8 x y = pow2_increases_lemma 128 73 *)

(* val lemma_helper_9: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 56 /\ v y < pow2 18)) *)
(*   (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 57)) *)
(* let lemma_helper_9 x y = pow2_increases_lemma 128 57; pow2_increases_lemma 56 18 *)

(* (\* Comes from the fact that '/' decreases, missing from F*/Z3 theory. Must go to axioms *\) *)
(* assume val lemma_helper_10: x:wide -> n:nat -> Lemma *)
(*   (requires (v x < pow2 n /\ n >= 56)) *)
(*   (ensures (n >= 56 /\ v x / pow2 56 < pow2 (n-56))) *)

(* val lemma_helper_11: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 56 /\ v y < 2)) *)
(*   (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 57)) *)
(* let lemma_helper_11 x y = pow2_increases_lemma 128 57 *)

(* val lemma_helper_12: x:wide{v x < pow2 56} -> y:wide -> ny:nat{ny < 56 /\ v y < pow2 ny} -> Lemma *)
(*   ( (v x + v y) / pow2 56 = 1 ==> (v x + v y) % pow2 56 < pow2 ny) *)
(* let lemma_helper_12 x y ny = ()   *)

(* #reset-options *)

val full_update: b:bigint_wide -> r0:s128 -> r1:s128 -> r2:s128 -> r3:s128 -> r4:s128 -> 
  r5:s128 -> r6:s128 -> r7:s128 -> r8:s128 -> STL unit
  (requires (fun h -> live h b /\ length b >= norm_length+1))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (norm_length+1) 
    /\ v (get h1 b 0) = v r0 /\ v (get h1 b 1) = v r1 /\ v (get h1 b 2) = v r2
    /\ v (get h1 b 3) = v r3 /\ v (get h1 b 4) = v r4 /\ v (get h1 b 5) = v r5
    /\ v (get h1 b 6) = v r6 /\ v (get h1 b 7) = v r7 /\ v (get h1 b 8) = v r8 ))
let full_update b r0 r1 r2 r3 r4 r5 r6 r7 r8 =    
  (* let h0 = HST.get() in *)
  upd b 0ul r0;
  (* let h1 = HST.get() in *)
  (* upd_lemma h0 h1 b 0 r0; *)
  upd b 1ul r1;
  (* let h2 = HST.get() in *)
  (* upd_lemma h1 h2 b 1 r1; *)
  upd b 2ul r2; 
  (* let h3 = HST.get() in *)
  (* upd_lemma h2 h3 b 2 r2; *)
  upd b 3ul r3; 
  (* let h4 = HST.get() in *)
  (* upd_lemma h3 h4 b 3 r3; *)
  upd b 4ul r4;
  (* let h5 = HST.get() in *)
  (* upd_lemma h4 h5 b 4 r4; *)
  upd b 5ul r5; 
  (* let h6 = HST.get() in *)
  (* upd_lemma h5 h6 b 5 r5; *)
  upd b 6ul r6;
  (* let h7 = HST.get() in *)
  (* upd_lemma h6 h7 b 6 r6; *)
  upd b 7ul r7; 
  (* let h8 = HST.get() in *)
  (* upd_lemma h7 h8 b 7 r7; *)
  upd b 8ul r8;
  (* let h9 = HST.get() in *)
  (* upd_lemma h8 h9 b 8 r8 *)
  ()
  
let carried3 h1 (b:bigint_wide) : GTot Type0 = 
  live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) < pow2 56 /\ v (get h1 b 1) < pow2 56
  /\ v (get h1 b 2) < pow2 56 /\ v (get h1 b 3) < pow2 56
  /\ v (get h1 b 4) < pow2 56 /\ v (get h1 b 5) < pow2 56
  /\ v (get h1 b 7) < pow2 56 /\ v (get h1 b 6) < pow2 56
  /\ v (get h1 b 8) < 2
  /\ (v (get h1 b 8) = 1 ==> ( v (get h1 b 5) < pow2 18
		    /\ v (get h1 b 6) < 2
		    /\ v (get h1 b 7) < 2 ))

val carry2: b:bigint_wide -> STL unit
  (requires (fun h -> carried2 h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (norm_length+1)
    /\ carried3 h1 b
    (* /\ eval h1 b (norm_length+1) = eval h0 b norm_length *)
    (* /\ modifies !{getRef b} h0 h1 *)
    ))
let carry2 b = 
  (* admit(); // Timeout *)
  (* let h0 = HST.get() in *)
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  let b5 = index b 5ul in
  let b6 = index b 6ul in
  let b7 = index b 7ul in
  let r0 = trim_2_56 b0 in
  let c1 = b0 |>> 56ul in
  (* lemma_helper_10 b0 73; *)
  (* cut (True /\ v c1 < pow2 17);  *)
  (* lemma_helper_7 b1 c1; *)
  let d1 = b1 |+ c1 in 
  let r1 = trim_2_56 d1 in
  (* cut (True /\ v r1 < pow2 56); *)
  let c2 = d1 |>> 56ul in
  (* lemma_helper_10 d1 57; *)
  (* lemma_helper_12 b1 c1 17; *)
  (* cut (v c2 < 2 /\ (v c2 = 1 ==> v r1 < pow2 17));  *)
  (* lemma_helper_11 b2 c2;  *)
  let d2 = b2 |+ c2 in 
  let r2 = trim_2_56 d2 in
  (* cut (True /\ v r2 < pow2 56); *)
  let c3 = d2 |>> 56ul in
  (* lemma_helper_10 d2 57; *)
  (* lemma_helper_12 b2 c2 1; *)
  (* cut (v c3 < 2 /\ (v c3 = 1 ==> v r2 < 2));  *)
  (* lemma_helper_11 b3 c3;  *)
  let d3 = b3 |+ c3 in
  let r3 = trim_2_56 d3 in
  (* cut (True /\ v r3 < pow2 56); *)
  let c4 = d3 |>> 56ul in 
  (* lemma_helper_10 d3 57; *)
  (* lemma_helper_12 b3 c3 1; *)
  (* cut (v c4 < 2 /\ (v c4 = 1 ==> v r3 < 2)); *)
  (* lemma_helper_8 b4 c4; *)
  let d4 = b4 |+ c4 in
  let r4 = trim_2_56 d4 in
  (* cut (True /\ v r4 < pow2 56); *)
  let c5 = d4 |>> 56ul in 
  (* lemma_helper_10 d4 74; *)
  (* cut (True /\ v c5 < pow2 18);  *)
  (* lemma_helper_9 b5 c5;  *)
  let d5 = b5 |+ c5 in 
  let r5 = trim_2_56 d5 in
  (* cut (True /\ v r5 < pow2 56); *)
  let c6 = d5 |>> 56ul in 
  (* lemma_helper_10 d5 57; *)
  (* lemma_helper_12 b5 c5 18; *)
  (* cut (v c6 < 2 /\ (v c6 = 1 ==> v r5 < pow2 18));  *)
  (* lemma_helper_11 b6 c6; *)
  let d6 = b6 |+ c6 in
  let r6 = trim_2_56 d6 in
  (* cut (True /\ v r6 < pow2 56); *)
  let c7 = d6 |>> 56ul in
  (* lemma_helper_10 d6 57; *)
  (* lemma_helper_12 b6 c6 1; *)
  (* cut (v c7 < 2 /\ (v c7 = 1 ==> (v r6 < 2 /\ v c6 = 1)));  *)
  (* lemma_helper_11 b7 c7;  *)
  let d7 = b7 |+ c7 in 
  let r7 = trim_2_56 d7 in
  (* cut (True /\ v r7 < pow2 56); *)
  let c8 = d7 |>> 56ul in 
  (* lemma_helper_10 d7 57; *)
  (* lemma_helper_12 b7 c7 1; *)
  (* cut (v c8 = 1 ==> v r7 < 2); *)
  (* cut (v c8 = 1 ==> (v r7 < 2 /\ v c7 = 1));  *)
  (* cut (v c8 = 1 ==> (v r7 < 2 /\ v r6 < 2 /\ v r5 < pow2 18));  *)
  full_update b r0 r1 r2 r3 r4 r5 r6 r7 c8

(* val lemma_helper_13: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 56 /\ v y < 2)) *)
(*   (ensures (v x + v y < pow2 platform_wide /\ v x + v y < pow2 57)) *)
(* let lemma_helper_13 x y =  *)
(*   pow2_increases_lemma platform_wide 57 *)

let carried4 h1 (b:bigint_wide) : GTot Type0 = 
  live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) < pow2 57 /\ v (get h1 b 1) < pow2 56
  /\ v (get h1 b 2) < pow2 56 /\ v (get h1 b 3) < pow2 56
  /\ v (get h1 b 4) < pow2 57 /\ v (get h1 b 5) < pow2 56
  /\ v (get h1 b 6) < pow2 56 /\ v (get h1 b 7) < pow2 56
  /\ ((v (get h1 b 0) >= pow2 56 \/ v (get h1 b 4) >= pow2 56)
      ==> (v (get h1 b 5) < pow2 18 /\ v (get h1 b 6) < 2 /\ v (get h1 b 7) < 2))

val carry2_top_to_0: b:bigint_wide -> STL unit 
    (requires (fun h -> carried3 h b))
    (ensures (fun h0 _ h1 -> updated h0 h1 b (norm_length+1)
      /\ carried4 h1 b
      (* /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime *)
      ))
let carry2_top_to_0 b =
  //@@
  let h0 = HST.get() in
  let btop = index b 8ul in
  let b0 = index b 0ul in
  let b4 = index b 4ul in
  (* lemma_helper_13 b0 btop; *)
  (* lemma_helper_13 b4 btop; *)
  upd b 0ul (b0 |+ btop);
  upd b 4ul (b4 |+ btop)
  (* let h1 = HST.get() in *)
  (* freduce_degree_lemma_0 h0 h1 b 0 *)

(* val lemma_helper_14: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 57 /\ v y < 2)) *)
(*   (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 58)) *)
(* let lemma_helper_14 x y = pow2_increases_lemma 128 58 *)

(* val lemma_helper_15: x:wide -> Lemma *)
(*   (requires (True)) *)
(*   (ensures (v x / pow2 56 > 0 ==> v x >= pow2 56)) *)
(* let lemma_helper_15 x = *)
(*   //@@ *)
(*   () *)

(* val lemma_helper_16: x:wide -> y:wide -> Lemma *)
(*   (requires (True)) *)
(*   (ensures ((v x < pow2 18 /\ v y < pow2 2) ==> (v x + v y < pow2 128 /\ v x + v y < pow2 56))) *)
(* let lemma_helper_16 x y =  *)
(*   //@@ *)
(*   pow2_increases_lemma 128 19; pow2_increases_lemma 56 19 *)

val full_update2: b:bigint_wide -> r0:s128{v r0 < pow2 56} -> r1:s128{v r1 < pow2 56} -> 
  r2:s128{v r2 < pow2 56} -> r3:s128{v r3 < pow2 56} -> r4:s128{v r4 < pow2 56} -> 
  r5:s128{v r5 < pow2 56} -> STL unit
  (requires (fun h -> live h b /\ length b >= norm_length+1
    /\ v (get h b 6) < pow2 56 /\ v (get h b 7) < pow2 56))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (norm_length+1) 
    /\ v (get h1 b 0) = v r0 /\ v (get h1 b 1) = v r1 /\ v (get h1 b 2) = v r2
    /\ v (get h1 b 3) = v r3 /\ v (get h1 b 4) = v r4 /\ v (get h1 b 5) = v r5
    /\ v (get h1 b 6) = v (get h0 b 6)
    /\ v (get h1 b 7) = v (get h0 b 7) ))
    (* /\ norm h1 b)) *)
let full_update2 b r0 r1 r2 r3 r4 r5 =    
  //@@
  (* let h0 = HST.get() in *)
  upd b 0ul r0;
  (* let h1 = HST.get() in *)
  (* upd_lemma h0 h1 b 0 r0; *)
  upd b 1ul r1;
  (* let h2 = HST.get() in *)
  (* upd_lemma h1 h2 b 1 r1; *)
  upd b 2ul r2; 
  (* let h3 = HST.get() in *)
  (* upd_lemma h2 h3 b 2 r2; *)
  upd b 3ul r3; 
  (* let h4 = HST.get() in *)
  (* upd_lemma h3 h4 b 3 r3; *)
  upd b 4ul r4;
  (* let h5 = HST.get() in *)
  (* upd_lemma h4 h5 b 4 r4; *)
  upd b 5ul r5
  (* let h6 = HST.get() in *)
  (* upd_lemma h5 h6 b 5 r5 *)

val carry3: b:bigint_wide -> STL unit
  (requires (fun h -> carried4 h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (norm_length+1)
    (* /\ Standardized h1 b *)
    (* /\ eval h1 b norm_length = eval h0 b norm_length *)
    ))
let carry3 b =
//  admit(); Partial functional correctness
  (* let h0 = HST.get() in *)
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  let b5 = index b 5ul in
  let r0 = trim_2_56 b0 in
  let c1 = b0 |>> 56ul in
  (* lemma_helper_10 b0 57; *)
  (* cut (v c1 = 1 ==> v b5 < pow2 18);   *)
  (* lemma_helper_7 b1 c1; *)
  let d1 = b1 |+ c1 in 
  let r1 = trim_2_56 d1 in
  let c2 = d1 |>> 56ul in
  cut (v c2 = 1 ==> v b5 < pow2 18);
  (* lemma_helper_10 d1 57; *)
  (* lemma_helper_12 b1 c1 17; *)
  (* lemma_helper_11 b2 c2;  *)
  let d2 = b2 |+ c2 in 
  let r2 = trim_2_56 d2 in
  let c3 = d2 |>> 56ul in
  (* cut (v c3 = 1 ==> v b5 < pow2 18);  *)
  (* lemma_helper_10 d2 57; *)
  (* lemma_helper_12 b2 c2 1; *)
  (* lemma_helper_11 b3 c3;  *)
  let d3 = b3 |+ c3 in
  let r3 = trim_2_56 d3 in
  (* cut (True /\ v r3 < pow2 56); *)
  let c4 = d3 |>> 56ul in 
  (* cut (v c4 = 1 ==> v b5 < pow2 18);  *)
  (* lemma_helper_10 d3 57; *)
  (* lemma_helper_12 b3 c3 1;  *)
  (* lemma_helper_14 b4 c4;  *)
  let d4 = b4 |+ c4 in
  let r4 = trim_2_56 d4 in
  let c5 = d4 |>> 56ul in 
  (* lemma_helper_10 d4 58; *)
  (* lemma_helper_15 d4; *)
  (* cut (v d4 >= pow2 56ul ==> (v c4 = 1 \/ v b4 >= pow2 56));  *)
  (* cut ((v c4 = 1 ==> v b5 < pow2 18) /\ (v b4 >= pow2 56ul ==> v b5 < pow2 18));  *)
  (* cut (v d4 >= pow2 56ul ==> v b5 < pow2 18);    *)
  (* cut (v c5 > 0 ==> (v b5 < pow2 18 /\ v c5 < pow2 2));  *)
  (* lemma_helper_16 b5 c5;  *)
  let d5 = b5 |+ c5 in 
  full_update2 b r0 r1 r2 r3 r4 d5
  (* let h1 = HST.get() in *)
  (* P448 = 2^448 - 2^224 - 1, hence *)
  (*   a[0] + 2^56*a[1] + 2^112*a[2] + 2^168*a[3] + 2^224*a[4]  *)
  (*           + 2^280*a[5] + 2^336*a[6] + 2^392*a[7] + 2^448*a[8] *)
  (* = (a[0]+a[8]) + 2^56*a[1] + 2^112*a[2] + 2^168*a[3] + 2^224*(a[4]+a[8]) *)
  (* 		    + 2^280*a[5] + 2^336*a[6] + 2^392*a[7]  *)
  (* admitP (True /\ eval h1 b norm_length = eval h0 b norm_length) *)

#reset-options

(* val lemma_helper_4: x:wide -> y:wide -> Lemma *)
(*   (requires (v x < pow2 (platform_wide - 3) /\ v y < pow2 (platform_wide - 3))) *)
(*   (ensures (v x + v y < pow2 (platform_wide - 2) /\ v x < pow2 (platform_wide - 2))) *)
(*   [SMTPat (v x); SMTPat (v y)] *)
(* let lemma_helper_4 x y = () *)

(* #reset-options *)

(* val lemma_helper_5: h0:heap -> h1:heap -> b:bigint_wide -> Lemma *)
(*   (requires (reducible h0 b /\ reduced h0 h1 b)) *)
(*   (ensures (reducible2 h1 b)) *)
(* let lemma_helper_5 h0 h1 b =  *)
(*   //@@ *)
(*   () *)

(* val upd_lemma_2: h0:heap -> h1:heap -> b:bigint_wide -> idx:nat -> x:wide -> Lemma *)
(*   (requires (updated h0 h1 b (norm_length+1) /\ idx < lengthb /\ h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx x))) *)
(*   (ensures (live h1 b /\ live h0 b /\ updated h0 h1 b (norm_length+1) /\ idx < lengthb  *)
(* 	    /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i <> idx /\ i < length b) ==> v (get h1 b i) = v (get h0 b i)) *)
(* 	    /\ eval h1 b idx = eval h0 b idx)) *)
(* let upd_lemma_2 h0 h1 b idx x =  *)
(*   //@@ *)
(*   eval_eq_lemma h0 h1 b b idx *)

(* val upd_lemma_3: h0:heap -> h1:heap -> h2:heap -> b:bigint_wide -> idx:nat -> x:wide -> Lemma *)
(*   (requires (updated h0 h1 b (2*norm_length-1) /\ updated h1 h2 b (2*norm_length-1)  *)
(*     /\ reduced2 h0 h1 b *)
(*     /\ (forall (i:nat). {:pattern (v (get h2 b i))} i < norm_length ==> v (get h2 b i) = v (get h1 b i)) )) *)
(*   (ensures (reduced2 h0 h2 b)) *)
(* let upd_lemma_3 h0 h1 h2 b idx x =  *)
(*   //@@ *)
(*   ()  *)

val freduce_degree: b:bigint_wide -> STL unit
  (requires (fun h -> reducible h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (2*norm_length-1)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime *)
    /\ carriable h1 b 0))
let freduce_degree b =
  //@@
  (* let h0 = HST.get() in *)
  freduce_degree_1 b;
  (* let h1 = HST.get() in *)
  (* lemma_helper_5 h0 h1 b;  *)
  freduce_degree_2 b;
  (* let h2 = HST.get() in *)
  (* cut (reduced2 h1 h2 b); *)
  (* cut (True /\ eval h2 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime); *)
  upd b 8ul (Hacl.UInt128.of_string "0")
  (* let h3 = HST.get() in  *)
  (* upd_lemma_2 h2 h3 b norm_length zero_wide;  *)
  (* upd_lemma_3 h1 h2 h3 b norm_length zero_wide;  *)
  (* freduce_lemma_0 h0 h1 h3 b *)

#reset-options

val freduce_coefficients: b:bigint_wide -> STL unit
  (requires (fun h -> carriable h b 0))
  (ensures (fun h0 _ h1 -> updated h0 h1 b (norm_length+1)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime *)
    (* /\ Standardized h1 b *)
    ))
let freduce_coefficients b =
  //@@
  (* let h0 = HST.get() in *)
  let zero_wide = (Hacl.UInt128.of_string "0") in
  upd b nlength zero_wide; (* Unnecessary, to remove *)
  (* let h1 = HST.get() in *)
  (* eval_eq_lemma h0 h1 b b norm_length;  *)
  (* cut (True /\ eval h1 b (norm_length+1) = eval h1 b norm_length);  *)
  carry b 0ul; 
  carry_top_to_0 b; 
  (* let h2 = HST.get() in *)
  upd b nlength zero_wide; 
  (* let h3 = HST.get() in *)
  (* eval_eq_lemma h2 h3 b b norm_length; *)
  carry2 b; 
  carry2_top_to_0 b;
  carry3 b

(* Not verified *)
val normalize:
  b:bigint -> Stl unit 
  (* (requires (fun h -> Standardized h b)) *)
  (* (ensures (fun h0 _ h1 -> Standardized h0 b /\ Standardized h1 b *)
  (*   /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime)) *)
let normalize b =
  (* admit(); // Not machine checked *)
  let two56m1 = Hacl.UInt64.of_string "0xffffffffffffff" in
  let two56m2 = Hacl.UInt64.of_string "0xfffffffffffffe" in  
  let one = Hacl.UInt64.of_string "1" in
  let b7 = index b 7ul in
  let b6 = index b 6ul in
  let b5 = index b 5ul in
  let b4 = index b 4ul in
  let b3 = index b 3ul in
  let b2 = index b 2ul in
  let b1 = index b 1ul in
  let b0 = index b 0ul in
  let mask = Hacl.UInt64.eq_mask b7 two56m1 in
  let mask = Hacl.UInt64.logand mask (Hacl.UInt64.eq_mask b6 two56m1) in
  let mask = Hacl.UInt64.logand mask (Hacl.UInt64.eq_mask b5 two56m1) in
  (* Case where b == 2^448-2^224-1 *)
  let mask1 = Hacl.UInt64.logand mask (Hacl.UInt64.eq_mask b4 two56m2) in
  let mask1 = Hacl.UInt64.logand mask1 (Hacl.UInt64.eq_mask b3 two56m1) in
  let mask1 = Hacl.UInt64.logand mask1 (Hacl.UInt64.eq_mask b2 two56m1) in
  let mask1 = Hacl.UInt64.logand mask1 (Hacl.UInt64.eq_mask b1 two56m1) in
  let mask1 = Hacl.UInt64.logand mask1 (Hacl.UInt64.eq_mask b0 two56m1) in
  (* Case where b >= 2^448-2^224-1 && b < 2^448 *)
  let mask2 = Hacl.UInt64.logand mask (Hacl.UInt64.eq_mask b4 two56m1) in
  let mask = Hacl.UInt64.logor mask1 mask2 in
  let mask' = Hacl.UInt64.lognot mask in // 0xfff... if mask == 0 , 0 else
  upd b 7ul (Hacl.UInt64.logand b7 mask'); // if b >= 2^448-2^224-1 then 0
  upd b 6ul (Hacl.UInt64.logand b6 mask'); // if b >= 2^448-2^224-1 then 0
  upd b 5ul (Hacl.UInt64.logand b5 mask'); // if b >= 2^448-2^224-1 then 0
  let b4' = Hacl.UInt64.logand (Hacl.UInt64.logxor b4 (Hacl.UInt64.of_string "0x1")) (Hacl.UInt64.of_string  "0x1") in
  // if b > 2^448-2^224-1 then 0 else 1
  upd b 4ul  (Hacl.UInt64.logor (Hacl.UInt64.logand b4' mask) (Hacl.UInt64.logand b4 mask'));
  // if b >= 2^448-2^224-1 then add 1
  upd b 0ul  (Hacl.UInt64.add b0 (Hacl.UInt64.logand mask one));
  // carry
  let mask3 = (Hacl.UInt64.of_string  "0xffffffffffffff") in
  let b0 = index b 0ul in let r0 = Hacl.UInt64.logand b0 mask3 in
  upd b 0ul (r0); 
  let c = Hacl.UInt64.shift_right b0 56ul in
  let b1 = index b 1ul in
  upd b 1ul (Hacl.UInt64.add b1 c);
  let b1 = index b 1ul in let r1 = Hacl.UInt64.logand b1 mask3 in
  upd b 1ul (r1); 
  let c = Hacl.UInt64.shift_right b1 56ul in
  let b2 = index b 2ul in
  upd b 2ul (Hacl.UInt64.add b2 c);
  let b2 = index b 2ul in let r2 = Hacl.UInt64.logand b2 mask3 in
  upd b 2ul (r2); 
  let c = Hacl.UInt64.shift_right b2 56ul in
  let b3 = index b 3ul in
  upd b 3ul (Hacl.UInt64.add b3 c);
  let b3 = index b 3ul in let r3 = Hacl.UInt64.logand b3 mask3 in
  upd b 3ul (r3); 
  let c = Hacl.UInt64.shift_right b3 56ul in
  let b4 = index b 4ul in
  upd b 4ul (Hacl.UInt64.add b4 c);
  let b4 = index b 4ul in
  upd b 4ul (Hacl.UInt64.logor (Hacl.UInt64.logand (Hacl.UInt64.logand one b4) mask) (Hacl.UInt64.logand b4 mask'))

let fits_2_57 h (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length
  /\ vv (get h b 0) < pow2 57  /\ vv (get h b 1) < pow2 57
  /\ vv (get h b 2) < pow2 57  /\ vv (get h b 3) < pow2 57
  /\ vv (get h b 4) < pow2 57  /\ vv (get h b 5) < pow2 57
  /\ vv (get h b 6) < pow2 57  /\ vv (get h b 7) < pow2 57

(* val lemmma_bigzero_0: unit -> Lemma (pow2 57 - 2 > pow2 56 /\ pow2 57 - 4 > pow2 56 /\ pow2 57 + pow2 56 < pow2 64) *)
(* let lemmma_bigzero_0 () =  *)
(*   pow2_double_sum 56; *)
(*   pow2_double_sum 57; *)
(*   pow2_increases_lemma 64 58; *)
(*   pow2_increases_lemma 57 1; *)
(*   pow2_increases_lemma 57 2; *)
(*   pow2_increases_lemma 56 1; *)
(*   pow2_increases_lemma 56 2 *)

val add_big_zero: bigint -> Stl unit
let add_big_zero b =
  (* admit(); // Must reduce timeout *)
  (* let h0 = HST.get() in *)
  let two57m2 = Hacl.UInt64.of_string  "0x1fffffffffffffe" in // 2^57 - 2
  let two57m4 = Hacl.UInt64.of_string "0x1fffffffffffffc" in // 2^56 - 4
  (* admitP (v two57m2 = pow2 57 - 2 /\ v two57m4 = pow2 57 -4); *)
  (* lemmma_bigzero_0 (); *)
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  let b5 = index b 5ul in
  let b6 = index b 6ul in
  let b7 = index b 7ul in
  upd b 0ul (Hacl.UInt64.add b0 two57m2);
  upd b 1ul (Hacl.UInt64.add b1 two57m2); 
  upd b 2ul (Hacl.UInt64.add b2 two57m2); 
  upd b 3ul (Hacl.UInt64.add b3 two57m2); 
  upd b 4ul (Hacl.UInt64.add b4 two57m4);
  upd b 5ul (Hacl.UInt64.add b5 two57m2);
  upd b 6ul (Hacl.UInt64.add b6 two57m2); 
  upd b 7ul (Hacl.UInt64.add b7 two57m2)
  (* let h1 = HST.get() in *)
  (* admitP(True /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime) *)
