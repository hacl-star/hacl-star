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
let op_Bar_Subtraction (x:s128) (y:s128) : Tot s128 = Hacl.UInt128.sub x y

(* let satisfies_modulo_constraints h b =  *)
(*   length b >= 2*norm_length-1 && getTemplate b = templ *)
(*   && maxValue h b < pow2 67 *)

(* val lemma_satisfies: h:heap -> b:bigint_wide -> n:nat -> Lemma *)
(*   (requires (live h b /\ (forall (i:nat). i < length b ==> v (get h b i) < pow2 n))) *)
(*   (ensures  (live h b /\ maxValue h b < pow2 n)) *)
(* let lemma_satisfies h b n = ()   *)

let sum_satisfies_constraints h0 h1 cpy a b : Lemma (True) = ()
(*   //@@ *)
(*   pow2_double_sum 32; *)
(*   cut (forall (i:nat). {:pattern (v (get h1 cpy i))} i < norm_length  *)
(* 	    ==> v (get h1 cpy i) < pow2 33); *)
(*   cut (forall (i:nat). {:pattern (v (get h1 cpy i))} (i >= norm_length /\ i < getLength h1 cpy) *)
(* 	    ==> v (get h1 cpy i) = 0); *)
(*   cut(forall (i:nat). {:pattern (v (get h1 cpy i))} i < getLength h1 cpy *)
(* 	   ==> v (get h1 cpy i) < pow2 33); *)
(*   lemma_satisfies h1 cpy 33; *)
(*   pow2_increases_lemma 67 33 *)

(* let n0 = ndiff' *)
(* let n1 = ndiff *)

let difference_satisfies_constraints h0 h1 cpy a b : Lemma (True) = ()
(*   //@@ *)
(*   cut(forall (i:nat). {:pattern (v (get h1 cpy i))} i < getLength h1 cpy *)
(* 	   ==> v (get h1 cpy i) < pow2 34); *)
(*   lemma_satisfies h1 cpy 34; *)
(*   pow2_increases_lemma 67 34 *)

(* val lemma_satisfies_2: h:heap -> b:bigint -> Lemma  *)
(*   (requires (Standardized h b)) *)
(*   (ensures  (Standardized h b /\ maxValueNorm h b < pow2 32)) *)
(* let lemma_satisfies_2 h b = () *)

(* val lemma_satisfies_4: a:nat -> b:nat -> c:pos -> d:pos -> Lemma (requires (a < c /\ b < d)) *)
(* 							    (ensures (a * b < c * d)) *)
(* let lemma_satisfies_4 a b c d = () *)

(* val lemma_satisfies_3: b:nat -> c:nat -> Lemma *)
(*   (requires (b < pow2 32 /\ c < pow2 32)) *)
(*   (ensures (norm_length * b * c < pow2 67)) *)
(* let lemma_satisfies_3 b c =  *)
(*   //@@ *)
(*   cut (True /\ 8 = pow2 3); *)
(*   pow2_exp_lemma 32 32; *)
(*   pow2_exp_lemma 3 64; *)
(*   Axiomatic.paren_mul_right norm_length b c; *)
(*   lemma_satisfies_4 b c (pow2 32) (pow2 32) *)

let mul_satisfies_constraints h0 h1 res a b : Lemma (True) = ()
(*   lemma_satisfies_2 h0 a; *)
(*   lemma_satisfies_2 h0 b; *)
(*   lemma_satisfies_3 (maxValueNorm h0 a) (maxValueNorm h0 b) *)

let updated h0 h1 (b:bigint_wide) (len:nat) : GTot Type0 = 
  live h0 b /\ live h1 b /\ length b >= len /\ length b = length b

val templ_large: nat -> Tot pos
let templ_large i = 64

type bigint_large = b:buffer s128(* {Bigint.t b = templ_large} *)

(* val lemma_helper_00: n:nat -> m:pos -> Lemma (requires (n < m)) (ensures (n % m = n)) *)
(* let lemma_helper_00 n m = Axiomatic.modulo_lemma_0 n m *)

(* val lemma_helper_01: n:nat -> m:pos -> Lemma (requires (n < m)) (ensures (pow2 n % pow2 m = pow2 n)) *)
(* let lemma_helper_01 n m = pow2_increases_lemma m n; lemma_helper_00 (pow2 n) (pow2 m) *)

(* val lemma_helper_02: unit -> Lemma (pow2 64 - 1 < pow2 128 /\ pow2 32 - 1 < pow2 128 /\ pow2 64 - pow2 32 + 1 < pow2 128) *)
(* let lemma_helper_02 () = pow2_increases_lemma 128 64; pow2_increases_lemma 64 32 *)

(* val lemma_helper_04: a:int -> b:int -> c:int -> d:int -> Lemma (a * (b - c + d) = a * b - a * c + a * d) *)
(* let lemma_helper_04 a b c d =  *)
(*   //@@ *)
(*   () *)

(* val lemma_helper_03: h:heap -> b:bigint_large -> Lemma *)
(*   (requires (live h b /\ length b >= 4  *)
(*     /\ v (get h b 0) = pow2 64 - 1 *)
(*     /\ v (get h b 1) = pow2 32 - 1 *)
(*     /\ v (get h b 2) = 0 *)
(*     /\ v (get h b 3) = pow2 64 - pow2 32 + 1)) *)
(*   (ensures (live h b /\ length b >= 4 /\ eval h b 4 = reveal prime)) *)
(* let lemma_helper_03 h b =  *)
(*   //@@ *)
(*   eval_definition h b 4; *)
(*   eval_definition h b 3; *)
(*   eval_definition h b 2; *)
(*   eval_definition h b 1;  *)
(*   bitweight_definition templ_large 2; *)
(*   bitweight_definition templ_large 1; *)
(*   bitweight_definition templ_large 0; *)
(*   Axiomatic.distributivity_sub_right (pow2 64) (pow2 32) 1; *)
(*   lemma_helper_04 (pow2 192) (pow2 64) (pow2 32) 1; *)
(*   Lemmas.pow2_exp_1 192 64; *)
(*   Lemmas.pow2_exp_1 192 32; *)
(*   Lemmas.pow2_exp_1 64 32 *)

val kPrime: unit -> STL (bigint_large)
  (requires (fun h -> True)) 
  (ensures (fun h0 b h1 -> (* not(contains h0 (getRef b)) *)
    (* /\  *)live h1 b /\ length b = 4
    (* /\ eval h1 b 4  = reveal prime *)
    /\ v (get h1 b 0) = pow2 64 - 1
    /\ v (get h1 b 1) = pow2 32 - 1
    /\ v (get h1 b 2) = 0
    /\ v (get h1 b 3) = pow2 64 - pow2 32 + 1
    /\ modifies Set.empty h0 h1))
let kPrime () =
  //@@
  let a = create (Hacl.UInt128.of_string "0") 4ul in
  let v_2_64 = (Hacl.UInt128.of_string "1") |<< 64ul in
  let v_2_32 = (Hacl.UInt128.of_string "1") |<< 32ul in 
  (* lemma_helper_01 32 128; *)
  (* lemma_helper_01 64 128;  *)
  (* pow2_increases_lemma 128 64; *)
  (* pow2_increases_lemma 64 32; *)
  (* pow2_increases_lemma 128 32;   *)
  let a0 = v_2_64 |- (Hacl.UInt128.of_string "1") in 
  let a1 = v_2_32 |- (Hacl.UInt128.of_string "1") in 
  let a3 = v_2_64 |- v_2_32 |+ (Hacl.UInt128.of_string "1") in 
  (* lemma_helper_02 (); *)
  upd a 0ul a0; 
  upd a 1ul a1;
  upd a 3ul a3;
  (* let h = ST.get() in  *)
  (* lemma_helper_03 h a; *)
  a

(* val lemma_helper_10: unit -> Lemma *)
(*   (pow2 64 % pow2 128 = pow2 64 /\ pow2 64 - 1 < pow2 128 /\ pow2 110 + pow2 32 < pow2 128 *)
(*    /\ pow2 110 % pow2 128 = pow2 110 /\ pow2 32 % pow2 128 = pow2 32 /\ pow2 110 + pow2 32 - 1 < pow2 128 *)
(*    /\ pow2 46 % pow2 128 = pow2 46 /\ pow2 64 - pow2 46 < pow2 128 /\ pow2 64 > pow2 46 *)
(*    /\ pow2 64 - pow2 32 < pow2 128 /\ pow2 64 > pow2 32) *)
(* let lemma_helper_10 () =  *)
(*   //@@ *)
(*   lemma_helper_01 32 128; *)
(*   lemma_helper_01 46 128; *)
(*   lemma_helper_01 64 128; *)
(*   lemma_helper_01 110 128; *)
(*   pow2_increases_lemma 128 110; *)
(*   pow2_increases_lemma 128 111; *)
(*   pow2_increases_lemma 110 32; *)
(*   Lemmas.pow2_double_sum 110; *)
(*   pow2_increases_lemma 128 64; *)
(*   pow2_increases_lemma 64 46; *)
(*   pow2_increases_lemma 46 32 *)

val zero_110: unit -> STL bigint_large
  (requires (fun h -> True)) 
  (ensures (fun h0 b h1 -> (* not(contains h0 (getRef b)) *)
    (* /\  *)live h1 b /\ length b = 4
    (* /\ eval h1 b 4 = reveal prime *)
    /\ v (get h1 b 0) = pow2 64 - 1
    /\ v (get h1 b 1) = pow2 110 + pow2 32 - 1
    /\ v (get h1 b 2) = pow2 64 - pow2 46
    /\ v (get h1 b 3) = pow2 64 - pow2 32
    /\ modifies Set.empty h0 h1))
let zero_110 () =
  //@@
  (* lemma_helper_10 (); *)
  let v2_32 = (Hacl.UInt128.of_string "1") |<< 32ul in
  let v2_46 = (Hacl.UInt128.of_string "1") |<< 46ul in
  let v2_64 = (Hacl.UInt128.of_string "1") |<< 64ul in
  let v2_110 = (Hacl.UInt128.of_string "1") |<< 110ul in
  let two64m0 = v2_64 |- (Hacl.UInt128.of_string "1") in 
  let two110p32m0 = (v2_110 |+ v2_32) |- (Hacl.UInt128.of_string "1") in 
  let two64m46 = v2_64 |- v2_46 in 
  let two64m32 = v2_64 |- v2_32 in
  let a = create (Hacl.UInt128.of_string "0") 4ul in
  upd a 0ul two64m0;
  upd a 1ul two110p32m0;
  upd a 2ul two64m46;
  upd a 3ul two64m32; 
  (* let h = ST.get() in *)
  (* admitP(eval h a 4 = reveal prime /\ True); // Same as kPrime *)
  a

#reset-options

let reducible (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= 15 
  /\ v (get h b 0) < pow2 67 /\ v (get h b 1) < pow2 67 /\ v (get h b 2) < pow2 67
  /\ v (get h b 3) < pow2 67 /\ v (get h b 4) < pow2 67 /\ v (get h b 5) < pow2 67
  /\ v (get h b 6) < pow2 67 /\ v (get h b 7) < pow2 67 /\ v (get h b 8) < pow2 67
  /\ v (get h b 9) < pow2 67 /\ v (get h b 10) < pow2 67 /\ v (get h b 11) < pow2 67
  /\ v (get h b 12) < pow2 67 /\ v (get h b 13) < pow2 67 /\ v (get h b 14) < pow2 67

let reduced (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= 8
  /\ v (get h b 0) < pow2 72 /\ v (get h b 1) < pow2 72 /\ v (get h b 2) < pow2 72
  /\ v (get h b 3) < pow2 72 /\ v (get h b 4) < pow2 72 /\ v (get h b 5) < pow2 72
  /\ v (get h b 6) < pow2 72 /\ v (get h b 7) < pow2 72

let added70 (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= 15
  /\ v (get h b 0) < pow2 71 + pow2 67 /\ v (get h b 1) < pow2 71 + pow2 67 /\ v (get h b 2) < pow2 71 + pow2 67
  /\ v (get h b 3) < pow2 71 + pow2 67 /\ v (get h b 4) < pow2 71 + pow2 67 /\ v (get h b 5) < pow2 71 + pow2 67
  /\ v (get h b 6) < pow2 71 + pow2 67 /\ v (get h b 7) < pow2 71 + pow2 67
  /\ v (get h b 0) > pow2 70 /\ v (get h b 1) > pow2 70 /\ v (get h b 2) > pow2 70
  /\ v (get h b 3) > pow2 70 /\ v (get h b 4) > pow2 70 /\ v (get h b 5) > pow2 70
  /\ v (get h b 6) > pow2 70 /\ v (get h b 7) > pow2 70
  /\ v (get h b 8) < pow2 67
  /\ v (get h b 9) < pow2 67 /\ v (get h b 10) < pow2 67 /\ v (get h b 11) < pow2 67
  /\ v (get h b 12) < pow2 67 /\ v (get h b 13) < pow2 67 /\ v (get h b 14) < pow2 67

#reset-options

(* val lemma_helper_20: unit -> Lemma  *)
(*   (pow2 71 % pow2 128 = pow2 71 /\ pow2 39 % pow2 128 = pow2 39 /\ pow2 71 - pow2 39 < pow2 128 *)
(*    /\ pow2 40 % pow2 128 = pow2 40 /\ pow2 71 - pow2 40 < pow2 128 /\ pow2 71 < pow2 128 *)
(*    /\ pow2 39 < pow2 71 /\ pow2 40 < pow2 71 *)
(*    /\ pow2 71 - pow2 39 > pow2 70 /\ pow2 71 - pow2 40 > pow2 70 /\ pow2 71 > pow2 70) *)
(* let lemma_helper_20 () = *)
(*   //@@ *)
(*   lemma_helper_01 39 128; *)
(*   lemma_helper_01 40 128; *)
(*   lemma_helper_01 71 128; *)
(*   pow2_increases_lemma 128 39; *)
(*   pow2_increases_lemma 128 40; *)
(*   pow2_increases_lemma 71 40; *)
(*   pow2_increases_lemma 71 39; *)
(*   pow2_increases_lemma 70 40; *)
(*   pow2_increases_lemma 70 39 *)

(* #reset-options *)

(* val lemma_helper_21: unit -> Lemma  *)
(*   (pow2 67 + pow2 71 - pow2 39 < pow2 128 /\ pow2 67 + pow2 71 - pow2 40 < pow2 128 /\ pow2 67 + pow2 71 < pow2 128) *)
(* let lemma_helper_21 () =  *)
(*   //@@ *)
(*   lemma_helper_01 39 128; *)
(*   lemma_helper_01 40 128; *)
(*   lemma_helper_01 71 128; *)
(*   pow2_increases_lemma 67 39; *)
(*   pow2_increases_lemma 67 40; *)
(*   pow2_increases_lemma 71 68; *)
(*   Lemmas.pow2_double_sum 71; *)
(*   pow2_increases_lemma 128 72; *)
(*   pow2_increases_lemma 128 40; *)
(*   pow2_increases_lemma 71 40; *)
(*   pow2_increases_lemma 71 39; *)
(*   pow2_increases_lemma 70 40; *)
(*   pow2_increases_lemma 70 39 *)

(* #reset-options *)

val add_zero_71: b:bigint_wide -> STL unit
  (requires (fun h -> reducible h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b 15 /\ reducible h0 b /\ added70 h1 b
    (* /\ eval h1 b 15 % reveal prime = eval h0 b 15 % reveal prime *)
    (* /\ modifies !{getRef b} h0 h1 *)
    ))
let add_zero_71 b =
  //@@
  (* let h0 = ST.get() in *)
  (* lemma_helper_20 (); *)
  let zero71m39 = ((Hacl.UInt128.of_string "1") |<< 71ul) |- ((Hacl.UInt128.of_string "1") |<< 39ul) in
  let zero71m40 = ((Hacl.UInt128.of_string "1") |<< 71ul) |- ((Hacl.UInt128.of_string "1") |<< 40ul) in
  let zero71 = ((Hacl.UInt128.of_string "1") |<< 71ul) in 
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  let b5 = index b 5ul in
  let b6 = index b 6ul in
  let b7 = index b 7ul in
  (* lemma_helper_21 (); *)
  upd b 0ul (b0 |+ zero71m39); 
  upd b 1ul (b1 |+ zero71m39);
  upd b 2ul (b2 |+ zero71m39);
  upd b 3ul (b3 |+ zero71);
  upd b 4ul (b4 |+ zero71m39);
  upd b 5ul (b5 |+ zero71m39);
  upd b 6ul (b6 |+ zero71);
  upd b 7ul (b7 |+ zero71m40)
  (* let h1 = ST.get() in *)
  (* admitP (eval h1 b 15 % reveal prime = eval h0 b 15 % reveal prime /\ True) // Adding p256 << 39  *)

#reset-options

val add_top_to_bottom: b:bigint_wide -> STL unit
  (requires (fun h -> added70 h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b 15 /\ added70 h0 b /\ reduced h1 b
    (* /\ eval h1 b 8 % reveal prime = eval h0 b 15 % reveal prime *)
    (* /\ modifies !{getRef b} h0 h1 *)
    ))
let add_top_to_bottom b =
  admit(); //
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  let b5 = index b 5ul in
  let b6 = index b 6ul in
  let b7 = index b 7ul in  
  let b8 =  index b 8ul  in 
  let b9 =  index b 9ul  in 
  let b10 = index b 10ul in 
  let b11 = index b 11ul in
  let b12 = index b 12ul in 
  let b13 = index b 13ul in 
  let b14 = index b 14ul in
  // What has to be added to the lower limbs. Forall X, |toX| < 7 * max inputX < 2^3 * max inputX 
  // Hence forall X, |toX| < 2^3 * 2 ^ 67 = 2 ^ 70 so it should be safe to add that to b + zero71
  let v0 = ((((((b0 |+ b8) |+ b9) |- b11) |- b12) |- b13) |- b14) in
  let v1 = ((((b1 |+ b9) |+ b10) |- b12) |- b13) |- b14 in
  let v2 = (((b2 |+ b10) |+ b11) |- b13) |- b14 in
  let v3 = ((((b3 |+ (b11 |<< 1ul)) |- b9) |- b8) |+ (b12 |<< 1ul)) |+ b13 in
  let v4 = ((((b4 |+ (b12 |<< 1ul)) |- b9) |- b10) |+ (b13 |<< 1ul)) |+ b14 in
  let v5 = (((b5 |+ (b13 |<< 1ul)) |- b10) |- b11) |+ (b14 |<< 1ul) in
  let v6 = ((((b6 |+ b13) |- b8) |- b9) |+ (b14 |<< 1ul)) |+ b14 in
  let v7 = ((((b7 |+ b8) |- b10) |- b11) |- b12) |- b13 in
  upd b 0ul v0;
  upd b 1ul v1;
  upd b 2ul v2;
  upd b 3ul v3;
  upd b 4ul v4;
  upd b 5ul v5;
  upd b 6ul v6;
  upd b 7ul v7

// The input is the result of the multiplication, it is such that 
// forall X, inputX < 8 * 2^32 * 2^32 = 2^67
val freduce_degree': b:bigint_wide -> STL unit 
  (requires (fun h -> reducible h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b 15 /\ reducible h0 b /\ reduced h1 b
    (* /\ eval h1 b 8 % reveal prime = eval h0 b 15 % reveal prime *)
    (* /\ modifies !{getRef b} h0 h1 *)
    ))
let freduce_degree' b =
  add_zero_71 b;
  add_top_to_bottom b

#reset-options

(* val lemma_helper_31: a:int -> b:int -> c:int -> Lemma (requires (a <= b /\ b < c)) *)
(* 					        (ensures (a < c)) *)
(* let lemma_helper_31 a b c = () *)

(* val lemma_helper_32: a:nat -> b:nat -> Lemma (requires (a < pow2 104 /\ b <= pow2 104)) *)
(* 				          (ensures (a + b < pow2 105)) *)
(* let lemma_helper_32 a b = ()					   *)

(* val lemma_helper_30: b0:wide -> b1:wide -> Lemma *)
(*   (requires (v b0 < pow2 72 /\ v b1 < pow2 72)) *)
(*   (ensures ((v b1 * pow2 32) % pow2 128 = v b1 * pow2 32 *)
(* 	    /\ v b0 + (v b1 * pow2 32) < pow2 105 *)
(* 	    /\ v b0 + (v b1 * pow2 32) < pow2 128)) *)
(* let lemma_helper_30 b0 b1 = *)
(*   //@@ *)
(*   coerce  *)
(*     (requires (v b0 < pow2 72 /\ v b1 < pow2 72)) *)
(*     (ensures ((v b1 * pow2 32) % pow2 128 = v b1 * pow2 32 *)
(* 	    /\ v b0 + (v b1 * pow2 32) < pow2 105 *)
(* 	    /\ v b0 + (v b1 * pow2 32) < pow2 128)) *)
(*   (fun _ -> Lemmas.pow2_exp_1 72 32; *)
(* 	  pow2_increases_lemma 128 104; *)
(* 	  pow2_increases_lemma 104 72; *)
(* 	  Lemmas.pow2_double_sum 104; *)
(* 	  cut (True /\ v b1 * pow2 32 <= pow2 104);  *)
(* 	  lemma_helper_31 (v b1 * pow2 32) (pow2 104) (pow2 128); *)
(* 	  lemma_helper_32 (v b0) (v b1 * pow2 32); *)
(* 	  pow2_increases_lemma 128 105; *)
(* 	  lemma_helper_00 (v b1 * pow2 32) (pow2 128) ) *)

#reset-options

val shrink: tmp:bigint_large -> b:bigint_wide(* {getRef b <> getRef tmp} *) -> STL unit
  (requires (fun h -> reduced h b /\ live h tmp /\ length tmp = 4))
  (ensures (fun h0 _ h1 -> reduced h0 b /\ live h1 tmp /\ length tmp = 4
      /\ v (get h1 tmp 0) < pow2 105
      /\ v (get h1 tmp 1) < pow2 105
      /\ v (get h1 tmp 2) < pow2 105
      /\ v (get h1 tmp 3) < pow2 105
      (* /\ eval h1 tmp 4 = eval h0 b 8 *)
      (* /\ modifies !{getRef tmp} h0 h1 *)
      ))
let shrink input b' = 
  //@@
  (* let h0 = ST.get() in *)
  let b0 = index b' 0ul in 
  let b1 = index b' 1ul in 
  let b2 = index b' 2ul in 
  let b3 = index b' 3ul in
  let b4 = index b' 4ul in 
  let b5 = index b' 5ul in 
  let b6 = index b' 6ul in 
  let b7 = index b' 7ul in
  (* lemma_helper_30 b0 b1;  *)
  upd input 0ul (b0 |+ (b1 |<< 32ul)); 
  (* lemma_helper_30 b2 b3; *)
  upd input 1ul (b2 |+ (b3 |<< 32ul)); 
  (* lemma_helper_30 b4 b5; *)
  upd input 2ul (b4 |+ (b5 |<< 32ul));
  (* lemma_helper_30 b6 b7;  *)
  upd input 3ul (b6 |+ (b7 |<< 32ul))
  (* let h1 = ST.get() in *)
  (* admitP (True /\ eval h1 input 4 = eval h0 b' 8) // Moving the content from template t:i->32 to t':i->64 *)


val mod_2_64: x:s128 -> Tot (y:s128{v y = v x % pow2 64})
let mod_2_64 x = 
  admit(); // In the semantics of the bitwise operator &, to add to axioms
  let mask64 = ((Hacl.UInt128.of_string "1") |<< 64ul) |- (Hacl.UInt128.of_string "1") in 
  let r = Hacl.UInt128.logand x mask64 in  
  r
  
(* val lemma_helper_40: a:wide -> b:wide -> c:wide -> Lemma *)
(*   (requires (v a < pow2 64 /\ v b < pow2 105 /\ v c < pow2 41)) *)
(*   (ensures (v a + v b + v c < pow2 106 /\ v a + v b + v c < pow2 128)) *)
(* let lemma_helper_40 a b c = *)
(*   //@@ *)
(*   pow2_increases_lemma 64 41;  *)
(*   Lemmas.pow2_double_sum 64; *)
(*   Lemmas.pow2_double_sum 104; *)
(*   cut (True /\ v a + v c < pow2 65); *)
(*   pow2_increases_lemma 105 65; *)
(*   pow2_increases_lemma 128 106 *)

(* val lemma_helper_41: a:wide -> b:wide -> Lemma *)
(*   (requires (v a < pow2 105 /\ v b = pow2 110 + pow2 32 - 1)) *)
(*   (ensures (v a + v b < pow2 111 /\ v a + v b < pow2 128)) *)
(* let lemma_helper_41 a b = *)
(*   //@@ *)
(*   pow2_increases_lemma 104 32; *)
(*   pow2_increases_lemma 110 105; *)
(*   pow2_increases_lemma 128 111 *)

(* val lemma_helper_42: a:wide -> b:wide -> Lemma *)
(*   (requires (v a < pow2 64 /\ v b < pow2 64)) *)
(*   (ensures (v a + v b < pow2 65 /\ v a + v b < pow2 128)) *)
(* let lemma_helper_42 a b = *)
(*   Lemmas.pow2_double_sum 64; *)
(*   pow2_increases_lemma 128 65 *)

(* val lemma_helper_43: a:wide -> b:wide -> Lemma *)
(*   (requires (v a < pow2 64 /\ v b < pow2 105)) *)
(*   (ensures  (v a + v b < pow2 106 /\ v a + v b < pow2 128)) *)
(* let lemma_helper_43 a b =  *)
(*   pow2_increases_lemma 105 64; *)
(*   Lemmas.pow2_double_sum 105; *)
(*   pow2_increases_lemma 128 106 *)

(* val lemma_helper_44: a:wide -> b:wide -> c:wide -> Lemma *)
(*   (requires (v a = pow2 64 - 1 /\ v b = pow2 110 + pow2 32 - 1 /\ v c = pow2 64 - pow2 32)) *)
(*   (ensures  (v a > pow2 63 /\ v b > pow2 63 /\ v c > pow2 63)) *)
(* let lemma_helper_44 a b c = *)
(*   pow2_increases_lemma 110 64; *)
(*   pow2_increases_lemma 63 32; *)
(*   pow2_increases_lemma 64 62; *)
(*   Lemmas.pow2_double_sum 62; *)
(*   Lemmas.pow2_double_sum 63 *)

#reset-options

val add_zero_110: tmp:bigint_large -> input:bigint_large(* {getRef tmp <> getRef input} *) -> STL unit
  (requires (fun h -> live h input /\ length input = 4 /\ live h tmp /\ length tmp = 4
      /\ v (get h input 0) < pow2 105 /\ v (get h input 1) < pow2 105
      /\ v (get h input 2) < pow2 105 /\ v (get h input 3) < pow2 105))
  (ensures (fun h0 _ h1 -> live h0 input /\ live h1 tmp /\ length tmp = 4 /\ length input = 4
    /\ v (get h1 tmp 0) < pow2 106 /\ v (get h1 tmp 1) < pow2 111
    /\ v (get h1 tmp 2) < pow2 65  /\ v (get h1 tmp 3) < pow2 106
    /\ v (get h1 tmp 0) >= pow2 64 - 1  /\ v (get h1 tmp 1) > pow2 110
    /\ v (get h1 tmp 3) > pow2 63
    (* /\ eval h1 tmp 4 = eval h0 input 4 *)
    (* /\ modifies !{getRef tmp} h0 h1 *)
    ))
let add_zero_110 tmp input =
  //@@
  (* let h0 = ST.get() in *)
  let zero110 = zero_110 () in
  let z3 = index zero110 3ul in
  let z2 = index zero110 2ul in
  let z1 = index zero110 1ul in
  let z0 = index zero110 0ul in
  let i3 = index input   3ul in
  let i2 = index input   2ul in
  let i1 = index input   1ul in
  let i0 = index input   0ul in
  let r2 = mod_2_64 i2 in
  let c2 = i2 |>> 64ul in
  (* admitP (True /\ v c2 < pow2 41); *)
  (* lemma_helper_40 z3 i3 c2; *)
  let t3 = z3 |+ i3 |+ c2 in
  (* lemma_helper_42 z2 r2;  *)
  let t2 = z2 |+ r2 in
  (* lemma_helper_41 i1 z1; *)
  let t1 = i1 |+ z1 in
  (* lemma_helper_43 z0 i0; *)
  let t0 = z0 |+ i0 in
  (* lemma_helper_44 z0 z1 z3; *)
  upd tmp 3ul t3;
  upd tmp 2ul t2;
  upd tmp 1ul t1;
  upd tmp 0ul t0
  (* Lemmas.pow2_double_sum 63; *)
  (* let h1 = ST.get() in *)
  (* admitP (True /\ eval h1 tmp 4 = eval h0 input 4) // Adding P256 *)

#reset-options

(* val lemma_helper_51: c3:wide -> c3_2_32:wide -> Lemma  *)
(*   (requires (v c3 < pow2 42 /\ c3_2_32 = (c3 |<< 32))) *)
(*   (ensures  (v c3_2_32 < pow2 74 /\ v c3_2_32 = v c3 * pow2 32)) *)
(* let lemma_helper_51 c3 c3_2_32 = *)
(*   coerce *)
(*     (requires (v c3 < pow2 42 /\ c3_2_32 = (c3 |<< 32))) *)
(*     (ensures  (v c3_2_32 < pow2 74 /\ v c3_2_32 = v c3 * pow2 32)) *)
(*     (fun _ -> Lemmas.pow2_exp_1 42 32; *)
(* 	    cut (True /\ v c3 * pow2 32 < pow2 74); *)
(* 	    pow2_increases_lemma 128 74; *)
(* 	    lemma_helper_00 (v c3 * pow2 32) (pow2 128)) *)

(* val lemma_helper_52: r3:wide -> c3_2_32:wide -> c3:wide -> Lemma *)
(*   (requires (v r3 < pow2 64 /\ v c3_2_32 < pow2 74 /\ v c3 < pow2 42 /\ v c3_2_32 = v c3 * pow2 32)) *)
(*   (ensures (v r3 + v c3_2_32 < pow2 128 /\ v r3 + v c3_2_32 >= v c3 /\ v r3 + v c3_2_32 - v c3 < pow2 75)) *)
(* let lemma_helper_52 r3 c3_2_32 c3 = *)
(*   pow2_increases_lemma 64 42; *)
(*   pow2_increases_lemma 74 42; *)
(*   pow2_increases_lemma 74 64; *)
(*   Lemmas.pow2_double_sum 74; *)
(*   pow2_increases_lemma 128 75 *)

(* val lemma_helper_53: t1:wide -> c3_2_32:wide -> Lemma *)
(*   (requires (v t1 < pow2 111 /\ v t1 > pow2 110 /\ v c3_2_32 < pow2 74)) *)
(*   (ensures (v t1 >= v c3_2_32 /\ v t1 - v c3_2_32 < pow2 111 /\ v t1 - v c3_2_32 > pow2 109)) *)
(* let lemma_helper_53 t1 c3_2_32 = *)
(*   pow2_increases_lemma 110 74; *)
(*   pow2_increases_lemma 109 74; *)
(*   Lemmas.pow2_double_sum 109 *)

(* val lemma_helper_54: t0:wide -> c3:wide -> Lemma *)
(*   (requires (v t0 < pow2 106 /\ v c3 < pow2 42)) *)
(*   (ensures (v t0 + v c3 < pow2 128)) *)
(* let lemma_helper_54 t0 c3 =  *)
(*   pow2_increases_lemma 106 42; *)
(*   Lemmas.pow2_double_sum 106; *)
(*   pow2_increases_lemma 128 107 *)

val carry_top_1: t:bigint_large -> STL unit
  (requires (fun h -> live h t /\ length t = 4
    /\ v (get h t 0) < pow2 106 /\ v (get h t 1) < pow2 111
    /\ v (get h t 2) < pow2 65 /\ v (get h t 3) < pow2 106
    /\ v (get h t 0) >= pow2 64 - 1 /\ v (get h t 1) > pow2 110
    /\ v (get h t 3) > pow2 63 ))
  (ensures (fun h0 _ h1 -> live h1 t /\ length t = 4 /\ live h0 t /\ length t = 4
    /\ v (get h1 t 0) < pow2 106 + pow2 42
    /\ v (get h1 t 1) < pow2 111
    /\ v (get h1 t 2) < pow2 65
    /\ v (get h1 t 3) < pow2 75
    /\ v (get h1 t 0) >= pow2 64 - 1
    /\ v (get h1 t 1) > pow2 109
    (* /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime *)
    (* /\ modifies !{getRef t} h0 h1 *)
    ))
let carry_top_1 t =
  //@@
  (* let h0 = ST.get() in *)
  let t3 = index t 3ul in
  let t1 = index t 1ul in
  let t0 = index t 0ul in
  let c3 = t3 |>> 64ul in
  (* admitP (True /\ v c3 < pow2 42); // From the semantics of '>>', must be ported to axioms *)
  let r3 = mod_2_64 t3 in
  let c3_2_32 = c3 |<< 32ul in
  (* lemma_helper_51 c3 c3_2_32;  *)
  (* Lemmas.pow2_double_sum 110;  *)
  (* Lemmas.pow2_double_sum 64;  *)
  (* lemma_helper_52 r3 c3_2_32 c3; *)
  let t3' = (r3 |+ c3_2_32) |- c3 in
  (* lemma_helper_53 t1 c3_2_32; *)
  let t1' = t1 |- c3_2_32 in
  (* lemma_helper_54 t0 c3; *)
  let t0' = t0 |+ c3 in
  upd t 3ul t3'; 
  upd t 1ul t1'; 
  upd t 0ul t0'
  (* let h1 = ST.get() in *)
  (* admitP(True /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime) *)

(* #reset-options *)

(* val lemma_helper_61: c3:wide -> c3_2_32:wide -> Lemma  *)
(*   (requires (v c3 < pow2 11 /\ c3_2_32 = (c3 |<< 32))) *)
(*   (ensures  (v c3_2_32 < pow2 43 /\ v c3_2_32 = v c3 * pow2 32)) *)
(* let lemma_helper_61 c3 c3_2_32 = *)
(*   coerce *)
(*     (requires (v c3 < pow2 11 /\ c3_2_32 = (c3 |<< 32))) *)
(*     (ensures  (v c3_2_32 < pow2 43 /\ v c3_2_32 = v c3 * pow2 32)) *)
(*     (fun _ -> Lemmas.pow2_exp_1 11 32; *)
(* 	    cut (True /\ v c3 * pow2 32 < pow2 43); *)
(* 	    pow2_increases_lemma 128 43; *)
(* 	    lemma_helper_00 (v c3 * pow2 32) (pow2 128)) *)

(* val lemma_helper_62: r3:wide -> c3_2_32:wide -> c3:wide -> Lemma *)
(*   (requires (v r3 < pow2 64 /\ v c3_2_32 < pow2 43 /\ v c3 < pow2 11 /\ v c3_2_32 = v c3 * pow2 32)) *)
(*   (ensures (v r3 + v c3_2_32 < pow2 128 /\ v r3 + v c3_2_32 >= v c3 /\ v r3 + v c3_2_32 - v c3 < pow2 64 + pow2 44)) *)
(* let lemma_helper_62 r3 c3_2_32 c3 = *)
(*   pow2_increases_lemma 64 11; *)
(*   pow2_increases_lemma 43 11; *)
(*   pow2_increases_lemma 64 43; *)
(*   Lemmas.pow2_double_sum 43; *)
(*   Lemmas.pow2_double_sum 64; *)
(*   pow2_increases_lemma 128 65 *)

(* val lemma_helper_63: t1:wide -> c3_2_32:wide -> Lemma *)
(*   (requires (v t1 < pow2 111 /\ v t1 > pow2 109 /\ v c3_2_32 < pow2 43)) *)
(*   (ensures (v t1 >= v c3_2_32 /\ v t1 - v c3_2_32 < pow2 128 /\ v t1 - v c3_2_32 > pow2 108)) *)
(* let lemma_helper_63 t1 c3_2_32 =  *)
(*   pow2_increases_lemma 109 43; *)
(*   pow2_increases_lemma 108 43; *)
(*   pow2_increases_lemma 128 109 *)

(* val lemma_helper_64: t0:wide -> c3:wide -> Lemma *)
(*   (requires (v t0 < pow2 106 + pow2 42 /\ v c3 < pow2 11)) *)
(*   (ensures  (v t0 + v c3 < pow2 128 /\ v t0 + v c3 < pow2 106 + pow2 43)) *)
(* let lemma_helper_64 t0 c3 =  *)
(*   pow2_increases_lemma 42 11; *)
(*   pow2_increases_lemma 127 106; *)
(*   pow2_increases_lemma 127 43; *)
(*   Lemmas.pow2_double_sum 127 *)

val carry_top_2: t:bigint_large -> STL unit
  (requires (fun h -> live h t /\ length t = 4
    /\ v (get h t 0) < pow2 106 + pow2 42 /\ v (get h t 0) >= pow2 64 - 1
    /\ v (get h t 1) < pow2 111 /\ v (get h t 1) > pow2 109
    /\ v (get h t 2) < pow2 65
    /\ v (get h t 3) < pow2 75 ))
  (ensures (fun h0 _ h1 -> live h1 t /\ length t = 4 /\ live h0 t /\ length t = 4
    /\ v (get h1 t 0) < pow2 106 + pow2 43 /\ v (get h1 t 0) >= pow2 64 - 1
    /\ v (get h1 t 1) < pow2 111 /\ v (get h1 t 1) > pow2 108
    /\ v (get h1 t 2) < pow2 65
    /\ v (get h1 t 3) < pow2 64 + pow2 44
    (* /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime *)
    (* /\ modifies !{getRef t} h0 h1 *)
    ))
let carry_top_2 t =
  //@@
  (* let h0 = ST.get() in *)
  let t3 = index t 3ul in
  let t1 = index t 1ul in
  let t0 = index t 0ul in
  let c3 = t3 |>> 64ul in
  (* admitP (True /\ v c3 < pow2 11); // From the semantics of '>>', must be ported to axioms *)
  let r3 = mod_2_64 t3 in
  let c3_2_32 = c3 |<< 32ul in
  (* lemma_helper_61 c3 c3_2_32; *)
  (* lemma_helper_62 r3 c3_2_32 c3; *)
  let t3' = r3 |+ c3_2_32 |- c3 in
  (* lemma_helper_63 t1 c3_2_32; *)
  let t1' = t1 |- c3_2_32 in
  (* lemma_helper_64 t0 c3; *)
  let t0' = t0 |+ c3 in 
  upd t 3ul t3';
  upd t 1ul t1';
  upd t 0ul t0'
  (* let h1 = ST.get() in *)
  (* admitP(True /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime) *)

val cond_subtract_prime: t:bigint_large -> STL unit
  (requires (fun h -> live h t /\ length t = 4
    /\ v (get h t 0) < pow2 106 + pow2 43 /\ v (get h t 0) >= pow2 64 - 1
    /\ v (get h t 1) < pow2 111 /\ v (get h t 1) > pow2 108
    /\ v (get h t 2) < pow2 65
    /\ v (get h t 3) < pow2 64 + pow2 44 ))
  (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ length t = 4 /\ length t = 4
    /\ (v (get h0 t 3) >= pow2 64 - pow2 32 + 1 ==> (
	v (get h1 t 3) < pow2 45 /\ v (get h1 t 2) < pow2 65
	/\ v (get h1 t 1) < pow2 111 /\ v (get h1 t 0) < pow2 106 + pow2 43 ) )
    /\ (v (get h0 t 3) < pow2 64 - pow2 32 + 1 ==> (
	v (get h1 t 2) < pow2 65 /\ v (get h1 t 1) < pow2 111 
	/\ v (get h1 t 0) < pow2 106 + pow2 43))
    (* /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime *)
    (* /\ modifies !{getRef t} h0 h1  *)
    ))
let cond_subtract_prime tmp =
  (* admit(); *)
  let prime = kPrime () in
  let t3 = index tmp 3ul in
  let kPrime3Test = (((Hacl.UInt128.of_string "1") |<< 64ul) |- ((Hacl.UInt128.of_string "1") |<< 32ul)) |+ (Hacl.UInt128.of_string "1") in
  let mask = Hacl.UInt128.gte_mask t3 kPrime3Test in
  (* Conditionnally subtract the prime *)
  let t0 = index tmp 0ul in
  let t1 = index tmp 1ul in
  let t3 = index tmp 3ul in
  let p0 = index prime 0ul in
  let p1 = index prime 1ul in
  let p3 = index prime 3ul in
  upd tmp 0ul (t0 |- (mask |& p0));
  upd tmp 1ul (t1 |- (mask |& p1));
  upd tmp 3ul (t3 |- (mask |& p3))

val carry_pass: t:bigint_large -> STL unit
  (requires (fun h -> live h t /\ length t = 4
    /\ ((v (get h t 3) < pow2 45 /\ v (get h t 2) < pow2 65
      /\ v (get h t 1) < pow2 111 /\ v (get h t 0) < pow2 106 + pow2 43 )
      \/ (v (get h t 2) < pow2 65 /\ v (get h t 1) < pow2 111 
	/\ v (get h t 0) < pow2 106 + pow2 43)) ))
  (ensures (fun h0 _ h1 -> live h0 t /\ length t = 4 /\ live h1 t /\ length t = 4
    (* /\ eval h1 t 4 = eval h0 t 4 *)
    (* /\ modifies !{getRef t} h0 h1 *)
    /\ v (get h1 t 0) < pow2 64
    /\ v (get h1 t 1) < pow2 64
    /\ v (get h1 t 2) < pow2 64
    /\ v (get h1 t 3) < pow2 64 ))
let carry_pass tmp =
  (* admit(); *)
  let mask64 = ((Hacl.UInt128.of_string "1") |<< 64ul) |- (Hacl.UInt128.of_string "1") in
  let t0 = index tmp 0ul in
  let t1 = index tmp 1ul in
  upd tmp 1ul (t1 |+ (t0 |>> 64ul));
  upd tmp 0ul (t0 |& mask64);
  let t1 = index tmp 1ul in
  let t2 = index tmp 2ul in
  let t3 = index tmp 3ul in
  upd tmp 2ul (t2 |+ (t1 |>> 64ul));
  let t2 = index tmp 2ul in
  upd tmp 1ul (t1 |& mask64);
  upd tmp 3ul (t3 |+ (t2 |>> 64ul));
  upd tmp 2ul (t2 |& mask64)

val expand: b:bigint_wide -> t:bigint_large(* {getRef t <> getRef b} *) -> STL unit
  (requires (fun h -> live h t /\ live h b /\ length b >= 8 /\ length t >= 4
    /\ v (get h t 0) < pow2 64 
    /\ v (get h t 1) < pow2 64 
    /\ v (get h t 2) < pow2 64 
    /\ v (get h t 3) < pow2 64 ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h0 b /\ live h0 t /\ length t >= 4 /\ length b >= 8
    /\ length b = length b
    (* /\ Standardized h1 b *)
    (* /\ eval h1 b 8 = eval h0 t 4 *)
    (* /\ modifies !{getRef b} h0 h1  *)
    ))    
let expand b' tmp =
  (* admit(); *)
  let t0 = index tmp 0ul in
  let t1 = index tmp 1ul in
  let t2 = index tmp 2ul in
  let t3 = index tmp 3ul in
  let mask32 = Hacl.UInt128.of_string "0xffffffff" in
  upd b' 0ul (t0 |& mask32);
  upd b' 1ul (t0 |>> 32ul);
  upd b' 2ul (t1 |& mask32);
  upd b' 3ul (t1 |>> 32ul);
  upd b' 4ul (t2 |& mask32);
  upd b' 5ul (t2 |>> 32ul);
  upd b' 6ul (t3 |& mask32);
  upd b' 7ul (t3 |>> 32ul)

(* val lemma_helper_80: h0:heap -> h1:heap -> h2:heap -> h3:heap -> b:bigint_wide -> i:bigint_large -> t:bigint_large -> Lemma  *)
(*   (requires (live h0 b /\ not(contains h0 (getRef i)) /\ not(contains h0 (getRef t)) /\ modifies !{} h0 h1 /\ modifies !{getRef t} h1 h2 *)
(*     /\ modifies !{getRef b} h2 h3)) *)
(*   (ensures  (modifies !{getRef b} h0 h3)) *)
(* let lemma_helper_80 h0 h1 h2 h3 b i t = () *)

// Input comes from freduce_degree so all limbs are < 2 ^ 72
val freduce_coefficients: b:bigint_wide -> STL unit 
  (requires (fun h -> reduced h b))
  (ensures (fun h0 _ h1 -> updated h0 h1 b 8 /\ reduced h0 b(*  /\ standardized h1 b *)
    (* /\ eval h1 b 8 % reveal prime = eval h0 b 8 % reveal prime *)
    (* /\ modifies !{getRef b} h0 h1 *)))
let freduce_coefficients b' =
  //@@
  (* let h0 = ST.get() in *)
  let input = create (Hacl.UInt128.of_string "0") 4ul in
  (* let h0' = ST.get() in *)
  (* eval_eq_lemma h0 h0' b' b' 8; *)
  shrink input b';
  (* let h1 = ST.get() in *)
  (* cut (modifies !{} h0 h1);  *)
  (* cut (True /\ eval h1 input 4 = eval h0 b' 8); *)
  (* At this point, eval b 8 with templ = eval input 4 with (x -> 64) *)
  // Code taken from openSSL NistP256 "felem_shrink"
  let tmp = create (Hacl.UInt128.of_string "0") 4ul in
  (* let h1' = ST.get() in *)
  (* eval_eq_lemma h1 h1' input input 4;  *)
  add_zero_110 tmp input; 
  carry_top_1 tmp; 
  carry_top_2 tmp; 
  (* Conditionnally subtract the prime value *)
  cond_subtract_prime tmp;
  (* let h2 = ST.get () in *)
  (* cut (modifies !{} h0 h2); *)
  (* cut (True /\ eval h2 tmp 4 % reveal prime = eval h0 b' 8 % reveal prime);  *)
  (* Carry pass *)
  carry_pass tmp;
  (* Expand tmp into b' *)
  (* let h3 = ST.get() in *)
  (* cut (modifies !{getRef tmp} h2 h3); *)
  expand b' tmp
  (* let h1 = ST.get() in  *)
  (* cut (eval h1 b' 8 % reveal prime = eval h0 b' 8 % reveal prime /\ True);  *)
  (* lemma_helper_80 h0 h2 h3 h1 b' input tmp *)

(* #reset-options *)

val freduce_degree: b:bigint_wide -> STL unit 
  (requires (fun h -> reducible h b))
 (ensures (fun h0 _ h1 -> updated h0 h1 b 15 /\ reducible h0 b(*  /\ standardized h1 b *)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime *)
    (* /\ modifies !{getRef b} h0 h1 *)))
let freduce_degree b =
  freduce_degree' b;
  freduce_coefficients b

(* #reset-options *)

(* Unit, just to fill in the interface *)
val carry_top_to_0: bigint_wide -> STL unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> h0==h1))
let carry_top_to_0 b = ()

val add_big_zero: bigint -> Stl unit
let add_big_zero b =
  (* admit(); // Adds P256<<1 shaped such that all limbs are >= 2^32 and < 2^33, to provide "Filled h1 b 32 33" *)
  let two33m1 = Hacl.UInt64.of_string "0x1fffffffe" in
  let two33m2 = Hacl.UInt64.of_string "0x1fffffffc" in
  let two33   = Hacl.UInt64.of_string "0x200000000" in
  let b0 = index b 0ul in
  upd b 0ul (Hacl.UInt64.add b0 two33m1);
  let b1 = index b 1ul in
  upd b 1ul (Hacl.UInt64.add b1 two33m1); 
  let b2 = index b 2ul in
  upd b 2ul (Hacl.UInt64.add b2 two33m1); 
  let b3 = index b 3ul in
  upd b 3ul (Hacl.UInt64.add b3 two33); 
  let b4 = index b 4ul in
  upd b 4ul (Hacl.UInt64.add b4 two33m1);
  let b5 = index b 5ul in
  upd b 5ul (Hacl.UInt64.add b5 two33m1);
  let b6 = index b 6ul in
  upd b 6ul (Hacl.UInt64.add b6 two33); 
  let b7 = index b 7ul in
  upd b 7ul (Hacl.UInt64.add b7 two33m2)

val subtract_u64: r:HyperStack.stackref s64 -> c:HyperStack.stackref s64 -> x:s64 -> STL unit 
  (requires (fun h -> True(* contains h r /\ contains h c *))) 
  (ensures (fun h0 _ h1 -> True))
let subtract_u64 result carry v =
  let z = !result in
  let r = Hacl.Cast.sint64_to_sint128 z in
  pow2_increases_lemma platform_wide platform_size;
  let r = Hacl.UInt128.sub_mod r (Hacl.Cast.sint64_to_sint128 v) in
  carry := Hacl.Cast.sint128_to_sint64 ((r |>> 64ul) |& (Hacl.UInt128.of_string "1"));
  result := Hacl.Cast.sint128_to_sint64 r

val felem_contract_loop: output:bigint -> prime:bigint_wide -> mask:HyperStack.stackref s64 -> res:HyperStack.stackref s64 -> 
  ctr:u32 -> STL unit
  (requires (fun h -> True)) 
  (ensures (fun h0 _ h1 -> True))
let rec felem_contract_loop output prime all_equal_so_far result ctr =
  (* admit(); // TOOD *)
  if UInt32.eq ctr 0ul then ()
  else begin
    let i = ctr -| 1ul in
    let pi = index prime i in
    let oi = index output i in
    let a = pi |- Hacl.Cast.sint64_to_sint128 (oi) in
    result := Hacl.UInt64.logor (!all_equal_so_far) (Hacl.Cast.sint128_to_sint64 (a |>> 64ul));
    let equal = Hacl.UInt64.logxor (Hacl.Cast.sint128_to_sint64 pi) (oi) in
    let equal = Hacl.UInt64.sub equal (Hacl.Cast.uint64_to_sint64 1uL) in
    let equal = Hacl.UInt64.logand equal (Hacl.UInt64.shift_left equal 32ul) in
    let equal = Hacl.UInt64.logand equal (Hacl.UInt64.shift_left equal 16ul) in
    let equal = Hacl.UInt64.logand equal (Hacl.UInt64.shift_left equal 8ul) in
    let equal = Hacl.UInt64.logand equal (Hacl.UInt64.shift_left equal 4ul) in
    let equal = Hacl.UInt64.logand equal (Hacl.UInt64.shift_left equal 2ul) in
    let equal = Hacl.UInt64.logand equal (Hacl.UInt64.shift_left equal 1ul) in
    let equal = Hacl.UInt64.eq_mask (Hacl.UInt64.logand (Hacl.UInt64.shift_right equal 63ul) (Hacl.Cast.uint64_to_sint64 1uL)) (Hacl.Cast.uint64_to_sint64 1uL) in
    all_equal_so_far := Hacl.UInt64.logand (!all_equal_so_far) equal;
    felem_contract_loop output prime all_equal_so_far result (ctr-|1ul)
  end
val normalize: b:bigint -> STL unit 
  (requires (fun h -> (* standardized h b /\  *)length b >= 8))
  (ensures (fun h0 _ h1 -> (* Standardized h0 b /\ *) length b >= 8 /\ live h1 b /\ 
    length b = length b
    /\ eval h1 b 8 = eval h0 b 8 % reveal prime))
let normalize output =  
  admit(); // Not machine checked
  let input = create (Hacl.Cast.uint64_to_sint64 0uL) 4ul in
  let b0 = index output 0ul in 
  let b1 = index output 1ul in 
  let b2 = index output 2ul in 
  let b3 = index output 3ul in
  let b4 = index output 4ul in 
  let b5 = index output 5ul in 
  let b6 = index output 6ul in 
  let b7 = index output 7ul in
  upd input 0ul (Hacl.UInt64.add b0 (Hacl.UInt64.shift_left b1 32ul));
  upd input 1ul (Hacl.UInt64.add b2 (Hacl.UInt64.shift_left b3 32ul));
  upd input 2ul (Hacl.UInt64.add b4 (Hacl.UInt64.shift_left b5 32ul));
  upd input 3ul (Hacl.UInt64.add b6 (Hacl.UInt64.shift_left b7 32ul));
  let all_equal_so_far = salloc (Hacl.UInt64.of_string "0xffffffffffffffff") in
  let result = salloc (Hacl.Cast.uint64_to_sint64 0uL) in
//  all_equal_so_far := sub_limb (!all_equal_so_far) (Hacl.Cast.uint64_to_sint64 1uL);
  let prime = kPrime () in
  felem_contract_loop input prime all_equal_so_far result 4ul;  
  result := Hacl.UInt64.logor (!result) (!all_equal_so_far);
  let final_result = !result in
  let carry = salloc (Hacl.Cast.uint64_to_sint64 0uL) in
  result := index input 0ul;
  let p0 = index prime 0ul in
  subtract_u64 result carry (Hacl.UInt64.logand final_result (Hacl.Cast.sint128_to_sint64 p0));
  upd input 0ul !result;
  result := index input 1ul;
  subtract_u64 result carry (!carry);
  upd input 1ul !result;
  result := index input 2ul;
  subtract_u64 result carry (!carry);
  upd input 2ul !result;
  result := index input 3ul;
  subtract_u64 result carry (!carry);
  upd input 3ul !result;
  let p1 = index prime 1ul in
  result := index input 1ul;
  subtract_u64 result carry (Hacl.UInt64.logand final_result (Hacl.Cast.sint128_to_sint64 p1));
  upd input 1ul !result;
  result := index input 2ul;
  subtract_u64 result carry (!carry);
  upd input 2ul !result;
  result := index input 3ul;
  subtract_u64 result carry (!carry);
  upd input 3ul !result;
  let p2 = index prime 2ul in
  result := index input 2ul;
  subtract_u64 result carry (Hacl.UInt64.logand final_result (Hacl.Cast.sint128_to_sint64 p2));
  upd input 2ul !result;
  result := index input 3ul;
  subtract_u64 result carry (!carry);
  upd input 3ul !result;
  let p3 = index prime 3ul in
  result := index input 3ul;
  subtract_u64 result carry (Hacl.UInt64.logand final_result (Hacl.Cast.sint128_to_sint64 p3));
  upd input 3ul !result;
  let mask32 = Hacl.UInt64.of_string "0xffffffff" in
  let i0 = index input 0ul in
  let i1 = index input 1ul in
  let i2 = index input 2ul in
  let i3 = index input 3ul in
  upd output 0ul (Hacl.UInt64.logand (i0) mask32);
  upd output 1ul (Hacl.UInt64.shift_right (i0) 32ul);
  upd output 2ul (Hacl.UInt64.logand (i1) mask32);
  upd output 3ul (Hacl.UInt64.shift_right (i1) 32ul);
  upd output 4ul (Hacl.UInt64.logand (i2) mask32);
  upd output 5ul (Hacl.UInt64.shift_right (i2) 32ul);
  upd output 6ul (Hacl.UInt64.logand (i3) mask32);
  upd output 7ul (Hacl.UInt64.shift_right (i3) 32ul)
