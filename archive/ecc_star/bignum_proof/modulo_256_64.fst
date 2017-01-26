(*--build-config
    options:--admit_fsi FStar.Set --verify_module Modulo --z3rlimit 20;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters_256_64.fst $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst modulo.fsti;
  --*)

module Modulo

(* 64/128 bits *)

open FStar.Heap
open FStar.Ghost
open IntLib
open Lemmas
open Parameters
open UInt
open Bigint
open Eval

let op_Bar_Amp x y = log_and_wide x y
let op_Bar_Greater_Greater x y = shift_right_wide x y
let op_Bar_Less_Less x y = shift_left_wide x y
let op_Bar_Plus x y = add_wide x y
let op_Bar_Star x y = mul_wide x y
let op_Bar_Subtraction x y = sub_wide x y

let satisfies_modulo_constraints h b = 
  getLength h b >= 2*norm_length-1 && getTemplate b = templ
  && maxValue h b < pow2 67

val lemma_satisfies: h:heap -> b:bigint_wide -> n:nat -> Lemma
  (requires (live h b /\ (forall (i:nat). i < getLength h b ==> v (getValue h b i) < pow2 n)))
  (ensures  (live h b /\ maxValue h b < pow2 n))
let lemma_satisfies h b n = ()  

let sum_satisfies_constraints h0 h1 cpy a b =
  //@@
  pow2_double_sum 32;
  cut (forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < norm_length 
	    ==> v (getValue h1 cpy i) < pow2 33);
  cut (forall (i:nat). {:pattern (v (getValue h1 cpy i))} (i >= norm_length /\ i < getLength h1 cpy)
	    ==> v (getValue h1 cpy i) = 0);
  cut(forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < getLength h1 cpy
	   ==> v (getValue h1 cpy i) < pow2 33);
  lemma_satisfies h1 cpy 33;
  pow2_increases_lemma 67 33

let n0 = ndiff'
let n1 = ndiff

let difference_satisfies_constraints h0 h1 cpy a b =
  //@@
  cut(forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < getLength h1 cpy
	   ==> v (getValue h1 cpy i) < pow2 34);
  lemma_satisfies h1 cpy 34;
  pow2_increases_lemma 67 34

val lemma_satisfies_2: h:heap -> b:bigint -> Lemma 
  (requires (Standardized h b))
  (ensures  (Standardized h b /\ maxValueNorm h b < pow2 32))
let lemma_satisfies_2 h b = ()

val lemma_satisfies_4: a:nat -> b:nat -> c:pos -> d:pos -> Lemma (requires (a < c /\ b < d))
							    (ensures (a * b < c * d))
let lemma_satisfies_4 a b c d = ()

val lemma_satisfies_3: b:nat -> c:nat -> Lemma
  (requires (b < pow2 32 /\ c < pow2 32))
  (ensures (norm_length * b * c < pow2 67))
let lemma_satisfies_3 b c = 
  //@@
  cut (True /\ 8 = pow2 3);
  pow2_exp_lemma 32 32;
  pow2_exp_lemma 3 64;
  Axiomatic.paren_mul_right norm_length b c;
  lemma_satisfies_4 b c (pow2 32) (pow2 32)

let mul_satisfies_constraints h0 h1 res a b =
  lemma_satisfies_2 h0 a;
  lemma_satisfies_2 h0 b;
  lemma_satisfies_3 (maxValueNorm h0 a) (maxValueNorm h0 b)

type Updated h0 h1 (b:bigint_wide) (len:nat) = 
  live h0 b /\ live h1 b /\ getLength h0 b >= len /\ getLength h1 b = getLength h0 b

val templ_large: nat -> Tot pos
let templ_large i = 64

type bigint_large = b:biginteger platform_wide{Bigint.t b = templ_large}

val lemma_helper_00: n:nat -> m:pos -> Lemma (requires (n < m)) (ensures (n % m = n))
let lemma_helper_00 n m = Axiomatic.modulo_lemma_0 n m

val lemma_helper_01: n:nat -> m:pos -> Lemma (requires (n < m)) (ensures (pow2 n % pow2 m = pow2 n))
let lemma_helper_01 n m = pow2_increases_lemma m n; lemma_helper_00 (pow2 n) (pow2 m)

val lemma_helper_02: unit -> Lemma (pow2 64 - 1 < pow2 128 /\ pow2 32 - 1 < pow2 128 /\ pow2 64 - pow2 32 + 1 < pow2 128)
let lemma_helper_02 () = pow2_increases_lemma 128 64; pow2_increases_lemma 64 32

val lemma_helper_04: a:int -> b:int -> c:int -> d:int -> Lemma (a * (b - c + d) = a * b - a * c + a * d)
let lemma_helper_04 a b c d = 
  //@@
  ()

val lemma_helper_03: h:heap -> b:bigint_large -> Lemma
  (requires (live h b /\ getLength h b >= 4 
    /\ v (getValue h b 0) = pow2 64 - 1
    /\ v (getValue h b 1) = pow2 32 - 1
    /\ v (getValue h b 2) = 0
    /\ v (getValue h b 3) = pow2 64 - pow2 32 + 1))
  (ensures (live h b /\ getLength h b >= 4 /\ eval h b 4 = reveal prime))
let lemma_helper_03 h b = 
  //@@
  eval_definition h b 4;
  eval_definition h b 3;
  eval_definition h b 2;
  eval_definition h b 1; 
  bitweight_definition templ_large 2;
  bitweight_definition templ_large 1;
  bitweight_definition templ_large 0;
  Axiomatic.distributivity_sub_right (pow2 64) (pow2 32) 1;
  lemma_helper_04 (pow2 192) (pow2 64) (pow2 32) 1;
  Lemmas.pow2_exp_1 192 64;
  Lemmas.pow2_exp_1 192 32;
  Lemmas.pow2_exp_1 64 32

val kPrime: unit -> ST (bigint_large)
  (requires (fun h -> True)) 
  (ensures (fun h0 b h1 -> not(contains h0 (getRef b))
    /\ live h1 b /\ getLength h1 b = 4
    /\ eval h1 b 4  = reveal prime
    /\ v (getValue h1 b 0) = pow2 64 - 1
    /\ v (getValue h1 b 1) = pow2 32 - 1
    /\ v (getValue h1 b 2) = 0
    /\ v (getValue h1 b 3) = pow2 64 - pow2 32 + 1
    /\ modifies !{} h0 h1))
let kPrime () =
  //@@
  let a = create_wide_templ 4 templ_large in
  let v_2_64 = one_wide |<< 64 in
  let v_2_32 = one_wide |<< 32 in 
  lemma_helper_01 32 128;
  lemma_helper_01 64 128; 
  pow2_increases_lemma 128 64;
  pow2_increases_lemma 64 32;
  pow2_increases_lemma 128 32;  
  let a0 = v_2_64 |- one_wide in 
  let a1 = v_2_32 |- one_wide in 
  let a3 = v_2_64 |- v_2_32 |+ one_wide in 
  lemma_helper_02 ();
  upd_wide a 0 a0; 
  upd_wide a 1 a1;
  upd_wide a 3 a3;
  let h = ST.get() in 
  lemma_helper_03 h a;
  a

val lemma_helper_10: unit -> Lemma
  (pow2 64 % pow2 128 = pow2 64 /\ pow2 64 - 1 < pow2 128 /\ pow2 110 + pow2 32 < pow2 128
   /\ pow2 110 % pow2 128 = pow2 110 /\ pow2 32 % pow2 128 = pow2 32 /\ pow2 110 + pow2 32 - 1 < pow2 128
   /\ pow2 46 % pow2 128 = pow2 46 /\ pow2 64 - pow2 46 < pow2 128 /\ pow2 64 > pow2 46
   /\ pow2 64 - pow2 32 < pow2 128 /\ pow2 64 > pow2 32)
let lemma_helper_10 () = 
  //@@
  lemma_helper_01 32 128;
  lemma_helper_01 46 128;
  lemma_helper_01 64 128;
  lemma_helper_01 110 128;
  pow2_increases_lemma 128 110;
  pow2_increases_lemma 128 111;
  pow2_increases_lemma 110 32;
  Lemmas.pow2_double_sum 110;
  pow2_increases_lemma 128 64;
  pow2_increases_lemma 64 46;
  pow2_increases_lemma 46 32

val zero_110: unit -> ST bigint_large
  (requires (fun h -> True)) 
  (ensures (fun h0 b h1 -> not(contains h0 (getRef b))
    /\ live h1 b /\ getLength h1 b = 4
    /\ eval h1 b 4 = reveal prime
    /\ v (getValue h1 b 0) = pow2 64 - 1
    /\ v (getValue h1 b 1) = pow2 110 + pow2 32 - 1
    /\ v (getValue h1 b 2) = pow2 64 - pow2 46
    /\ v (getValue h1 b 3) = pow2 64 - pow2 32
    /\ modifies !{} h0 h1))
let zero_110 () =
  //@@
  lemma_helper_10 ();
  let v2_32 = one_wide |<< 32 in
  let v2_46 = one_wide |<< 46 in
  let v2_64 = one_wide |<< 64 in
  let v2_110 = one_wide |<< 110 in
  let two64m0 = v2_64 |- one_wide in 
  let two110p32m0 = (v2_110 |+ v2_32) |- one_wide in 
  let two64m46 = v2_64 |- v2_46 in 
  let two64m32 = v2_64 |- v2_32 in
  let a = create_wide_templ 4 templ_large in
  upd_wide a 0 two64m0;
  upd_wide a 1 two110p32m0;
  upd_wide a 2 two64m46;
  upd_wide a 3 two64m32; 
  let h = ST.get() in
  admitP(eval h a 4 = reveal prime /\ True); // Same as kPrime
  a

#reset-options

type Reducible (h:heap) (b:bigint_wide) =
  live h b /\ getLength h b >= 15 
  /\ v (getValue h b 0) < pow2 67 /\ v (getValue h b 1) < pow2 67 /\ v (getValue h b 2) < pow2 67
  /\ v (getValue h b 3) < pow2 67 /\ v (getValue h b 4) < pow2 67 /\ v (getValue h b 5) < pow2 67
  /\ v (getValue h b 6) < pow2 67 /\ v (getValue h b 7) < pow2 67 /\ v (getValue h b 8) < pow2 67
  /\ v (getValue h b 9) < pow2 67 /\ v (getValue h b 10) < pow2 67 /\ v (getValue h b 11) < pow2 67
  /\ v (getValue h b 12) < pow2 67 /\ v (getValue h b 13) < pow2 67 /\ v (getValue h b 14) < pow2 67

type Reduced (h:heap) (b:bigint_wide) =
  live h b /\ getLength h b >= 8
  /\ v (getValue h b 0) < pow2 72 /\ v (getValue h b 1) < pow2 72 /\ v (getValue h b 2) < pow2 72
  /\ v (getValue h b 3) < pow2 72 /\ v (getValue h b 4) < pow2 72 /\ v (getValue h b 5) < pow2 72
  /\ v (getValue h b 6) < pow2 72 /\ v (getValue h b 7) < pow2 72

type Added70 (h:heap) (b:bigint_wide) =
  live h b /\ getLength h b >= 15
  /\ v (getValue h b 0) < pow2 71 + pow2 67 /\ v (getValue h b 1) < pow2 71 + pow2 67 /\ v (getValue h b 2) < pow2 71 + pow2 67
  /\ v (getValue h b 3) < pow2 71 + pow2 67 /\ v (getValue h b 4) < pow2 71 + pow2 67 /\ v (getValue h b 5) < pow2 71 + pow2 67
  /\ v (getValue h b 6) < pow2 71 + pow2 67 /\ v (getValue h b 7) < pow2 71 + pow2 67
  /\ v (getValue h b 0) > pow2 70 /\ v (getValue h b 1) > pow2 70 /\ v (getValue h b 2) > pow2 70
  /\ v (getValue h b 3) > pow2 70 /\ v (getValue h b 4) > pow2 70 /\ v (getValue h b 5) > pow2 70
  /\ v (getValue h b 6) > pow2 70 /\ v (getValue h b 7) > pow2 70
  /\ v (getValue h b 8) < pow2 67
  /\ v (getValue h b 9) < pow2 67 /\ v (getValue h b 10) < pow2 67 /\ v (getValue h b 11) < pow2 67
  /\ v (getValue h b 12) < pow2 67 /\ v (getValue h b 13) < pow2 67 /\ v (getValue h b 14) < pow2 67

#reset-options

val lemma_helper_20: unit -> Lemma 
  (pow2 71 % pow2 128 = pow2 71 /\ pow2 39 % pow2 128 = pow2 39 /\ pow2 71 - pow2 39 < pow2 128
   /\ pow2 40 % pow2 128 = pow2 40 /\ pow2 71 - pow2 40 < pow2 128 /\ pow2 71 < pow2 128
   /\ pow2 39 < pow2 71 /\ pow2 40 < pow2 71
   /\ pow2 71 - pow2 39 > pow2 70 /\ pow2 71 - pow2 40 > pow2 70 /\ pow2 71 > pow2 70)
let lemma_helper_20 () =
  //@@
  lemma_helper_01 39 128;
  lemma_helper_01 40 128;
  lemma_helper_01 71 128;
  pow2_increases_lemma 128 39;
  pow2_increases_lemma 128 40;
  pow2_increases_lemma 71 40;
  pow2_increases_lemma 71 39;
  pow2_increases_lemma 70 40;
  pow2_increases_lemma 70 39

#reset-options

val lemma_helper_21: unit -> Lemma 
  (pow2 67 + pow2 71 - pow2 39 < pow2 128 /\ pow2 67 + pow2 71 - pow2 40 < pow2 128 /\ pow2 67 + pow2 71 < pow2 128)
let lemma_helper_21 () = 
  //@@
  lemma_helper_01 39 128;
  lemma_helper_01 40 128;
  lemma_helper_01 71 128;
  pow2_increases_lemma 67 39;
  pow2_increases_lemma 67 40;
  pow2_increases_lemma 71 68;
  Lemmas.pow2_double_sum 71;
  pow2_increases_lemma 128 72;
  pow2_increases_lemma 128 40;
  pow2_increases_lemma 71 40;
  pow2_increases_lemma 71 39;
  pow2_increases_lemma 70 40;
  pow2_increases_lemma 70 39

#reset-options

val add_zero_71: b:bigint_wide -> ST unit
  (requires (fun h -> Reducible h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b 15 /\ Reducible h0 b /\ Added70 h1 b
    /\ eval h1 b 15 % reveal prime = eval h0 b 15 % reveal prime
    /\ modifies !{getRef b} h0 h1))
let add_zero_71 b =
  //@@
  let h0 = ST.get() in
  lemma_helper_20 ();
  let zero71m39 = (one_wide |<< 71) |- (one_wide |<< 39) in
  let zero71m40 = (one_wide |<< 71) |- (one_wide |<< 40) in
  let zero71 = (one_wide |<< 71) in 
  let b0 = index_wide b 0 in
  let b1 = index_wide b 1 in
  let b2 = index_wide b 2 in
  let b3 = index_wide b 3 in
  let b4 = index_wide b 4 in
  let b5 = index_wide b 5 in
  let b6 = index_wide b 6 in
  let b7 = index_wide b 7 in
  lemma_helper_21 ();
  upd_wide b 0 (b0 |+ zero71m39); 
  upd_wide b 1 (b1 |+ zero71m39);
  upd_wide b 2 (b2 |+ zero71m39);
  upd_wide b 3 (b3 |+ zero71);
  upd_wide b 4 (b4 |+ zero71m39);
  upd_wide b 5 (b5 |+ zero71m39);
  upd_wide b 6 (b6 |+ zero71);
  upd_wide b 7 (b7 |+ zero71m40); 
  let h1 = ST.get() in
  admitP (eval h1 b 15 % reveal prime = eval h0 b 15 % reveal prime /\ True) // Adding p256 << 39 

#reset-options

val add_top_to_bottom: b:bigint_wide -> ST unit
  (requires (fun h -> Added70 h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b 15 /\ Added70 h0 b /\ Reduced h1 b
    /\ eval h1 b 8 % reveal prime = eval h0 b 15 % reveal prime
    /\ modifies !{getRef b} h0 h1))
let add_top_to_bottom b =
  admit(); //
  let b0 = index_wide b 0 in
  let b1 = index_wide b 1 in
  let b2 = index_wide b 2 in
  let b3 = index_wide b 3 in
  let b4 = index_wide b 4 in
  let b5 = index_wide b 5 in
  let b6 = index_wide b 6 in
  let b7 = index_wide b 7 in  
  let b8 =  index_wide b 8  in 
  let b9 =  index_wide b 9  in 
  let b10 = index_wide b 10 in 
  let b11 = index_wide b 11 in
  let b12 = index_wide b 12 in 
  let b13 = index_wide b 13 in 
  let b14 = index_wide b 14 in
  // What has to be added to the lower limbs. Forall X, |toX| < 7 * max inputX < 2^3 * max inputX 
  // Hence forall X, |toX| < 2^3 * 2 ^ 67 = 2 ^ 70 so it should be safe to add that to b + zero71
  let v0 = ((((((b0 |+ b8) |+ b9) |- b11) |- b12) |- b13) |- b14) in
  let v1 = ((((b1 |+ b9) |+ b10) |- b12) |- b13) |- b14 in
  let v2 = (((b2 |+ b10) |+ b11) |- b13) |- b14 in
  let v3 = ((((b3 |+ (b11 |<< 1)) |- b9) |- b8) |+ (b12 |<< 1)) |+ b13 in
  let v4 = ((((b4 |+ (b12 |<< 1)) |- b9) |- b10) |+ (b13 |<< 1)) |+ b14 in
  let v5 = (((b5 |+ (b13 |<< 1)) |- b10) |- b11) |+ (b14 |<< 1) in
  let v6 = ((((b6 |+ b13) |- b8) |- b9) |+ (b14 |<< 1)) |+ b14 in
  let v7 = ((((b7 |+ b8) |- b10) |- b11) |- b12) |- b13 in
  upd_wide b 0 v0;
  upd_wide b 1 v1;
  upd_wide b 2 v2;
  upd_wide b 3 v3;
  upd_wide b 4 v4;
  upd_wide b 5 v5;
  upd_wide b 6 v6;
  upd_wide b 7 v7

// The input is the result of the multiplication, it is such that 
// forall X, inputX < 8 * 2^32 * 2^32 = 2^67
val freduce_degree': b:bigint_wide -> ST unit 
  (requires (fun h -> Reducible h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b 15 /\ Reducible h0 b /\ Reduced h1 b
    /\ eval h1 b 8 % reveal prime = eval h0 b 15 % reveal prime
    /\ modifies !{getRef b} h0 h1))
let freduce_degree' b =
  add_zero_71 b;
  add_top_to_bottom b

#reset-options

val lemma_helper_31: a:int -> b:int -> c:int -> Lemma (requires (a <= b /\ b < c))
					        (ensures (a < c))
let lemma_helper_31 a b c = ()

val lemma_helper_32: a:nat -> b:nat -> Lemma (requires (a < pow2 104 /\ b <= pow2 104))
				          (ensures (a + b < pow2 105))
let lemma_helper_32 a b = ()					  

val lemma_helper_30: b0:wide -> b1:wide -> Lemma
  (requires (v b0 < pow2 72 /\ v b1 < pow2 72))
  (ensures ((v b1 * pow2 32) % pow2 128 = v b1 * pow2 32
	    /\ v b0 + (v b1 * pow2 32) < pow2 105
	    /\ v b0 + (v b1 * pow2 32) < pow2 128))
let lemma_helper_30 b0 b1 =
  //@@
  coerce 
    (requires (v b0 < pow2 72 /\ v b1 < pow2 72))
    (ensures ((v b1 * pow2 32) % pow2 128 = v b1 * pow2 32
	    /\ v b0 + (v b1 * pow2 32) < pow2 105
	    /\ v b0 + (v b1 * pow2 32) < pow2 128))
  (fun _ -> Lemmas.pow2_exp_1 72 32;
	  pow2_increases_lemma 128 104;
	  pow2_increases_lemma 104 72;
	  Lemmas.pow2_double_sum 104;
	  cut (True /\ v b1 * pow2 32 <= pow2 104); 
	  lemma_helper_31 (v b1 * pow2 32) (pow2 104) (pow2 128);
	  lemma_helper_32 (v b0) (v b1 * pow2 32);
	  pow2_increases_lemma 128 105;
	  lemma_helper_00 (v b1 * pow2 32) (pow2 128) )

#reset-options

val shrink: tmp:bigint_large -> b:bigint_wide{getRef b <> getRef tmp} -> ST unit
  (requires (fun h -> Reduced h b /\ live h tmp /\ getLength h tmp = 4))
  (ensures (fun h0 _ h1 -> Reduced h0 b /\ live h1 tmp /\ getLength h1 tmp = 4
      /\ v (getValue h1 tmp 0) < pow2 105
      /\ v (getValue h1 tmp 1) < pow2 105
      /\ v (getValue h1 tmp 2) < pow2 105
      /\ v (getValue h1 tmp 3) < pow2 105
      /\ eval h1 tmp 4 = eval h0 b 8
      /\ modifies !{getRef tmp} h0 h1))
let shrink input b' = 
  //@@
  let h0 = ST.get() in
  let b0 = index_wide b' 0 in 
  let b1 = index_wide b' 1 in 
  let b2 = index_wide b' 2 in 
  let b3 = index_wide b' 3 in
  let b4 = index_wide b' 4 in 
  let b5 = index_wide b' 5 in 
  let b6 = index_wide b' 6 in 
  let b7 = index_wide b' 7 in
  lemma_helper_30 b0 b1; 
  upd_wide input 0 (b0 |+ (b1 |<< 32)); 
  lemma_helper_30 b2 b3;
  upd_wide input 1 (b2 |+ (b3 |<< 32)); 
  lemma_helper_30 b4 b5;
  upd_wide input 2 (b4 |+ (b5 |<< 32));
  lemma_helper_30 b6 b7; 
  upd_wide input 3 (b6 |+ (b7 |<< 32)); 
  let h1 = ST.get() in
  admitP (True /\ eval h1 input 4 = eval h0 b' 8) // Moving the content from template t:i->32 to t':i->64


val mod_2_64: x:wide -> Tot (y:wide{v y = v x % pow2 64})
let mod_2_64 x = 
  admit(); // In the semantics of the bitwise operator &, to add to axioms
  let mask64 = (one_wide |<< 64) |- one_wide in 
  let r = log_and_wide x mask64 in  
  r
  
val lemma_helper_40: a:wide -> b:wide -> c:wide -> Lemma
  (requires (v a < pow2 64 /\ v b < pow2 105 /\ v c < pow2 41))
  (ensures (v a + v b + v c < pow2 106 /\ v a + v b + v c < pow2 128))
let lemma_helper_40 a b c =
  //@@
  pow2_increases_lemma 64 41; 
  Lemmas.pow2_double_sum 64;
  Lemmas.pow2_double_sum 104;
  cut (True /\ v a + v c < pow2 65);
  pow2_increases_lemma 105 65;
  pow2_increases_lemma 128 106

val lemma_helper_41: a:wide -> b:wide -> Lemma
  (requires (v a < pow2 105 /\ v b = pow2 110 + pow2 32 - 1))
  (ensures (v a + v b < pow2 111 /\ v a + v b < pow2 128))
let lemma_helper_41 a b =
  //@@
  pow2_increases_lemma 104 32;
  pow2_increases_lemma 110 105;
  pow2_increases_lemma 128 111

val lemma_helper_42: a:wide -> b:wide -> Lemma
  (requires (v a < pow2 64 /\ v b < pow2 64))
  (ensures (v a + v b < pow2 65 /\ v a + v b < pow2 128))
let lemma_helper_42 a b =
  Lemmas.pow2_double_sum 64;
  pow2_increases_lemma 128 65

val lemma_helper_43: a:wide -> b:wide -> Lemma
  (requires (v a < pow2 64 /\ v b < pow2 105))
  (ensures  (v a + v b < pow2 106 /\ v a + v b < pow2 128))
let lemma_helper_43 a b = 
  pow2_increases_lemma 105 64;
  Lemmas.pow2_double_sum 105;
  pow2_increases_lemma 128 106

val lemma_helper_44: a:wide -> b:wide -> c:wide -> Lemma
  (requires (v a = pow2 64 - 1 /\ v b = pow2 110 + pow2 32 - 1 /\ v c = pow2 64 - pow2 32))
  (ensures  (v a > pow2 63 /\ v b > pow2 63 /\ v c > pow2 63))
let lemma_helper_44 a b c =
  pow2_increases_lemma 110 64;
  pow2_increases_lemma 63 32;
  pow2_increases_lemma 64 62;
  Lemmas.pow2_double_sum 62;
  Lemmas.pow2_double_sum 63

#reset-options

val add_zero_110: tmp:bigint_large -> input:bigint_large{getRef tmp <> getRef input} -> ST unit
  (requires (fun h -> live h input /\ getLength h input = 4 /\ live h tmp /\ getLength h tmp = 4
      /\ v (getValue h input 0) < pow2 105 /\ v (getValue h input 1) < pow2 105
      /\ v (getValue h input 2) < pow2 105 /\ v (getValue h input 3) < pow2 105))
  (ensures (fun h0 _ h1 -> live h0 input /\ live h1 tmp /\ getLength h1 tmp = 4 /\ getLength h0 input = 4
    /\ v (getValue h1 tmp 0) < pow2 106 /\ v (getValue h1 tmp 1) < pow2 111
    /\ v (getValue h1 tmp 2) < pow2 65  /\ v (getValue h1 tmp 3) < pow2 106
    /\ v (getValue h1 tmp 0) >= pow2 64 - 1  /\ v (getValue h1 tmp 1) > pow2 110
    /\ v (getValue h1 tmp 3) > pow2 63
    /\ eval h1 tmp 4 = eval h0 input 4
    /\ modifies !{getRef tmp} h0 h1))
let add_zero_110 tmp input =
  //@@
  let h0 = ST.get() in
  let zero110 = zero_110 () in
  let z3 = index_wide zero110 3 in
  let z2 = index_wide zero110 2 in
  let z1 = index_wide zero110 1 in
  let z0 = index_wide zero110 0 in
  let i3 = index_wide input   3 in
  let i2 = index_wide input   2 in
  let i1 = index_wide input   1 in
  let i0 = index_wide input   0 in
  let r2 = mod_2_64 i2 in
  let c2 = i2 |>> 64 in
  admitP (True /\ v c2 < pow2 41);
  lemma_helper_40 z3 i3 c2;
  let t3 = z3 |+ i3 |+ c2 in
  lemma_helper_42 z2 r2; 
  let t2 = z2 |+ r2 in
  lemma_helper_41 i1 z1;
  let t1 = i1 |+ z1 in
  lemma_helper_43 z0 i0;
  let t0 = z0 |+ i0 in
  lemma_helper_44 z0 z1 z3;
  upd_wide tmp 3 t3;
  upd_wide tmp 2 t2;
  upd_wide tmp 1 t1;
  upd_wide tmp 0 t0;
  Lemmas.pow2_double_sum 63;
  let h1 = ST.get() in
  admitP (True /\ eval h1 tmp 4 = eval h0 input 4) // Adding P256

#reset-options

val lemma_helper_51: c3:wide -> c3_2_32:wide -> Lemma 
  (requires (v c3 < pow2 42 /\ c3_2_32 = (c3 |<< 32)))
  (ensures  (v c3_2_32 < pow2 74 /\ v c3_2_32 = v c3 * pow2 32))
let lemma_helper_51 c3 c3_2_32 =
  coerce
    (requires (v c3 < pow2 42 /\ c3_2_32 = (c3 |<< 32)))
    (ensures  (v c3_2_32 < pow2 74 /\ v c3_2_32 = v c3 * pow2 32))
    (fun _ -> Lemmas.pow2_exp_1 42 32;
	    cut (True /\ v c3 * pow2 32 < pow2 74);
	    pow2_increases_lemma 128 74;
	    lemma_helper_00 (v c3 * pow2 32) (pow2 128))

val lemma_helper_52: r3:wide -> c3_2_32:wide -> c3:wide -> Lemma
  (requires (v r3 < pow2 64 /\ v c3_2_32 < pow2 74 /\ v c3 < pow2 42 /\ v c3_2_32 = v c3 * pow2 32))
  (ensures (v r3 + v c3_2_32 < pow2 128 /\ v r3 + v c3_2_32 >= v c3 /\ v r3 + v c3_2_32 - v c3 < pow2 75))
let lemma_helper_52 r3 c3_2_32 c3 =
  pow2_increases_lemma 64 42;
  pow2_increases_lemma 74 42;
  pow2_increases_lemma 74 64;
  Lemmas.pow2_double_sum 74;
  pow2_increases_lemma 128 75

val lemma_helper_53: t1:wide -> c3_2_32:wide -> Lemma
  (requires (v t1 < pow2 111 /\ v t1 > pow2 110 /\ v c3_2_32 < pow2 74))
  (ensures (v t1 >= v c3_2_32 /\ v t1 - v c3_2_32 < pow2 111 /\ v t1 - v c3_2_32 > pow2 109))
let lemma_helper_53 t1 c3_2_32 =
  pow2_increases_lemma 110 74;
  pow2_increases_lemma 109 74;
  Lemmas.pow2_double_sum 109

val lemma_helper_54: t0:wide -> c3:wide -> Lemma
  (requires (v t0 < pow2 106 /\ v c3 < pow2 42))
  (ensures (v t0 + v c3 < pow2 128))
let lemma_helper_54 t0 c3 = 
  pow2_increases_lemma 106 42;
  Lemmas.pow2_double_sum 106;
  pow2_increases_lemma 128 107

val carry_top_1: t:bigint_large -> ST unit
  (requires (fun h -> live h t /\ getLength h t = 4
    /\ v (getValue h t 0) < pow2 106 /\ v (getValue h t 1) < pow2 111
    /\ v (getValue h t 2) < pow2 65 /\ v (getValue h t 3) < pow2 106
    /\ v (getValue h t 0) >= pow2 64 - 1 /\ v (getValue h t 1) > pow2 110
    /\ v (getValue h t 3) > pow2 63 ))
  (ensures (fun h0 _ h1 -> live h1 t /\ getLength h1 t = 4 /\ live h0 t /\ getLength h0 t = 4
    /\ v (getValue h1 t 0) < pow2 106 + pow2 42
    /\ v (getValue h1 t 1) < pow2 111
    /\ v (getValue h1 t 2) < pow2 65
    /\ v (getValue h1 t 3) < pow2 75
    /\ v (getValue h1 t 0) >= pow2 64 - 1
    /\ v (getValue h1 t 1) > pow2 109
    /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime
    /\ modifies !{getRef t} h0 h1))
let carry_top_1 t =
  //@@
  let h0 = ST.get() in
  let t3 = index_wide t 3 in
  let t1 = index_wide t 1 in
  let t0 = index_wide t 0 in
  let c3 = t3 |>> 64 in
  admitP (True /\ v c3 < pow2 42); // From the semantics of '>>', must be ported to axioms
  let r3 = mod_2_64 t3 in
  let c3_2_32 = c3 |<< 32 in
  lemma_helper_51 c3 c3_2_32; 
  Lemmas.pow2_double_sum 110; 
  Lemmas.pow2_double_sum 64; 
  lemma_helper_52 r3 c3_2_32 c3;
  let t3' = (r3 |+ c3_2_32) |- c3 in
  lemma_helper_53 t1 c3_2_32;
  let t1' = t1 |- c3_2_32 in
  lemma_helper_54 t0 c3;
  let t0' = t0 |+ c3 in
  upd_wide t 3 t3'; 
  upd_wide t 1 t1'; 
  upd_wide t 0 t0'; 
  let h1 = ST.get() in
  admitP(True /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime)

#reset-options

val lemma_helper_61: c3:wide -> c3_2_32:wide -> Lemma 
  (requires (v c3 < pow2 11 /\ c3_2_32 = (c3 |<< 32)))
  (ensures  (v c3_2_32 < pow2 43 /\ v c3_2_32 = v c3 * pow2 32))
let lemma_helper_61 c3 c3_2_32 =
  coerce
    (requires (v c3 < pow2 11 /\ c3_2_32 = (c3 |<< 32)))
    (ensures  (v c3_2_32 < pow2 43 /\ v c3_2_32 = v c3 * pow2 32))
    (fun _ -> Lemmas.pow2_exp_1 11 32;
	    cut (True /\ v c3 * pow2 32 < pow2 43);
	    pow2_increases_lemma 128 43;
	    lemma_helper_00 (v c3 * pow2 32) (pow2 128))

val lemma_helper_62: r3:wide -> c3_2_32:wide -> c3:wide -> Lemma
  (requires (v r3 < pow2 64 /\ v c3_2_32 < pow2 43 /\ v c3 < pow2 11 /\ v c3_2_32 = v c3 * pow2 32))
  (ensures (v r3 + v c3_2_32 < pow2 128 /\ v r3 + v c3_2_32 >= v c3 /\ v r3 + v c3_2_32 - v c3 < pow2 64 + pow2 44))
let lemma_helper_62 r3 c3_2_32 c3 =
  pow2_increases_lemma 64 11;
  pow2_increases_lemma 43 11;
  pow2_increases_lemma 64 43;
  Lemmas.pow2_double_sum 43;
  Lemmas.pow2_double_sum 64;
  pow2_increases_lemma 128 65

val lemma_helper_63: t1:wide -> c3_2_32:wide -> Lemma
  (requires (v t1 < pow2 111 /\ v t1 > pow2 109 /\ v c3_2_32 < pow2 43))
  (ensures (v t1 >= v c3_2_32 /\ v t1 - v c3_2_32 < pow2 128 /\ v t1 - v c3_2_32 > pow2 108))
let lemma_helper_63 t1 c3_2_32 = 
  pow2_increases_lemma 109 43;
  pow2_increases_lemma 108 43;
  pow2_increases_lemma 128 109

val lemma_helper_64: t0:wide -> c3:wide -> Lemma
  (requires (v t0 < pow2 106 + pow2 42 /\ v c3 < pow2 11))
  (ensures  (v t0 + v c3 < pow2 128 /\ v t0 + v c3 < pow2 106 + pow2 43))
let lemma_helper_64 t0 c3 = 
  pow2_increases_lemma 42 11;
  pow2_increases_lemma 127 106;
  pow2_increases_lemma 127 43;
  Lemmas.pow2_double_sum 127

val carry_top_2: t:bigint_large -> ST unit
  (requires (fun h -> live h t /\ getLength h t = 4
    /\ v (getValue h t 0) < pow2 106 + pow2 42 /\ v (getValue h t 0) >= pow2 64 - 1
    /\ v (getValue h t 1) < pow2 111 /\ v (getValue h t 1) > pow2 109
    /\ v (getValue h t 2) < pow2 65
    /\ v (getValue h t 3) < pow2 75 ))
  (ensures (fun h0 _ h1 -> live h1 t /\ getLength h1 t = 4 /\ live h0 t /\ getLength h0 t = 4
    /\ v (getValue h1 t 0) < pow2 106 + pow2 43 /\ v (getValue h1 t 0) >= pow2 64 - 1
    /\ v (getValue h1 t 1) < pow2 111 /\ v (getValue h1 t 1) > pow2 108
    /\ v (getValue h1 t 2) < pow2 65
    /\ v (getValue h1 t 3) < pow2 64 + pow2 44
    /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime
    /\ modifies !{getRef t} h0 h1))
let carry_top_2 t =
  //@@
  let h0 = ST.get() in
  let t3 = index_wide t 3 in
  let t1 = index_wide t 1 in
  let t0 = index_wide t 0 in
  let c3 = t3 |>> 64 in
  admitP (True /\ v c3 < pow2 11); // From the semantics of '>>', must be ported to axioms
  let r3 = mod_2_64 t3 in
  let c3_2_32 = c3 |<< 32 in
  lemma_helper_61 c3 c3_2_32;
  lemma_helper_62 r3 c3_2_32 c3;
  let t3' = r3 |+ c3_2_32 |- c3 in
  lemma_helper_63 t1 c3_2_32;
  let t1' = t1 |- c3_2_32 in
  lemma_helper_64 t0 c3;
  let t0' = t0 |+ c3 in 
  upd_wide t 3 t3';
  upd_wide t 1 t1';
  upd_wide t 0 t0';
  let h1 = ST.get() in
  admitP(True /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime)

val cond_subtract_prime: t:bigint_large -> ST unit
  (requires (fun h -> live h t /\ getLength h t = 4
    /\ v (getValue h t 0) < pow2 106 + pow2 43 /\ v (getValue h t 0) >= pow2 64 - 1
    /\ v (getValue h t 1) < pow2 111 /\ v (getValue h t 1) > pow2 108
    /\ v (getValue h t 2) < pow2 65
    /\ v (getValue h t 3) < pow2 64 + pow2 44 ))
  (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ getLength h0 t = 4 /\ getLength h1 t = 4
    /\ (v (getValue h0 t 3) >= pow2 64 - pow2 32 + 1 ==> (
	v (getValue h1 t 3) < pow2 45 /\ v (getValue h1 t 2) < pow2 65
	/\ v (getValue h1 t 1) < pow2 111 /\ v (getValue h1 t 0) < pow2 106 + pow2 43 ) )
    /\ (v (getValue h0 t 3) < pow2 64 - pow2 32 + 1 ==> (
	v (getValue h1 t 2) < pow2 65 /\ v (getValue h1 t 1) < pow2 111 
	/\ v (getValue h1 t 0) < pow2 106 + pow2 43))
    /\ eval h1 t 4 % reveal prime = eval h0 t 4 % reveal prime
    /\ modifies !{getRef t} h0 h1 ))
let cond_subtract_prime tmp =
  admit();
  let prime = kPrime () in
  let t3 = index_wide tmp 3 in
  let kPrime3Test = ((one_wide |<< 64) |- (one_wide |<< 32)) |+ one_wide in
  let mask = gte_wide t3 kPrime3Test in
  (* Conditionnally subtract the prime *)
  let t0 = index_wide tmp 0 in
  let t1 = index_wide tmp 1 in
  let t3 = index_wide tmp 3 in
  let p0 = index_wide prime 0 in
  let p1 = index_wide prime 1 in
  let p3 = index_wide prime 3 in
  upd_wide tmp 0 (t0 |- (mask |& p0));
  upd_wide tmp 1 (t1 |- (mask |& p1));
  upd_wide tmp 3 (t3 |- (mask |& p3))

val carry_pass: t:bigint_large -> ST unit
  (requires (fun h -> live h t /\ getLength h t = 4
    /\ ((v (getValue h t 3) < pow2 45 /\ v (getValue h t 2) < pow2 65
      /\ v (getValue h t 1) < pow2 111 /\ v (getValue h t 0) < pow2 106 + pow2 43 )
      \/ (v (getValue h t 2) < pow2 65 /\ v (getValue h t 1) < pow2 111 
	/\ v (getValue h t 0) < pow2 106 + pow2 43)) ))
  (ensures (fun h0 _ h1 -> live h0 t /\ getLength h0 t = 4 /\ live h1 t /\ getLength h1 t = 4
    /\ eval h1 t 4 = eval h0 t 4
    /\ modifies !{getRef t} h0 h1
    /\ v (getValue h1 t 0) < pow2 64
    /\ v (getValue h1 t 1) < pow2 64
    /\ v (getValue h1 t 2) < pow2 64
    /\ v (getValue h1 t 3) < pow2 64 ))
let carry_pass tmp =
  admit();
  let mask64 = (one_wide |<< 64) |- one_wide in
  let t0 = index_wide tmp 0 in
  let t1 = index_wide tmp 1 in
  upd_wide tmp 1 (t1 |+ (t0 |>> 64));
  upd_wide tmp 0 (t0 |& mask64);
  let t1 = index_wide tmp 1 in
  let t2 = index_wide tmp 2 in
  let t3 = index_wide tmp 3 in
  upd_wide tmp 2 (t2 |+ (t1 |>> 64));
  let t2 = index_wide tmp 2 in
  upd_wide tmp 1 (t1 |& mask64);
  upd_wide tmp 3 (t3 |+ (t2 |>> 64));
  upd_wide tmp 2 (t2 |& mask64)

val expand: b:bigint_wide -> t:bigint_large{getRef t <> getRef b} -> ST unit
  (requires (fun h -> live h t /\ live h b /\ getLength h b >= 8 /\ getLength h t >= 4
    /\ v (getValue h t 0) < pow2 64 
    /\ v (getValue h t 1) < pow2 64 
    /\ v (getValue h t 2) < pow2 64 
    /\ v (getValue h t 3) < pow2 64 ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h0 b /\ live h0 t /\ getLength h0 t >= 4 /\ getLength h0 b >= 8
    /\ getLength h1 b = getLength h0 b
    /\ Standardized h1 b
    /\ eval h1 b 8 = eval h0 t 4
    /\ modifies !{getRef b} h0 h1 ))    
let expand b' tmp =
  admit();
  let t0 = index_wide tmp 0 in
  let t1 = index_wide tmp 1 in
  let t2 = index_wide tmp 2 in
  let t3 = index_wide tmp 3 in
  let mask32 = to_wide "0xffffffff" in
  upd_wide b' 0 (t0 |& mask32);
  upd_wide b' 1 (t0 |>> 32);
  upd_wide b' 2 (t1 |& mask32);
  upd_wide b' 3 (t1 |>> 32);
  upd_wide b' 4 (t2 |& mask32);
  upd_wide b' 5 (t2 |>> 32);
  upd_wide b' 6 (t3 |& mask32);
  upd_wide b' 7 (t3 |>> 32)

val lemma_helper_80: h0:heap -> h1:heap -> h2:heap -> h3:heap -> b:bigint_wide -> i:bigint_large -> t:bigint_large -> Lemma 
  (requires (live h0 b /\ not(contains h0 (getRef i)) /\ not(contains h0 (getRef t)) /\ modifies !{} h0 h1 /\ modifies !{getRef t} h1 h2
    /\ modifies !{getRef b} h2 h3))
  (ensures  (modifies !{getRef b} h0 h3))
let lemma_helper_80 h0 h1 h2 h3 b i t = ()

// Input comes from freduce_degree so all limbs are < 2 ^ 72
val freduce_coefficients: b:bigint_wide -> ST unit 
  (requires (fun h -> Reduced h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b 8 /\ Reduced h0 b /\ Standardized h1 b
    /\ eval h1 b 8 % reveal prime = eval h0 b 8 % reveal prime
    /\ modifies !{getRef b} h0 h1))
let freduce_coefficients b' =
  //@@
  let h0 = ST.get() in
  let input = create_wide_templ 4 templ_large in
  let h0' = ST.get() in
  eval_eq_lemma h0 h0' b' b' 8;
  shrink input b';
  let h1 = ST.get() in
  cut (modifies !{} h0 h1); 
  cut (True /\ eval h1 input 4 = eval h0 b' 8);
  (* At this point, eval b 8 with templ = eval input 4 with (x -> 64) *)
  // Code taken from openSSL NistP256 "felem_shrink"
  let tmp = create_wide_templ 4 templ_large in
  let h1' = ST.get() in
  eval_eq_lemma h1 h1' input input 4; 
  add_zero_110 tmp input; 
  carry_top_1 tmp; 
  carry_top_2 tmp; 
  (* Conditionnally subtract the prime value *)
  cond_subtract_prime tmp;
  let h2 = ST.get () in
  cut (modifies !{} h0 h2);
  cut (True /\ eval h2 tmp 4 % reveal prime = eval h0 b' 8 % reveal prime); 
  (* Carry pass *)
  carry_pass tmp;
  (* Expand tmp into b' *)
  let h3 = ST.get() in
  cut (modifies !{getRef tmp} h2 h3);
  expand b' tmp;
  let h1 = ST.get() in 
  cut (eval h1 b' 8 % reveal prime = eval h0 b' 8 % reveal prime /\ True); 
  lemma_helper_80 h0 h2 h3 h1 b' input tmp

#reset-options

val freduce_degree: b:bigint_wide -> ST unit 
  (requires (fun h -> Reducible h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b 15 /\ Reducible h0 b /\ Standardized h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime
    /\ modifies !{getRef b} h0 h1))
let freduce_degree b =
  freduce_degree' b;
  freduce_coefficients b

#reset-options

(* Unit, just to fill in the interface *)
val carry_top_to_0: bigint_wide -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> h0==h1))
let carry_top_to_0 b = ()

let add_big_zero b =
  admit(); // Adds P256<<1 shaped such that all limbs are >= 2^32 and < 2^33, to provide "Filled h1 b 32 33"
  let two33m1 = to_limb "0x1fffffffe" in
  let two33m2 = to_limb "0x1fffffffc" in
  let two33   = to_limb "0x200000000" in
  let b0 = index_limb b 0 in
  upd_limb b 0 (add_limb b0 two33m1);
  let b1 = index_limb b 1 in
  upd_limb b 1 (add_limb b1 two33m1); 
  let b2 = index_limb b 2 in
  upd_limb b 2 (add_limb b2 two33m1); 
  let b3 = index_limb b 3 in
  upd_limb b 3 (add_limb b3 two33); 
  let b4 = index_limb b 4 in
  upd_limb b 4 (add_limb b4 two33m1);
  let b5 = index_limb b 5 in
  upd_limb b 5 (add_limb b5 two33m1);
  let b6 = index_limb b 6 in
  upd_limb b 6 (add_limb b6 two33); 
  let b7 = index_limb b 7 in
  upd_limb b 7 (add_limb b7 two33m2)

val subtract_u64: r:ref limb -> c:ref limb -> x:limb -> ST unit 
  (requires (fun h -> contains h r /\ contains h c)) 
  (ensures (fun h0 _ h1 -> True))
let subtract_u64 result carry v =
  let z = !result in
  let r = limb_to_wide z in
  pow2_increases_lemma platform_wide platform_size;
  let r = UInt.sub_mod_wide r (limb_to_wide v) in
  carry := wide_to_limb ((r |>> 64) |& one_wide);
  result := wide_to_limb r

val felem_contract_loop: output:bigint -> prime:bigint_wide -> mask:ref limb -> res:ref limb -> 
  ctr:nat -> ST unit
  (requires (fun h -> True)) 
  (ensures (fun h0 _ h1 -> True))
let rec felem_contract_loop output prime all_equal_so_far result ctr =
  admit(); // TOOD
  match ctr with
  | 0 -> ()
  | _ -> 
    let i = ctr - 1 in
    let pi = index_wide prime i in
    let oi = index_limb output i in
    let a = pi |- limb_to_wide (oi) in
    result := log_or_limb (!all_equal_so_far) (wide_to_limb (a |>> 64));
    let equal = log_xor_limb (wide_to_limb pi) (oi) in
    let equal = sub_limb equal one_limb in
    let equal = log_and_limb equal (shift_left_limb equal 32) in
    let equal = log_and_limb equal (shift_left_limb equal 16) in
    let equal = log_and_limb equal (shift_left_limb equal 8) in
    let equal = log_and_limb equal (shift_left_limb equal 4) in
    let equal = log_and_limb equal (shift_left_limb equal 2) in
    let equal = log_and_limb equal (shift_left_limb equal 1) in
    let equal = eq_limb (log_and_limb (shift_right_limb equal 63) one_limb) one_limb in
    all_equal_so_far := log_and_limb (!all_equal_so_far) equal;
    felem_contract_loop output prime all_equal_so_far result (ctr-1)

val normalize: b:bigint -> ST unit 
  (requires (fun h -> Standardized h b /\ getLength h b >= 8))
  (ensures (fun h0 _ h1 -> Standardized h0 b /\ getLength h0 b >= 8 /\ live h1 b /\ 
    getLength h1 b = getLength h0 b
    /\ eval h1 b 8 = eval h0 b 8 % reveal prime))
let normalize output =  
  admit(); // Not machine checked
  let input = create_limb 4 in
  let b0 = index_limb output 0 in 
  let b1 = index_limb output 1 in 
  let b2 = index_limb output 2 in 
  let b3 = index_limb output 3 in
  let b4 = index_limb output 4 in 
  let b5 = index_limb output 5 in 
  let b6 = index_limb output 6 in 
  let b7 = index_limb output 7 in
  upd_limb input 0 (add_limb b0 (shift_left_limb b1 32));
  upd_limb input 1 (add_limb b2 (shift_left_limb b3 32));
  upd_limb input 2 (add_limb b4 (shift_left_limb b5 32));
  upd_limb input 3 (add_limb b6 (shift_left_limb b7 32));
  let all_equal_so_far = ref (to_limb "0xffffffffffffffff") in
  let result = ref zero_limb in
//  all_equal_so_far := sub_limb (!all_equal_so_far) one_limb;
  let prime = kPrime () in
  felem_contract_loop input prime all_equal_so_far result 4;  
  result := log_or_limb (!result) (!all_equal_so_far);
  let final_result = !result in
  let carry = ref zero_limb in
  result := index_limb input 0;
  let p0 = index_wide prime 0 in
  subtract_u64 result carry (log_and_limb final_result (wide_to_limb p0));
  upd_limb input 0 !result;
  result := index_limb input 1;
  subtract_u64 result carry (!carry);
  upd_limb input 1 !result;
  result := index_limb input 2;
  subtract_u64 result carry (!carry);
  upd_limb input 2 !result;
  result := index_limb input 3;
  subtract_u64 result carry (!carry);
  upd_limb input 3 !result;
  let p1 = index_wide prime 1 in
  result := index_limb input 1;
  subtract_u64 result carry (log_and_limb final_result (wide_to_limb p1));
  upd_limb input 1 !result;
  result := index_limb input 2;
  subtract_u64 result carry (!carry);
  upd_limb input 2 !result;
  result := index_limb input 3;
  subtract_u64 result carry (!carry);
  upd_limb input 3 !result;
  let p2 = index_wide prime 2 in
  result := index_limb input 2;
  subtract_u64 result carry (log_and_limb final_result (wide_to_limb p2));
  upd_limb input 2 !result;
  result := index_limb input 3;
  subtract_u64 result carry (!carry);
  upd_limb input 3 !result;
  let p3 = index_wide prime 3 in
  result := index_limb input 3;
  subtract_u64 result carry (log_and_limb final_result (wide_to_limb p3));
  upd_limb input 3 !result;
  let mask32 = to_limb "0xffffffff" in
  let i0 = index_limb input 0 in
  let i1 = index_limb input 1 in
  let i2 = index_limb input 2 in
  let i3 = index_limb input 3 in
  upd_limb output 0 (log_and_limb (i0) mask32);
  upd_limb output 1 (shift_right_limb (i0) 32);
  upd_limb output 2 (log_and_limb (i1) mask32);
  upd_limb output 3 (shift_right_limb (i1) 32);
  upd_limb output 4 (log_and_limb (i2) mask32);
  upd_limb output 5 (shift_right_limb (i2) 32);
  upd_limb output 6 (log_and_limb (i3) mask32);
  upd_limb output 7 (shift_right_limb (i3) 32)
