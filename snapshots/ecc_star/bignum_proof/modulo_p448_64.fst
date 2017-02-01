(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --z3rlimit 15 --verify_module Modulo;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters_448_64.fst $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst modulo_lemmas.fst modulo.fsti;
  --*)

module Modulo

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
let op_Bar_Plus x y = add_wide x y
let op_Bar_Star x y = mul_wide x y

let satisfies_modulo_constraints h b =
  getLength h b >= 2*norm_length-1 && getTemplate b = templ
  && maxValue h b < pow2 (platform_wide - 3)

val lemma_satisfies: h:heap -> b:bigint_wide -> n:nat -> Lemma
  (requires (live h b /\ (forall (i:nat). i < getLength h b ==> v (getValue h b i) < pow2 n)))
  (ensures  (live h b /\ maxValue h b < pow2 n))
let lemma_satisfies h b n = ()  

let sum_satisfies_constraints h0 h1 cpy a b =
  //@@
  pow2_double_sum 56;
  cut (forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < norm_length 
	    ==> v (getValue h1 cpy i) < pow2 57);
  cut (forall (i:nat). {:pattern (v (getValue h1 cpy i))} (i >= norm_length /\ i < getLength h1 cpy)
	    ==> v (getValue h1 cpy i) = 0);
  cut(forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < getLength h1 cpy
	   ==> v (getValue h1 cpy i) < pow2 57);
  lemma_satisfies h1 cpy 57;
  pow2_increases_lemma (platform_wide - 3) 57

let n0 = ndiff'
let n1 = ndiff

let difference_satisfies_constraints h0 h1 cpy a b =
  //@@
  cut(forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < getLength h1 cpy
	   ==> v (getValue h1 cpy i) < pow2 58);
  lemma_satisfies h1 cpy 58;
  pow2_increases_lemma (platform_wide - 3) 58  

val lemma_satisfies_2: h:heap -> b:bigint -> Lemma 
  (requires (Standardized h b))
  (ensures  (Standardized h b /\ maxValueNorm h b < pow2 56))
let lemma_satisfies_2 h b = ()

val lemma_satisfies_4: a:nat -> b:nat -> c:pos -> d:pos -> Lemma (requires (a < c /\ b < d))
							    (ensures (a * b < c * d))
let lemma_satisfies_4 a b c d = ()

val lemma_satisfies_3: b:nat -> c:nat -> Lemma
  (requires (b < pow2 56 /\ c < pow2 56))
  (ensures (norm_length * b * c <= pow2 115))
let lemma_satisfies_3 b c = 
  cut (True /\ 8 = pow2 3);
  pow2_exp_lemma 56 56;
  pow2_exp_lemma 3 112;
  Axiomatic.paren_mul_right norm_length b c;
  lemma_satisfies_4 b c (pow2 56) (pow2 56)

let mul_satisfies_constraints h0 h1 res a b =
  lemma_satisfies_2 h0 a;
  lemma_satisfies_2 h0 b;
  lemma_satisfies_3 (maxValueNorm h0 a) (maxValueNorm h0 b);
  pow2_increases_lemma (platform_wide - 3) 115

type Updated (h0:heap) (h1:heap) (b:bigint_wide) (len:nat) =
  live h0 b /\ live h1 b /\ getLength h0 b >= len /\ getLength h1 b = getLength h0 b

val lemma_helper_000: ctr:nat{ctr>=2} -> Lemma (ctr-1+norm_length = ctr+norm_length-1 
					   /\ ctr+norm_length-1 = (ctr-1) + norm_length
					   /\ (ctr+norm_length-1)-1=ctr+norm_length-2)
let lemma_helper_000 ctr = ()					   

val lemma_helper_001: ctr:nat{ctr>=2} -> Lemma 
  (bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 56)
let lemma_helper_001 ctr = 
  bitweight_definition templ (ctr+norm_length-2)

val lemma_helper_002: a:nat -> b:nat -> Lemma (bitweight templ (a+b) = bitweight templ a + bitweight templ b)
let rec lemma_helper_002 a b = match a with | 0 -> () | _ -> lemma_helper_002 (a-1) b

val lemma_helper_003: ctr:nat{ctr>=2} -> Lemma (pow2 56 * pow2 (bitweight templ (ctr-2)) = pow2 (bitweight templ (ctr-1)))
let lemma_helper_003 ctr = 
  bitweight_definition templ 1;
  lemma_helper_002 1 (ctr-2); 
  Lemmas.pow2_exp_1 56 (bitweight templ (ctr-2))

val lemma_helper_004: ctr:nat{ctr>=2} -> Lemma
  (requires (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 56 * pow2 (bitweight templ (ctr+norm_length-2))))
  (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let lemma_helper_004 ctr =
  //@@ long
  lemma_helper_002 (ctr-2) norm_length;
  Lemmas.pow2_exp_1 (bitweight templ (ctr-2)) (bitweight templ norm_length);
  Axiomatic.paren_mul_right (pow2 56) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
  lemma_helper_003 ctr

val pow2_bitweight_lemma_1: ctr:pos -> 
  Lemma
    (requires (True))
    (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let rec pow2_bitweight_lemma_1 ctr =
  //@@
  match ctr with
  | 1 -> ()
  | _ -> 
    lemma_helper_000 ctr;
    pow2_bitweight_lemma_1 (ctr-1);
    lemma_helper_001 ctr;
    bitweight_definition templ (ctr+norm_length-2);
    Lemmas.pow2_exp_1 56 (bitweight templ (ctr+norm_length-2)); 
    lemma_helper_004 ctr

val bitweight_norm_length_lemma: unit -> Lemma (requires (True)) (ensures (bitweight templ norm_length = 448))
let bitweight_norm_length_lemma () = 
  //@@
  bitweight_definition templ (norm_length-1);
  bitweight_definition templ (norm_length-2);
  bitweight_definition templ (norm_length-3);
  bitweight_definition templ (norm_length-4);
  bitweight_definition templ (norm_length-5);
  bitweight_definition templ (norm_length-6);
  bitweight_definition templ (norm_length-7);
  bitweight_definition templ (norm_length-8)

(* 
   P_448 = 2^448 - 2^224 - 1, hence 
     a[i+0] + 2^56*a[i+1] + 2^112*a[i+2] + 2^168*a[i+3] + 2^224*a[i+4] 
            + 2^280*a[i+5] + 2^336*a[i+6] + 2^392*a[i+7] + 2^448*a[i+8]
  = (a[i+0]+a[i+8]) + 2^56*a[i+1] + 2^112*a[i+2] + 2^168*a[i+3] + 2^224*(a[i+4]+a[i+8])
		    + 2^280*a[i+5] + 2^336*a[i+6] + 2^392*a[i+7] 
 *)
assume val freduce_degree_lemma_0: h0:heap -> h1:heap -> b:bigint_wide -> ctr:nat{ctr < norm_length-1 /\ Updated h0 h1 b (norm_length+1+ctr)} -> Lemma
  (requires (forall (i:nat). {:pattern (v (getValue h1 b i))} (i < getLength h0 b /\ i <> ctr /\ i <> ctr+4) ==>
				(v (getValue h1 b i) = v (getValue h0 b i)
				/\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + v (getValue h0 b (ctr+8))
				/\ v (getValue h1 b (ctr+4)) = v (getValue h0 b (ctr+4)) + v (getValue h0 b (ctr+8))) ))
  (ensures (eval h0 b (9+ctr) % reveal prime = eval h1 b (8+ctr) % reveal prime))

val lemma_helper_0: x:wide -> y:wide -> Lemma 
  (requires (v x < pow2 (platform_wide - 3) /\ v y < pow2 (platform_wide - 3) ))
  (ensures (v x + v y < pow2 platform_wide))
let lemma_helper_0 x y = 
  //@@
  ()

type Reducible h b = 
  live h b /\ getLength h b >= 2 * norm_length - 1
  /\ v (getValue h b 0 ) < pow2 (platform_wide-3)  /\ v (getValue h b 1 ) < pow2 (platform_wide-3)
  /\ v (getValue h b 2 ) < pow2 (platform_wide-3)  /\ v (getValue h b 3 ) < pow2 (platform_wide-3)
  /\ v (getValue h b 4 ) < pow2 (platform_wide-3)  /\ v (getValue h b 5 ) < pow2 (platform_wide-3)
  /\ v (getValue h b 6 ) < pow2 (platform_wide-3)  /\ v (getValue h b 7 ) < pow2 (platform_wide-3)
  /\ v (getValue h b 8 ) < pow2 (platform_wide-3)  /\ v (getValue h b 9 ) < pow2 (platform_wide-3)
  /\ v (getValue h b 10) < pow2 (platform_wide-3)  /\ v (getValue h b 11) < pow2 (platform_wide-3)
  /\ v (getValue h b 12) < pow2 (platform_wide-3)  /\ v (getValue h b 13) < pow2 (platform_wide-3)
  /\ v (getValue h b 14) < pow2 (platform_wide-3)

type Reduced h0 h1 (b:bigint_wide) =
  live h0 b /\ live h1 b /\ getLength h0 b >= 2*norm_length-1 /\ getLength h1 b >= 2*norm_length-1
  /\ v (getValue h1 b 0 ) = v (getValue h0 b 0 ) 
  /\ v (getValue h1 b 1 ) = v (getValue h0 b 1)
  /\ v (getValue h1 b 2 ) = v (getValue h0 b 2 ) 
  /\ v (getValue h1 b 3 ) = v (getValue h0 b 3 ) + v (getValue h0 b 11)
  /\ v (getValue h1 b 4 ) = v (getValue h0 b 4 ) + v (getValue h0 b 12)
  /\ v (getValue h1 b 5 ) = v (getValue h0 b 5 ) + v (getValue h0 b 13)
  /\ v (getValue h1 b 6 ) = v (getValue h0 b 6 ) + v (getValue h0 b 14)
  /\ v (getValue h1 b 7 ) = v (getValue h0 b 7 ) + v (getValue h0 b 11)
  /\ v (getValue h1 b 8 ) = v (getValue h0 b 8 ) + v (getValue h0 b 12)
  /\ v (getValue h1 b 9 ) = v (getValue h0 b 9 ) + v (getValue h0 b 13)
  /\ v (getValue h1 b 10) = v (getValue h0 b 10) + v (getValue h0 b 14)

val freduce_degree_1: b:bigint_wide -> ST unit
  (requires (fun h -> Reducible h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (2*norm_length-1)
    /\ Reduced h0 h1 b
    /\ eval h1 b 11 % reveal prime = eval h0 b 15 % reveal prime))
let freduce_degree_1 b =
  //@@
  let b14 = index_wide b 14 in 
  let b13 = index_wide b 13 in
  let b12 = index_wide b 12 in
  let b11 = index_wide b 11 in
  let b10 = index_wide b 10 in
  let b9  = index_wide b 9  in
  let b8  = index_wide b 8  in
  let b7  = index_wide b 7  in
  let b6  = index_wide b 6  in
  let b5  = index_wide b 5  in
  let b4  = index_wide b 4  in
  let b3  = index_wide b 3  in
  let h0 = ST.get() in
  lemma_helper_0 b10 b14;
  lemma_helper_0 b6  b14;
  upd_wide b 10 (b10 |+ b14);
  upd_wide b 6  (b6  |+ b14);
  let h1 = ST.get() in 
  freduce_degree_lemma_0 h0 h1 b 6; 
  lemma_helper_0 b9  b13;
  lemma_helper_0 b5  b13;
  upd_wide b 9  (b9  |+ b13);
  upd_wide b 5  (b5  |+ b13);
  let h2 = ST.get() in 
  freduce_degree_lemma_0 h1 h2 b 5; 
  lemma_helper_0 b8 b12;
  lemma_helper_0 b4 b12;
  upd_wide b 8  (b8  |+ b12);
  upd_wide b 4  (b4  |+ b12);
  let h3 = ST.get() in 
  freduce_degree_lemma_0 h2 h3 b 4; 
  lemma_helper_0 b7 b11;
  lemma_helper_0 b3 b11;
  upd_wide b 7  (b7  |+ b11);
  upd_wide b 3  (b3  |+ b11);
  let h4 = ST.get() in
  freduce_degree_lemma_0 h3 h4 b 3

val lemma_helper_1: x:wide -> y:wide -> Lemma 
  (requires (v x < pow2 (platform_wide - 2) /\ v y < pow2 (platform_wide - 2) ))
  (ensures (v x + v y < pow2 platform_wide))
let lemma_helper_1 x y = ()

type Reducible2 (h:heap) (b:bigint_wide) =
  live h b /\ getLength h b >= 2 * norm_length - 1
  /\ v (getValue h b 0) < pow2 (platform_wide - 2)
  /\ v (getValue h b 1) < pow2 (platform_wide - 2)
  /\ v (getValue h b 2) < pow2 (platform_wide - 2)
  /\ v (getValue h b 3) < pow2 (platform_wide - 2)
  /\ v (getValue h b 4) < pow2 (platform_wide - 2)
  /\ v (getValue h b 5) < pow2 (platform_wide - 2)
  /\ v (getValue h b 6) < pow2 (platform_wide - 2)
  /\ v (getValue h b 7) < pow2 (platform_wide - 2)
  /\ v (getValue h b 8) < pow2 (platform_wide - 2)
  /\ v (getValue h b 9) < pow2 (platform_wide - 2)
  /\ v (getValue h b 10) < pow2 (platform_wide - 2)

type Reduced2 (h0:heap) (h1:heap) (b:bigint_wide) = 
  live h0 b /\ getLength h0 b >= 2 * norm_length - 1 /\ live h1 b /\ getLength h1 b >= 2 * norm_length - 1
  /\ v (getValue h1 b 0 ) = v (getValue h0 b 0 ) + v (getValue h0 b 8 )
  /\ v (getValue h1 b 1 ) = v (getValue h0 b 1 ) + v (getValue h0 b 9 )
  /\ v (getValue h1 b 2 ) = v (getValue h0 b 2 ) + v (getValue h0 b 10) 
  /\ v (getValue h1 b 3 ) = v (getValue h0 b 3 )
  /\ v (getValue h1 b 4 ) = v (getValue h0 b 4 ) + v (getValue h0 b 8)
  /\ v (getValue h1 b 5 ) = v (getValue h0 b 5 ) + v (getValue h0 b 9)
  /\ v (getValue h1 b 6 ) = v (getValue h0 b 6 ) + v (getValue h0 b 10)
  /\ v (getValue h1 b 7 ) = v (getValue h0 b 7 )

val freduce_degree_2: b:bigint_wide -> ST unit
  (requires (fun h -> Reducible2 h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (2*norm_length-1)
    /\ Reduced2 h0 h1 b
    /\ eval h1 b 8 % reveal prime = eval h0 b 11 % reveal prime))
let freduce_degree_2 b =
  //@@
  let b11 = index_wide b 11 in
  let b10 = index_wide b 10 in
  let b9  = index_wide b 9  in
  let b8  = index_wide b 8  in
  let b6  = index_wide b 6  in
  let b5  = index_wide b 5  in
  let b4  = index_wide b 4  in
  let b2  = index_wide b 2  in
  let b1  = index_wide b 1  in
  let b0  = index_wide b 0  in
  let h0 = ST.get() in
  lemma_helper_1 b6 b10;
  lemma_helper_1 b2 b10;
  upd_wide b 6 (b6 |+ b10);
  upd_wide b 2 (b2 |+ b10);
  let h1 = ST.get() in
  freduce_degree_lemma_0 h0 h1 b 2; 
  lemma_helper_1 b5 b9;
  lemma_helper_1 b1 b9;
  upd_wide b 5 (b5 |+ b9);
  upd_wide b 1 (b1 |+ b9);
  let h2 = ST.get() in
  freduce_degree_lemma_0 h1 h2 b 1; 
  lemma_helper_1 b4 b8;
  lemma_helper_1 b0 b8;
  upd_wide b 4  (b4  |+ b8);
  upd_wide b 0  (b0  |+ b8);
  let h3 = ST.get() in
  freduce_degree_lemma_0 h2 h3 b 0

#reset-options

val trim_2_56:x:wide -> Tot (y:wide{v y = v x % pow2 56})
let trim_2_56 x = 
  let mask = shift_left_wide one_wide 56 in
  cut (v mask = pow2 56 % pow2 platform_wide /\ pow2 56 >= 1); 
  Lemmas.pow2_increases_1 platform_wide 56; 
  ModuloLemmas.mod_lemma_1 (pow2 56) (pow2 platform_wide);
  let mask = sub_wide mask one_wide in
  let res = x |& mask in
  log_and_wide_lemma_3 x mask 56;
  res

val lemma_helper_2: bip1:wide -> c:wide -> 
  Lemma
    (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 56)))
    (ensures (v bip1 + v c < pow2 platform_wide))
let lemma_helper_2 bip1 c = 
  coerce 
    (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 56)))
    (ensures (v bip1 + v c < pow2 platform_wide))
    (fun _ -> ModuloLemmas.helper_lemma_4 (v bip1) (v c) 56 platform_wide)

val pow2_bitweight_lemma: ctr:nat -> 
  Lemma
    (requires (True))
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr)))
let pow2_bitweight_lemma ctr =
  bitweight_definition templ ctr;
  Lemmas.pow2_exp_1 (bitweight templ ctr) (templ ctr)

val eval_carry_lemma:
  ha:heap -> a:bigint_wide{live ha a /\ getLength ha a >= norm_length+1} -> 
  hb:heap -> b:bigint_wide{live hb b /\ getLength hb b >= norm_length+1} ->
  ctr:nat{ctr < norm_length} -> 
  Lemma
    (requires (
      v (getValue hb b ctr) = v (getValue ha a ctr) % pow2 (templ ctr)
      /\ v (getValue hb b (ctr+1)) = v (getValue ha a (ctr+1)) + v (getValue ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (getValue hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (getValue hb b i) = v (getValue ha a i))
    ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
let eval_carry_lemma ha a hb b ctr =
  coerce 
    (requires (
      v (getValue hb b ctr) = v (getValue ha a ctr) % pow2 (templ ctr)
      /\ v (getValue hb b (ctr+1)) = v (getValue ha a (ctr+1)) + v (getValue ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (getValue hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (getValue hb b i) = v (getValue ha a i))
    ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
    (fun _ -> 
      //@@
      eval_eq_lemma ha hb a b ctr;
      assert(eval ha a ctr = eval hb b ctr);
      eval_definition ha a (ctr+2);
      eval_definition ha a (ctr+1);
      eval_definition hb b (ctr+2);
      eval_definition hb b (ctr+1);
      ModuloLemmas.helper_lemma_0 ctr; ModuloLemmas.helper_lemma_1 ctr;
      assert(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (getValue hb b (ctr+1)) + eval hb b (ctr+1)); 
      assert(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (getValue hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (getValue hb b ctr) + eval hb b ctr));  
      assert(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (getValue ha a (ctr+1)) + v (getValue ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (getValue ha a ctr) % pow2 (templ ctr)) + eval hb b ctr)); 
      Axiomatic.distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (getValue ha a (ctr+1))) (v (getValue ha a ctr) / pow2 (templ ctr));
      cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (getValue ha a (ctr+1))
	      + pow2 (bitweight templ (ctr+1)) * v (getValue ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (getValue ha a ctr) % pow2 (templ ctr)) + eval hb b ctr)); 
      pow2_bitweight_lemma ctr; 
      cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (getValue ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (getValue ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (getValue ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));  
      ModuloLemmas.helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (getValue ha a ctr)) (eval hb b ctr); 
      cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (getValue ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * v (getValue ha a ctr) + eval hb b ctr));  
      cut(True /\ eval hb b (ctr+2) = eval ha a (ctr+2)); 
      eval_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1);
      ModuloLemmas.helper_lemma_3 (eval ha a (norm_length+1)) (eval hb b (norm_length+1)) (eval ha a (ctr+2)) (eval hb b (ctr+2)) )

opaque type Carriable (h:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h b /\ getLength h b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h b i))}
      (i > ctr /\ i <= norm_length) ==> v (getValue h b i) < pow2 (platform_wide - 1))

opaque type Carried (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ getLength h1 b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i < ctr ==> v (getValue h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (getValue h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (getValue h1 b norm_length) < pow2 72)

opaque type Untouched_2 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ getLength h0 b >= norm_length+1 /\ getLength h1 b = getLength h0 b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < getLength h0 b) ==> v (getValue h0 b i) = v (getValue h1 b i))

val freduce_lemma_0: h0:heap -> h1:heap -> h2:heap -> b:bigint_wide -> Lemma
  (requires (Reducible h0 b /\ Reduced h0 h1 b /\ Reduced2 h1 h2 b /\ v (getValue h2 b 8) = 0))
  (ensures (Carriable h2 b 0))
let freduce_lemma_0 h0 h1 h2 b = 
  pow2_double_sum (platform_wide-3);
  pow2_double_sum (platform_wide-2);
  pow2_increases_lemma (platform_wide-1) (platform_wide-3); ()

val carry: b:bigint_wide -> ctr:nat{ctr <= norm_length} -> ST unit
  (requires (fun h -> Carriable h b ctr /\ Carried h b ctr))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1)
    /\ Carried h1 b norm_length
    /\ Untouched_2 h0 h1 b ctr
    /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
    /\ modifies !{getRef b} h0 h1))
let rec carry b i =
  admit();
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index_wide b i in
    let ri = trim_2_56 bi in
    assert(v ri < pow2 (templ i)); 
    upd_wide b i ri; 
    let h1 = ST.get() in
    let c = (bi |>> 56) in
    upd_lemma h0 h1 b i ri; 
    admitP (True /\ v c < pow2 (platform_wide - 56)); // From the spec of >> on wides, to add
    let bip1 = index_wide b (i+1) in 
    lemma_helper_2 bip1 c;
    let z = bip1 |+ c in 
    upd_wide b (i+1) z;
    let h2 = ST.get() in
    upd_lemma h1 h2 b (i+1) z;
    eval_carry_lemma h0 b h2 b i;
    carry b (i+1)

#reset-options

opaque type Carried2 (h1:heap) (b:bigint_wide) =
  live h1 b /\ getLength h1 b >= norm_length + 1
  /\ v (getValue h1 b 1) < pow2 56 /\ v (getValue h1 b 2) < pow2 56 /\ v (getValue h1 b 3) < pow2 56
  /\ v (getValue h1 b 5) < pow2 56 /\ v (getValue h1 b 6) < pow2 56 /\ v (getValue h1 b 7) < pow2 56
  /\ v (getValue h1 b 0) < pow2 73 /\ v (getValue h1 b 4) < pow2 73
  /\ v (getValue h1 b norm_length) < pow2 72

val lemma_helper_3: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 56 /\ v y < pow2 72))
  (ensures (v x + v y < pow2 platform_wide /\ v x + v y < pow2 73))
let lemma_helper_3 x y = 
  pow2_increases_lemma 72 57;
  pow2_increases_lemma platform_wide 73

val carry_top_to_0:
  b:bigint_wide -> ST unit 
    (requires (fun h -> Carried h b norm_length /\ getLength h b >= norm_length+1)) 
    (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1)
      /\ Carried h0 b norm_length /\ Carried2 h1 b
      /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
      /\ v (getValue h1 b 0) = v (getValue h0 b 0) + v (getValue h0 b 8)
      /\ v (getValue h1 b 4) = v (getValue h0 b 4) + v (getValue h0 b 8)
      /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i < norm_length+1 /\ i <> 0 /\ i <> 4)
			   ==> v (getValue h1 b i) = v (getValue h0 b i))
      ))
let carry_top_to_0 b =
  //@@
  let h0 = ST.get() in
  let btop = index_wide b 8 in
  let b0 = index_wide b 0 in
  let b4 = index_wide b 4 in
  lemma_helper_3 b0 btop;
  lemma_helper_3 b4 btop;
  upd_wide b 0 (b0 |+ btop);
  upd_wide b 4 (b4 |+ btop);
  let h1 = ST.get() in
  freduce_degree_lemma_0 h0 h1 b 0

#reset-options

(* Comes from the specification of the % function, missing in Z3 theory. Must go to axioms *)
assume val lemma_helper_6: x:wide -> Lemma 
 ((v x < pow2 56 + pow2 18 /\ v x >= pow2 56) ==> v x % pow2 56 < pow2 18)

val lemma_helper_7: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 56 /\ v y < pow2 17))
  (ensures (v x + v y < pow2 57 /\ v x + v y < pow2 128))
let lemma_helper_7 x y = pow2_increases_lemma 56 18; pow2_increases_lemma 128 57

val lemma_helper_8: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 73 /\ v y < 2))
  (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 74))
let lemma_helper_8 x y = pow2_increases_lemma 128 73

val lemma_helper_9: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 56 /\ v y < pow2 18))
  (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 57))
let lemma_helper_9 x y = pow2_increases_lemma 128 57; pow2_increases_lemma 56 18

(* Comes from the fact that '/' decreases, missing from F*/Z3 theory. Must go to axioms *)
assume val lemma_helper_10: x:wide -> n:nat -> Lemma
  (requires (v x < pow2 n /\ n >= 56))
  (ensures (n >= 56 /\ v x / pow2 56 < pow2 (n-56)))

val lemma_helper_11: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 56 /\ v y < 2))
  (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 57))
let lemma_helper_11 x y = pow2_increases_lemma 128 57

val lemma_helper_12: x:wide{v x < pow2 56} -> y:wide -> ny:nat{ny < 56 /\ v y < pow2 ny} -> Lemma
  ( (v x + v y) / pow2 56 = 1 ==> (v x + v y) % pow2 56 < pow2 ny)
let lemma_helper_12 x y ny = ()  

#reset-options

val full_update: b:bigint_wide -> r0:wide -> r1:wide -> r2:wide -> r3:wide -> r4:wide -> 
  r5:wide -> r6:wide -> r7:wide -> r8:wide -> ST unit
  (requires (fun h -> live h b /\ getLength h b >= norm_length+1))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1) 
    /\ v (getValue h1 b 0) = v r0 /\ v (getValue h1 b 1) = v r1 /\ v (getValue h1 b 2) = v r2
    /\ v (getValue h1 b 3) = v r3 /\ v (getValue h1 b 4) = v r4 /\ v (getValue h1 b 5) = v r5
    /\ v (getValue h1 b 6) = v r6 /\ v (getValue h1 b 7) = v r7 /\ v (getValue h1 b 8) = v r8 ))
let full_update b r0 r1 r2 r3 r4 r5 r6 r7 r8 =    
  let h0 = ST.get() in
  upd_wide b 0 r0;
  let h1 = ST.get() in
  upd_lemma h0 h1 b 0 r0;
  upd_wide b 1 r1;
  let h2 = ST.get() in
  upd_lemma h1 h2 b 1 r1;
  upd_wide b 2 r2; 
  let h3 = ST.get() in
  upd_lemma h2 h3 b 2 r2;
  upd_wide b 3 r3; 
  let h4 = ST.get() in
  upd_lemma h3 h4 b 3 r3;
  upd_wide b 4 r4;
  let h5 = ST.get() in
  upd_lemma h4 h5 b 4 r4;
  upd_wide b 5 r5; 
  let h6 = ST.get() in
  upd_lemma h5 h6 b 5 r5;
  upd_wide b 6 r6;
  let h7 = ST.get() in
  upd_lemma h6 h7 b 6 r6;
  upd_wide b 7 r7; 
  let h8 = ST.get() in
  upd_lemma h7 h8 b 7 r7;
  upd_wide b 8 r8;
  let h9 = ST.get() in
  upd_lemma h8 h9 b 8 r8

type Carried3 h1 (b:bigint_wide) = 
  live h1 b /\ getLength h1 b >= norm_length+1
  /\ v (getValue h1 b 0) < pow2 56 /\ v (getValue h1 b 1) < pow2 56
  /\ v (getValue h1 b 2) < pow2 56 /\ v (getValue h1 b 3) < pow2 56
  /\ v (getValue h1 b 4) < pow2 56 /\ v (getValue h1 b 5) < pow2 56
  /\ v (getValue h1 b 7) < pow2 56 /\ v (getValue h1 b 6) < pow2 56
  /\ v (getValue h1 b 8) < 2
  /\ (v (getValue h1 b 8) = 1 ==> ( v (getValue h1 b 5) < pow2 18
		    /\ v (getValue h1 b 6) < 2
		    /\ v (getValue h1 b 7) < 2 ))

val carry2: b:bigint_wide -> ST unit
  (requires (fun h -> Carried2 h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1)
    /\ Carried3 h1 b
    /\ eval h1 b (norm_length+1) = eval h0 b norm_length
    /\ modifies !{getRef b} h0 h1))
let carry2 b = 
  admit(); // Timeout
  let h0 = ST.get() in
  let b0 = index_wide b 0 in
  let b1 = index_wide b 1 in
  let b2 = index_wide b 2 in
  let b3 = index_wide b 3 in
  let b4 = index_wide b 4 in
  let b5 = index_wide b 5 in
  let b6 = index_wide b 6 in
  let b7 = index_wide b 7 in
  let r0 = trim_2_56 b0 in
  let c1 = b0 |>> 56 in
  lemma_helper_10 b0 73;
  cut (True /\ v c1 < pow2 17); 
  lemma_helper_7 b1 c1;
  let d1 = b1 |+ c1 in 
  let r1 = trim_2_56 d1 in
  cut (True /\ v r1 < pow2 56);
  let c2 = d1 |>> 56 in
  lemma_helper_10 d1 57;
  lemma_helper_12 b1 c1 17;
  cut (v c2 < 2 /\ (v c2 = 1 ==> v r1 < pow2 17)); 
  lemma_helper_11 b2 c2; 
  let d2 = b2 |+ c2 in 
  let r2 = trim_2_56 d2 in
  cut (True /\ v r2 < pow2 56);
  let c3 = d2 |>> 56 in
  lemma_helper_10 d2 57;
  lemma_helper_12 b2 c2 1;
  cut (v c3 < 2 /\ (v c3 = 1 ==> v r2 < 2)); 
  lemma_helper_11 b3 c3; 
  let d3 = b3 |+ c3 in
  let r3 = trim_2_56 d3 in
  cut (True /\ v r3 < pow2 56);
  let c4 = d3 |>> 56 in 
  lemma_helper_10 d3 57;
  lemma_helper_12 b3 c3 1;
  cut (v c4 < 2 /\ (v c4 = 1 ==> v r3 < 2));
  lemma_helper_8 b4 c4;
  let d4 = b4 |+ c4 in
  let r4 = trim_2_56 d4 in
  cut (True /\ v r4 < pow2 56);
  let c5 = d4 |>> 56 in 
  lemma_helper_10 d4 74;
  cut (True /\ v c5 < pow2 18); 
  lemma_helper_9 b5 c5; 
  let d5 = b5 |+ c5 in 
  let r5 = trim_2_56 d5 in
  cut (True /\ v r5 < pow2 56);
  let c6 = d5 |>> 56 in 
  lemma_helper_10 d5 57;
  lemma_helper_12 b5 c5 18;
  cut (v c6 < 2 /\ (v c6 = 1 ==> v r5 < pow2 18)); 
  lemma_helper_11 b6 c6;
  let d6 = b6 |+ c6 in
  let r6 = trim_2_56 d6 in
  cut (True /\ v r6 < pow2 56);
  let c7 = d6 |>> 56 in
  lemma_helper_10 d6 57;
  lemma_helper_12 b6 c6 1;
  cut (v c7 < 2 /\ (v c7 = 1 ==> (v r6 < 2 /\ v c6 = 1))); 
  lemma_helper_11 b7 c7; 
  let d7 = b7 |+ c7 in 
  let r7 = trim_2_56 d7 in
  cut (True /\ v r7 < pow2 56);
  let c8 = d7 |>> 56 in 
  lemma_helper_10 d7 57;
  lemma_helper_12 b7 c7 1;
  cut (v c8 = 1 ==> v r7 < 2);
  cut (v c8 = 1 ==> (v r7 < 2 /\ v c7 = 1)); 
  cut (v c8 = 1 ==> (v r7 < 2 /\ v r6 < 2 /\ v r5 < pow2 18)); 
  full_update b r0 r1 r2 r3 r4 r5 r6 r7 c8

val lemma_helper_13: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 56 /\ v y < 2))
  (ensures (v x + v y < pow2 platform_wide /\ v x + v y < pow2 57))
let lemma_helper_13 x y = 
  pow2_increases_lemma platform_wide 57

type Carried4 h1 (b:bigint_wide) = 
  live h1 b /\ getLength h1 b >= norm_length+1
  /\ v (getValue h1 b 0) < pow2 57 /\ v (getValue h1 b 1) < pow2 56
  /\ v (getValue h1 b 2) < pow2 56 /\ v (getValue h1 b 3) < pow2 56
  /\ v (getValue h1 b 4) < pow2 57 /\ v (getValue h1 b 5) < pow2 56
  /\ v (getValue h1 b 6) < pow2 56 /\ v (getValue h1 b 7) < pow2 56
  /\ ((v (getValue h1 b 0) >= pow2 56 \/ v (getValue h1 b 4) >= pow2 56)
      ==> (v (getValue h1 b 5) < pow2 18 /\ v (getValue h1 b 6) < 2 /\ v (getValue h1 b 7) < 2))

val carry2_top_to_0: b:bigint_wide -> ST unit 
    (requires (fun h -> Carried3 h b))
    (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1)
      /\ Carried4 h1 b
      /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
      ))
let carry2_top_to_0 b =
  //@@
  let h0 = ST.get() in
  let btop = index_wide b 8 in
  let b0 = index_wide b 0 in
  let b4 = index_wide b 4 in
  lemma_helper_13 b0 btop;
  lemma_helper_13 b4 btop;
  upd_wide b 0 (b0 |+ btop);
  upd_wide b 4 (b4 |+ btop);
  let h1 = ST.get() in
  freduce_degree_lemma_0 h0 h1 b 0

val lemma_helper_14: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 57 /\ v y < 2))
  (ensures (v x + v y < pow2 128 /\ v x + v y < pow2 58))
let lemma_helper_14 x y = pow2_increases_lemma 128 58

val lemma_helper_15: x:wide -> Lemma
  (requires (True))
  (ensures (v x / pow2 56 > 0 ==> v x >= pow2 56))
let lemma_helper_15 x =
  //@@
  ()

val lemma_helper_16: x:wide -> y:wide -> Lemma
  (requires (True))
  (ensures ((v x < pow2 18 /\ v y < pow2 2) ==> (v x + v y < pow2 128 /\ v x + v y < pow2 56)))
let lemma_helper_16 x y = 
  //@@
  pow2_increases_lemma 128 19; pow2_increases_lemma 56 19

val full_update2: b:bigint_wide -> r0:wide{v r0 < pow2 56} -> r1:wide{v r1 < pow2 56} -> 
  r2:wide{v r2 < pow2 56} -> r3:wide{v r3 < pow2 56} -> r4:wide{v r4 < pow2 56} -> 
  r5:wide{v r5 < pow2 56} -> ST unit
  (requires (fun h -> live h b /\ getLength h b >= norm_length+1
    /\ v (getValue h b 6) < pow2 56 /\ v (getValue h b 7) < pow2 56))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1) 
    /\ v (getValue h1 b 0) = v r0 /\ v (getValue h1 b 1) = v r1 /\ v (getValue h1 b 2) = v r2
    /\ v (getValue h1 b 3) = v r3 /\ v (getValue h1 b 4) = v r4 /\ v (getValue h1 b 5) = v r5
    /\ v (getValue h1 b 6) = v (getValue h0 b 6)
    /\ v (getValue h1 b 7) = v (getValue h0 b 7)
    /\ Standardized h1 b))
let full_update2 b r0 r1 r2 r3 r4 r5 =    
  //@@
  let h0 = ST.get() in
  upd_wide b 0 r0;
  let h1 = ST.get() in
  upd_lemma h0 h1 b 0 r0;
  upd_wide b 1 r1;
  let h2 = ST.get() in
  upd_lemma h1 h2 b 1 r1;
  upd_wide b 2 r2; 
  let h3 = ST.get() in
  upd_lemma h2 h3 b 2 r2;
  upd_wide b 3 r3; 
  let h4 = ST.get() in
  upd_lemma h3 h4 b 3 r3;
  upd_wide b 4 r4;
  let h5 = ST.get() in
  upd_lemma h4 h5 b 4 r4;
  upd_wide b 5 r5; 
  let h6 = ST.get() in
  upd_lemma h5 h6 b 5 r5

val carry3: b:bigint_wide -> ST unit
  (requires (fun h -> Carried4 h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1)
    /\ Standardized h1 b
    /\ eval h1 b norm_length = eval h0 b norm_length
    ))
let carry3 b =
//  admit(); Partial functional correctness
  let h0 = ST.get() in
  let b0 = index_wide b 0 in
  let b1 = index_wide b 1 in
  let b2 = index_wide b 2 in
  let b3 = index_wide b 3 in
  let b4 = index_wide b 4 in
  let b5 = index_wide b 5 in
  let r0 = trim_2_56 b0 in
  let c1 = b0 |>> 56 in
  lemma_helper_10 b0 57;
  cut (v c1 = 1 ==> v b5 < pow2 18);  
  lemma_helper_7 b1 c1;
  let d1 = b1 |+ c1 in 
  let r1 = trim_2_56 d1 in
  let c2 = d1 |>> 56 in
  cut (v c2 = 1 ==> v b5 < pow2 18);
  lemma_helper_10 d1 57;
  lemma_helper_12 b1 c1 17;
  lemma_helper_11 b2 c2; 
  let d2 = b2 |+ c2 in 
  let r2 = trim_2_56 d2 in
  let c3 = d2 |>> 56 in
  cut (v c3 = 1 ==> v b5 < pow2 18); 
  lemma_helper_10 d2 57;
  lemma_helper_12 b2 c2 1;
  lemma_helper_11 b3 c3; 
  let d3 = b3 |+ c3 in
  let r3 = trim_2_56 d3 in
  cut (True /\ v r3 < pow2 56);
  let c4 = d3 |>> 56 in 
  cut (v c4 = 1 ==> v b5 < pow2 18); 
  lemma_helper_10 d3 57;
  lemma_helper_12 b3 c3 1; 
  lemma_helper_14 b4 c4; 
  let d4 = b4 |+ c4 in
  let r4 = trim_2_56 d4 in
  let c5 = d4 |>> 56 in 
  lemma_helper_10 d4 58;
  lemma_helper_15 d4;
  cut (v d4 >= pow2 56 ==> (v c4 = 1 \/ v b4 >= pow2 56)); 
  cut ((v c4 = 1 ==> v b5 < pow2 18) /\ (v b4 >= pow2 56 ==> v b5 < pow2 18)); 
  cut (v d4 >= pow2 56 ==> v b5 < pow2 18);   
  cut (v c5 > 0 ==> (v b5 < pow2 18 /\ v c5 < pow2 2)); 
  lemma_helper_16 b5 c5; 
  let d5 = b5 |+ c5 in 
  full_update2 b r0 r1 r2 r3 r4 d5;
  let h1 = ST.get() in
  (* P448 = 2^448 - 2^224 - 1, hence *)
  (*   a[0] + 2^56*a[1] + 2^112*a[2] + 2^168*a[3] + 2^224*a[4]  *)
  (*           + 2^280*a[5] + 2^336*a[6] + 2^392*a[7] + 2^448*a[8] *)
  (* = (a[0]+a[8]) + 2^56*a[1] + 2^112*a[2] + 2^168*a[3] + 2^224*(a[4]+a[8]) *)
  (* 		    + 2^280*a[5] + 2^336*a[6] + 2^392*a[7]  *)
  admitP (True /\ eval h1 b norm_length = eval h0 b norm_length)

#reset-options

val lemma_helper_4: x:wide -> y:wide -> Lemma
  (requires (v x < pow2 (platform_wide - 3) /\ v y < pow2 (platform_wide - 3)))
  (ensures (v x + v y < pow2 (platform_wide - 2) /\ v x < pow2 (platform_wide - 2)))
  [SMTPat (v x); SMTPat (v y)]
let lemma_helper_4 x y = ()

#reset-options

val lemma_helper_5: h0:heap -> h1:heap -> b:bigint_wide -> Lemma
  (requires (Reducible h0 b /\ Reduced h0 h1 b))
  (ensures (Reducible2 h1 b))
let lemma_helper_5 h0 h1 b = 
  //@@
  ()

val upd_lemma_2: h0:heap -> h1:heap -> b:bigint_wide -> idx:nat -> x:wide -> Lemma
  (requires (Updated h0 h1 b (norm_length+1) /\ idx < getLength h1 b /\ h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx x)))
  (ensures (live h1 b /\ live h0 b /\ Updated h0 h1 b (norm_length+1) /\ idx < getLength h1 b 
	    /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i <> idx /\ i < getLength h1 b) ==> v (getValue h1 b i) = v (getValue h0 b i))
	    /\ eval h1 b idx = eval h0 b idx))
let upd_lemma_2 h0 h1 b idx x = 
  //@@
  eval_eq_lemma h0 h1 b b idx

val upd_lemma_3: h0:heap -> h1:heap -> h2:heap -> b:bigint_wide -> idx:nat -> x:wide -> Lemma
  (requires (Updated h0 h1 b (2*norm_length-1) /\ Updated h1 h2 b (2*norm_length-1) 
    /\ Reduced2 h0 h1 b
    /\ (forall (i:nat). {:pattern (v (getValue h2 b i))} i < norm_length ==> v (getValue h2 b i) = v (getValue h1 b i)) ))
  (ensures (Reduced2 h0 h2 b))
let upd_lemma_3 h0 h1 h2 b idx x = 
  //@@
  () 

val freduce_degree: b:bigint_wide -> ST unit
  (requires (fun h -> Reducible h b))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (2*norm_length-1)
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime
    /\ Carriable h1 b 0))
let freduce_degree b =
  //@@
  let h0 = ST.get() in
  freduce_degree_1 b;
  let h1 = ST.get() in
  lemma_helper_5 h0 h1 b; 
  freduce_degree_2 b;
  let h2 = ST.get() in
  cut (Reduced2 h1 h2 b);
  cut (True /\ eval h2 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime);
  upd_wide b 8 zero_wide;
  let h3 = ST.get() in 
  upd_lemma_2 h2 h3 b norm_length zero_wide; 
  upd_lemma_3 h1 h2 h3 b norm_length zero_wide; 
  freduce_lemma_0 h0 h1 h3 b

#reset-options

val freduce_coefficients: b:bigint_wide -> ST unit
  (requires (fun h -> Carriable h b 0))
  (ensures (fun h0 _ h1 -> Updated h0 h1 b (norm_length+1)
    /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime
    /\ Standardized h1 b))
let freduce_coefficients b =
  //@@
  let h0 = ST.get() in
  upd_wide b norm_length zero_wide; (* Unnecessary, to remove *)
  let h1 = ST.get() in
  eval_eq_lemma h0 h1 b b norm_length; 
  cut (True /\ eval h1 b (norm_length+1) = eval h1 b norm_length); 
  carry b 0; 
  carry_top_to_0 b; 
  let h2 = ST.get() in
  upd_wide b norm_length zero_wide; 
  let h3 = ST.get() in
  eval_eq_lemma h2 h3 b b norm_length;
  carry2 b; 
  carry2_top_to_0 b;
  carry3 b

(* Not verified *)
val normalize:
  b:bigint -> ST unit 
  (requires (fun h -> Standardized h b))
  (ensures (fun h0 _ h1 -> Standardized h0 b /\ Standardized h1 b
    /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime))
let normalize b =
  admit(); // Not machine checked
  let two56m1 = to_limb "0xffffffffffffff" in
  let two56m2 = to_limb "0xfffffffffffffe" in  
  let b7 = index_limb b 7 in
  let b6 = index_limb b 6 in
  let b5 = index_limb b 5 in
  let b4 = index_limb b 4 in
  let b3 = index_limb b 3 in
  let b2 = index_limb b 2 in
  let b1 = index_limb b 1 in
  let b0 = index_limb b 0 in
  let mask = eq_limb b7 two56m1 in
  let mask = log_and_limb mask (eq_limb b6 two56m1) in
  let mask = log_and_limb mask (eq_limb b5 two56m1) in
  (* Case where b == 2^448-2^224-1 *)
  let mask1 = log_and_limb mask (eq_limb b4 two56m2) in
  let mask1 = log_and_limb mask1 (eq_limb b3 two56m1) in
  let mask1 = log_and_limb mask1 (eq_limb b2 two56m1) in
  let mask1 = log_and_limb mask1 (eq_limb b1 two56m1) in
  let mask1 = log_and_limb mask1 (eq_limb b0 two56m1) in
  (* Case where b >= 2^448-2^224-1 && b < 2^448 *)
  let mask2 = log_and_limb mask (eq_limb b4 two56m1) in
  let mask = log_or_limb mask1 mask2 in
  let mask' = log_not_limb mask in // 0xfff... if mask == 0 , 0 else
  upd_limb b 7 (log_and_limb b7 mask'); // if b >= 2^448-2^224-1 then 0
  upd_limb b 6 (log_and_limb b6 mask'); // if b >= 2^448-2^224-1 then 0
  upd_limb b 5 (log_and_limb b5 mask'); // if b >= 2^448-2^224-1 then 0
  let b4' = log_and_limb (log_xor_limb b4 (to_limb "0x1")) (to_limb "0x1") in
  // if b > 2^448-2^224-1 then 0 else 1
  upd_limb b 4  (log_or_limb (log_and_limb b4' mask) (log_and_limb b4 mask'));
  // if b >= 2^448-2^224-1 then add 1
  upd_limb b 0  (add_limb b0 (log_and_limb mask one_limb));
  // Carry
  let mask3 = (to_limb "0xffffffffffffff") in
  let b0 = index_limb b 0 in let r0 = log_and_limb b0 mask3 in
  upd_limb b 0 (r0); 
  let c = shift_right_limb b0 56 in
  let b1 = index_limb b 1 in
  upd_limb b 1 (add_limb b1 c);
  let b1 = index_limb b 1 in let r1 = log_and_limb b1 mask3 in
  upd_limb b 1 (r1); 
  let c = shift_right_limb b1 56 in
  let b2 = index_limb b 2 in
  upd_limb b 2 (add_limb b2 c);
  let b2 = index_limb b 2 in let r2 = log_and_limb b2 mask3 in
  upd_limb b 2 (r2); 
  let c = shift_right_limb b2 56 in
  let b3 = index_limb b 3 in
  upd_limb b 3 (add_limb b3 c);
  let b3 = index_limb b 3 in let r3 = log_and_limb b3 mask3 in
  upd_limb b 3 (r3); 
  let c = shift_right_limb b3 56 in
  let b4 = index_limb b 4 in
  upd_limb b 4 (add_limb b4 c);
  let b4 = index_limb b 4 in
  upd_limb b 4 (log_or_limb (log_and_limb (log_and_limb one_limb b4) mask) (log_and_limb b4 mask'))

type Fits_2_57 h (b:bigint) =
  live h b /\ getLength h b >= norm_length
  /\ v (getValue h b 0) < pow2 57  /\ v (getValue h b 1) < pow2 57
  /\ v (getValue h b 2) < pow2 57  /\ v (getValue h b 3) < pow2 57
  /\ v (getValue h b 4) < pow2 57  /\ v (getValue h b 5) < pow2 57
  /\ v (getValue h b 6) < pow2 57  /\ v (getValue h b 7) < pow2 57

val lemmma_bigzero_0: unit -> Lemma (pow2 57 - 2 > pow2 56 /\ pow2 57 - 4 > pow2 56 /\ pow2 57 + pow2 56 < pow2 64)
let lemmma_bigzero_0 () = 
  pow2_double_sum 56;
  pow2_double_sum 57;
  pow2_increases_lemma 64 58;
  pow2_increases_lemma 57 1;
  pow2_increases_lemma 57 2;
  pow2_increases_lemma 56 1;
  pow2_increases_lemma 56 2

let add_big_zero b =
  admit(); // Must reduce timeout
  let h0 = ST.get() in
  let two57m2 = to_limb "0x1fffffffffffffe" in // 2^57 - 2
  let two57m4 = to_limb "0x1fffffffffffffc" in // 2^56 - 4
  admitP (v two57m2 = pow2 57 - 2 /\ v two57m4 = pow2 57 -4);
  lemmma_bigzero_0 ();
  let b0 = index_limb b 0 in
  let b1 = index_limb b 1 in
  let b2 = index_limb b 2 in
  let b3 = index_limb b 3 in
  let b4 = index_limb b 4 in
  let b5 = index_limb b 5 in
  let b6 = index_limb b 6 in
  let b7 = index_limb b 7 in
  upd_limb b 0 (add_limb b0 two57m2);
  upd_limb b 1 (add_limb b1 two57m2); 
  upd_limb b 2 (add_limb b2 two57m2); 
  upd_limb b 3 (add_limb b3 two57m2); 
  upd_limb b 4 (add_limb b4 two57m4);
  upd_limb b 5 (add_limb b5 two57m2);
  upd_limb b 6 (add_limb b6 two57m2); 
  upd_limb b 7 (add_limb b7 two57m2);
  let h1 = ST.get() in
  admitP(True /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime)
