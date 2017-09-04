(*--build-config
    options:--admit_fsi FStar.Set --verify_module Modulo --z3rlimit 100;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters_25519_64.fst uint.fst bigint.fst eval.fst modulo_lemmas.fst modulo.fsti
  --*)

module Modulo

(* 64/128 bits *)

open IntLib
open Parameters
open UInt
open FStar.Heap
open FStar.Ghost
open Bigint
open Eval

let op_Bar_Amp x y = log_and_wide x y
let op_Bar_Greater_Greater x y = shift_right_wide x y
let op_Bar_Less_Less x y = shift_left_wide x y
let op_Bar_Plus x y = add_wide x y
let op_Bar_Star x y = mul_wide x y

assume val prime_modulo_lemma: unit -> Lemma (pow2 255 % (reveal prime) = 19)

assume val modulo_lemma: a:nat -> b:pos -> 
  Lemma
    (requires (a < b))
    (ensures (a % b = a))
    [SMTPat (a % b)]

val pow2_4_lemma: unit -> 
  Lemma
    (requires (True))
    (ensures (pow2 4 = 16))
    [SMTPat (pow2 4)]
let pow2_4_lemma () = 
  //@@
  ()

val pow2_5_lemma: unit -> 
  Lemma
    (requires (True))
    (ensures (pow2 5 = 32))
    [SMTPat (pow2 5)]
let pow2_5_lemma () = 
  //@@
  ()

let satisfies_modulo_constraints h b =
  getLength h b >= 2*norm_length-1
  && getTemplate b = templ && maxValue h b * 20 < pow2 (platform_wide - 1)

type SatisfiesModuloConstraints (h:heap) (b:bigint_wide) = live h b /\ satisfies_modulo_constraints h b

val times_19: x:wide{19 * v x < pow2 platform_wide} -> Tot (y:wide{v y = 19 * v x})
let times_19 x =
  let y = x |<< 4 in
  let z = x |<< 1 in
  x |+ y |+ z

opaque type Reducible (h:heap) (b:bigint_wide) (ctr:nat) =
  live h b /\ getLength h b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (getValue h b (i+norm_length))}
      (i >= ctr /\ i < norm_length-1) ==> v (getValue h b i) + 19 * v (getValue h b (i+norm_length)) < pow2 platform_wide)

opaque type Reducible' (h:heap) (b:bigint_wide) (ctr:nat{ctr < norm_length-1}) =
  live h b /\ getLength h b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (getValue h b (i+norm_length))}
      i <= ctr ==> v (getValue h b i) + 19 * v (getValue h b (i+norm_length)) < pow2 platform_wide)

opaque type Times19 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ getLength h0 b >= 2*norm_length-1 /\ getLength h1 b = getLength h0 b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
       (i >= ctr /\ i < norm_length - 1) ==> v (getValue h1 b i) = v (getValue h0 b i) + 19 * (v (getValue h0 b (i+norm_length))))

opaque type Times19' (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat{ctr < norm_length - 1}) =
  live h0 b /\ live h1 b /\ getLength h0 b >= 2*norm_length-1 /\ getLength h1 b = getLength h0 b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
       i <= ctr ==> v (getValue h1 b i) = v (getValue h0 b i) + 19 * (v (getValue h0 b (i+norm_length))))

opaque type Untouched (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ getLength h0 b >= 2*norm_length-1 /\ getLength h1 b = getLength h0 b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
      ((i < ctr \/ i >= norm_length-1) /\ i < 2*norm_length-1) ==> v (getValue h0 b i) = v (getValue h1 b i))

opaque type Untouched' (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) = 
  live h0 b /\ live h1 b /\ getLength h0 b >= 2*norm_length-1 /\ getLength h1 b = getLength h0 b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)} (i > ctr /\ i < 2*norm_length-1) ==> 
      v (getValue h0 b i) = v (getValue h1 b i))

#reset-options

(* val helper_lemma_00: ctr:nat{ctr >= 2} -> Lemma *)
(*   (requires (True)) *)
(*   (ensures (bitweight templ (ctr+norm_length-2) = bitweight templ (ctr-2) + bitweight templ *)

(* val lemma_helper_0: ctr:nat{ctr >= 2} -> Lemma *)
(*   (requires (True)) *)
(*   (ensures (pow2 (bitweight templ (ctr+norm_length-2)) = pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length))) *)
(* let lemma_helper_0 ctr =  *)
(*   bitweight_definition templ (ctr+norm_length *)

val lemma_helper_00: ctr:nat{ctr>=2} -> Lemma (ctr-1+norm_length = ctr+norm_length-1 
					   /\ ctr+norm_length-1 = (ctr-1) + norm_length
					   /\ (ctr+norm_length-1)-1=ctr+norm_length-2)
let lemma_helper_00 ctr = ()					   

val lemma_helper_01: ctr:nat{ctr>=2} -> Lemma 
  (bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 51)
let lemma_helper_01 ctr = 
  bitweight_definition templ (ctr+norm_length-2)

val lemma_helper_02: a:nat -> b:nat -> Lemma (bitweight templ (a+b) = bitweight templ a + bitweight templ b)
let rec lemma_helper_02 a b = match a with | 0 -> () | _ -> lemma_helper_02 (a-1) b

val lemma_helper_03: ctr:nat{ctr>=2} -> Lemma (pow2 51 * pow2 (bitweight templ (ctr-2)) = pow2 (bitweight templ (ctr-1)))
let lemma_helper_03 ctr = 
  bitweight_definition templ 1;
  lemma_helper_02 1 (ctr-2); 
  Lemmas.pow2_exp_1 51 (bitweight templ (ctr-2))

val lemma_helper_04: ctr:nat{ctr>=2} -> Lemma
  (requires (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 51 * pow2 (bitweight templ (ctr+norm_length-2))))
  (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let lemma_helper_04 ctr =
  //@@
  lemma_helper_02 (ctr-2) norm_length;
  Lemmas.pow2_exp_1 (bitweight templ (ctr-2)) (bitweight templ norm_length); 
  Axiomatic.paren_mul_right (pow2 51) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
  lemma_helper_03 ctr

val pow2_bitweight_lemma_1: ctr:pos -> 
  Lemma
    (requires (True))
    (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let rec pow2_bitweight_lemma_1 ctr =
  //@@
  match ctr with
  | 1 -> ()
  | _ -> 
    lemma_helper_00 ctr;
    pow2_bitweight_lemma_1 (ctr-1);
    lemma_helper_01 ctr;
    bitweight_definition templ (ctr+norm_length-2);
    Lemmas.pow2_exp_1 51 (bitweight templ (ctr+norm_length-2)); 
    lemma_helper_04 ctr

#reset-options

val bitweight_norm_length_lemma: unit ->
  Lemma (requires (True))
	(ensures (bitweight templ norm_length = 255))
	[SMTPat (bitweight templ norm_length)]
let bitweight_norm_length_lemma () = 
  //@@
  bitweight_definition templ (norm_length-1);
  bitweight_definition templ (norm_length-2);
  bitweight_definition templ (norm_length-3);
  bitweight_definition templ (norm_length-4);
  bitweight_definition templ (norm_length-5)
  
#reset-options

val lemma_helper_10: h0:heap -> b:bigint_wide{live h0 b (* /\ getLength h0 b >= 2*norm_length-1 *)} -> ctr:pos{getLength h0 b >= ctr+norm_length+1 /\ ctr < norm_length-1} -> Lemma
  ( ctr+norm_length = norm_length+ctr 
    /\ (norm_length+1+ctr)-1 = norm_length + ctr 
    /\ norm_length+ctr = (ctr+1)+norm_length-1 
    /\ eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length))
let lemma_helper_10 h0 b ctr = 
  //@@
  eval_definition h0 b (norm_length+1+ctr)

val lemma_helper_12: a:int -> b:int -> c:int -> Lemma (a * b * c = b * (a * c))
let lemma_helper_12 a b c = ()

val lemma_helper_11: h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b /\ (* getLength h0 b >= 2 * norm_length - 1 /\ *) getLength h0 b = getLength h1 b} -> ctr:pos{getLength h0 b >= ctr + norm_length + 1 /\ctr < norm_length-1} -> prime:pos -> 
  GLemma unit
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))} (i < getLength h0 b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i))
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
      /\ eval h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime
      /\ eval h0 b (norm_length+ctr) - eval h0 b (ctr+1) = eval h1 b (norm_length+ctr) - eval h1 b (ctr+1)
      /\ eval h0 b ctr = eval h1 b ctr))
    (ensures (eval h0 b (norm_length+1+ctr) % (prime) = eval h1 b (norm_length+ctr) % (prime))) []
let lemma_helper_11 h0 h1 b ctr prime = 
  //@@
  eval_definition h0 b (norm_length+1+ctr);
  Axiomatic.distributivity_add_right (pow2 (bitweight templ ctr)) (v (getValue h0 b ctr)) (19 * v (getValue h0 b (norm_length+ctr)));
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  lemma_helper_12 19 (pow2 (bitweight templ ctr)) (v (getValue h0 b (norm_length+ctr))); 
  cut (True /\ 19 * v (getValue h0 b (ctr+norm_length)) = v (getValue h1 b ctr) - v (getValue h0 b ctr));
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * (v (getValue h1 b ctr) - v (getValue h0 b ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  Axiomatic.distributivity_sub_right (pow2 (bitweight templ ctr)) (v (getValue h1 b ctr)) (v (getValue h0 b ctr));
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * v (getValue h1 b ctr) - pow2 (bitweight templ ctr) * v (getValue h0 b ctr) + eval h0 b (norm_length+ctr)) % prime); 
  eval_definition h0 b (ctr+1);
  eval_definition h1 b (ctr+1);
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * v (getValue h1 b ctr) - pow2 (bitweight templ ctr) * v (getValue h0 b ctr) + eval h1 b (norm_length+ctr) - eval h1 b (ctr+1) + eval h0 b (ctr+1)) % prime);
  ()

opaque val freduce_degree_lemma_2:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b (* /\ getLength h0 b >= 2 * norm_length - 1 *) /\ getLength h0 b = getLength h1 b} -> 
  ctr:pos{getLength h0 b >= ctr + norm_length + 1 /\ ctr < norm_length-1} ->
  GLemma unit
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))}
	(i < getLength h0 b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i)) 
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
    ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
    []
let freduce_degree_lemma_2 h0 h1 b ctr = 
  //@@
  let prime = reveal prime in
  eval_definition h0 b (norm_length+1+ctr); 
  (* cut (ctr+norm_length = norm_length+ctr /\ (norm_length+1+ctr)-1 = norm_length + ctr /\ norm_length+ctr = (ctr+1)+norm_length-1); *)
  (* cut (True /\ eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length));  *)
  lemma_helper_10 h0 b ctr;
  pow2_bitweight_lemma_1 (ctr+1); 
  lemma_helper_02 norm_length ctr;
  bitweight_norm_length_lemma (); 
  Lemmas.pow2_exp_1 255 (bitweight templ ctr);
  (* cut(True /\ pow2 (bitweight templ (norm_length+ctr)) = pow2 255 * pow2 (bitweight templ ctr));  *)
  Axiomatic.paren_mul_left (pow2 255) (pow2 (bitweight templ ctr)) (v (getValue h0 b (norm_length+ctr))); 
  Axiomatic.paren_mul_right (pow2 255) (pow2 (bitweight templ ctr)) (v (getValue h0 b (norm_length+ctr))); 
  cut (True /\ eval h0 b (norm_length+1+ctr) = (pow2 255 * pow2 (bitweight templ ctr)) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr));
  ModuloLemmas.helper_lemma_5 (pow2 255) (pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr))) (eval h0 b (norm_length+ctr)) prime; 
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = ((pow2 255 % prime) * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  prime_modulo_lemma (); 
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  eval_eq_lemma h0 h1 b b ctr; 
  eval_definition h0 b (ctr+1);
  eval_definition h1 b (ctr+1);
  (* cut (True /\ eval h0 b (ctr+1) = pow2 (bitweight templ ctr) * v (getValue h0 b ctr) + eval h0 b ctr); *)
  (* cut (True /\ eval h1 b (ctr+1) = pow2 (bitweight templ ctr) * (v (getValue h0 b ctr) + 19 * v (getValue h0 b (norm_length+ctr))) + eval h0 b ctr);  *)
  Axiomatic.distributivity_add_right (pow2 (bitweight templ ctr)) (v (getValue h0 b ctr)) (19 * v (getValue h0 b (norm_length+ctr))); 
  eval_partial_eq_lemma h0 h1 b b (ctr+1) (norm_length+ctr);
  lemma_helper_11 h0 h1 b ctr prime

#reset-options

opaque val gfreduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b (* /\ getLength h0 b >= 2 * norm_length - 1 *) /\ getLength h0 b = getLength h1 b} -> 
  ctr:nat{getLength h0 b >= ctr+norm_length+1 /\ ctr < norm_length-1} ->
  GLemma unit
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))}
	(i < getLength h0 b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i)) 
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
    ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
    []
let gfreduce_degree_lemma h0 h1 b ctr =
  //@@
  let prime = reveal prime in
  if ctr = 0 then (
    eval_definition h0 b (norm_length+1);
    assert(eval h0 b (norm_length+1) = pow2 (bitweight templ norm_length) * v (getValue h0 b norm_length) + eval h0 b norm_length); 
    assert(eval h0 b (norm_length+1) = pow2 255 * v (getValue h0 b norm_length) + eval h0 b norm_length);
    ModuloLemmas.helper_lemma_5 (pow2 255) (v (getValue h0 b norm_length)) (eval h0 b norm_length) prime;
    assert(eval h0 b (norm_length+1) % prime = ((pow2 255 % prime) * v (getValue h0 b norm_length) + eval h0 b norm_length) % prime); 
    prime_modulo_lemma ();
    assert(eval h0 b (norm_length+1) % prime = (19 * v (getValue h0 b norm_length) + eval h0 b norm_length) % prime);
    cut(eval h0 b 1 = v (getValue h0 b 0) /\ eval h1 b 1 = v (getValue h0 b 0) + 19 * v (getValue h0 b norm_length)); 
    eval_partial_eq_lemma h0 h1 b b 1 norm_length;
    cut(True /\ eval h1 b norm_length - eval h1 b 1 = eval h0 b norm_length - eval h0 b 1)
  ) else (
    freduce_degree_lemma_2 h0 h1 b ctr
  )

val freduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b /\ (* getLength h0 b >= 2 * norm_length - 1 /\ *) getLength h0 b = getLength h1 b} -> 
  ctr:nat{getLength h0 b >= ctr+norm_length+1 /\ ctr < norm_length-1} -> Lemma 
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))}
	(i < getLength h0 b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i)) 
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
    ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma h0 h1 b ctr = 
  coerce 
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))}
	(i < getLength h0 b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i)) 
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
    ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
    (fun _ -> gfreduce_degree_lemma h0 h1 b ctr)

#reset-options

val freduce_degree': 
  b:bigint_wide -> ctr:nat{ctr < norm_length - 1} -> 
  ST unit 
    (requires (fun h -> Reducible' h b ctr)) 
    (ensures (fun h0 _ h1 -> Untouched' h0 h1 b ctr /\ Times19' h0 h1 b ctr
      /\ eval h1 b (norm_length) % reveal prime = eval h0 b (norm_length+1+ctr) % reveal prime
      /\ modifies !{getRef b} h0 h1))
let rec freduce_degree' b ctr' =
  //@@
  let h0 = ST.get() in
  match ctr' with
  | 0 -> 
    let b5ctr = index_wide b (0+norm_length) in 
    let bctr = index_wide b 0 in
    let b5ctr = times_19 b5ctr in
    let bctr = bctr |+ b5ctr in 
    upd_wide b 0 bctr;
    let h1 = ST.get() in
    upd_lemma h0 h1 b 0 bctr;
    freduce_degree_lemma h0 h1 b 0;
    cut (True /\ eval h0 b (norm_length+1+0) % reveal prime = eval h1 b (norm_length+0) % reveal prime);
    cut (True /\ eval h0 b (norm_length+1) % reveal prime = eval h1 b (norm_length+0) % reveal prime)
  | _ -> 
    let ctr = ctr' in
    let b5ctr = index_wide b (ctr + norm_length) in 
    let bctr = index_wide b ctr in
    let b5ctr = times_19 b5ctr in
    let bctr = bctr |+ b5ctr in 
    upd_wide b ctr bctr;
    let h1 = ST.get() in
    upd_lemma h0 h1 b ctr bctr;
    freduce_degree_lemma h0 h1 b ctr; 
    cut (True /\ eval h0 b (norm_length+1+ctr) % reveal prime = eval h1 b (norm_length+ctr) % reveal prime);
    cut(Reducible' h1 b (ctr-1)); 
    freduce_degree' b (ctr-1); 
    let h2 = ST.get() in 
    cut (forall (i:nat). {:pattern (v (getValue h1 b i))} (i > ctr /\ i < 2*norm_length-1) ==>
	   v (getValue h1 b i) = v (getValue h0 b i)); 
    cut(Untouched' h0 h2 b ctr);
    cut (Times19' h0 h2 b ctr) 

#reset-options

val aux_lemma_4: h:heap -> b:bigint_wide -> Lemma
  (requires (live h b /\ satisfies_modulo_constraints h b))
  (ensures (Reducible' h b (norm_length-2)))
let aux_lemma_4 h b = 
  let max = maxValue h b in
  cut (forall (i:nat). {:pattern (v (getValue h b i))} i < getLength h b ==> v (getValue h b i) <= max); 
  Lemmas.pow2_increases_1 platform_wide (platform_wide-1)

val aux_lemma_5: h0:heap -> h1:heap -> b:bigint_wide -> Lemma
  (requires (live h0 b /\ satisfies_modulo_constraints h0 b /\ Times19' h0 h1 b (norm_length-2)
      /\ Untouched' h0 h1 b (norm_length-2)))
  (ensures (live h0 b /\ satisfies_modulo_constraints h0 b /\ Times19' h0 h1 b (norm_length-2)
    /\ (forall (i:nat). i <= norm_length ==> v (getValue h1 b i) < pow2 (platform_wide-1))))
let aux_lemma_5 h0 h1 b = 
  //@@
  let max = maxValue h0 b in
  cut (forall (i:nat). {:pattern (v (getValue h0 b i))} i < getLength h0 b ==> v (getValue h0 b i) <= max);
  cut (forall (i:nat). i < norm_length-1 ==> v (getValue h1 b i) = v (getValue h0 b i) + 19 * v (getValue h0 b (i+norm_length)) )

#reset-options

val freduce_degree: b:bigint_wide -> ST unit 
  (requires (fun h -> live h b /\ satisfies_modulo_constraints h b)) 
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ satisfies_modulo_constraints h0 b
    /\ getLength h0 b >= 2*norm_length - 1
    /\ getLength h1 b = getLength h0 b /\ modifies !{getRef b} h0 h1 /\ getLength h1 b >= norm_length+1
    /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i <= norm_length ==> 
	v (getValue h1 b i) < pow2 (platform_wide - 1))
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b = 
  let h0 = ST.get() in
  aux_lemma_4 h0 b; 
  freduce_degree' b (norm_length-2); 
  let h1 = ST.get() in
  aux_lemma_5 h0 h1 b

#reset-options

val pow2_bitweight_lemma: ctr:nat -> 
  Lemma
    (requires (True))
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr)))
let pow2_bitweight_lemma ctr =
  bitweight_definition templ ctr;
  Lemmas.pow2_exp_1 (bitweight templ ctr) (templ ctr)

#reset-options

opaque val geval_carry_lemma:
  ha:heap -> a:bigint_wide{live ha a /\ getLength ha a >= norm_length+1} -> 
  hb:heap -> b:bigint_wide{live hb b /\ getLength hb b >= norm_length+1} ->
  ctr:nat{ctr < norm_length} -> 
  GLemma unit
    (requires (
      v (getValue hb b ctr) = v (getValue ha a ctr) % pow2 (templ ctr)
      /\ v (getValue hb b (ctr+1)) = v (getValue ha a (ctr+1)) + v (getValue ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (getValue hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (getValue hb b i) = v (getValue ha a i))
    ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
  []

let geval_carry_lemma ha a hb b ctr =
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
  ModuloLemmas.helper_lemma_3 (eval ha a (norm_length+1)) (eval hb b (norm_length+1)) (eval ha a (ctr+2)) (eval hb b (ctr+2))

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
    (fun _ -> geval_carry_lemma ha a hb b ctr)

opaque val gauxiliary_lemma_1: bip1:wide -> c:wide -> 
  GLemma unit
    (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 51)))
    (ensures (v bip1 + v c < pow2 platform_wide))
    []
let gauxiliary_lemma_1 bip1 c =
  ModuloLemmas.helper_lemma_4 (v bip1) (v c) 51 platform_wide

opaque val auxiliary_lemma_1: bip1:wide -> c:wide -> 
  Lemma
    (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 51)))
    (ensures (v bip1 + v c < pow2 platform_wide))
let auxiliary_lemma_1 bip1 c =
  coerce
    (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 51)))
    (ensures (v bip1 + v c < pow2 platform_wide))
    (fun _ -> gauxiliary_lemma_1 bip1 c)

#reset-options

val mod_lemma_1: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let mod_lemma_1 a b = ()

#reset-options

// The encoding needs to depend on the bitwise encoding
val mod2_51: a:wide -> Tot (b:wide{v b = v a % pow2 51})
let mod2_51 a = 
  let mask = shift_left_wide one_wide 51 in
  cut (v mask = pow2 51 % pow2 platform_wide /\ pow2 51 >= 1); 
  Lemmas.pow2_increases_1 platform_wide 51; 
  mod_lemma_1 (pow2 51) (pow2 platform_wide);
  let mask = sub_wide mask one_wide in
  let res = a |& mask in
  log_and_wide_lemma_3 a mask 51;
  res

opaque type Carriable (h:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h b /\ getLength h b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h b i))}
      (i > ctr /\ i <= norm_length) ==> v (getValue h b i) < pow2 (platform_wide - 1))

opaque type Carried (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ getLength h1 b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i < ctr ==> v (getValue h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (getValue h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (getValue h1 b norm_length) < pow2 77)

opaque type Carried' (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ getLength h1 b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i >= ctr /\ i < norm_length) ==> v (getValue h1 b i) < pow2 (templ ctr))
  /\ v (getValue h1 b norm_length) < pow2 77

opaque type Untouched_2 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ getLength h0 b >= norm_length+1 /\ getLength h1 b = getLength h0 b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < getLength h0 b) ==> v (getValue h0 b i) = v (getValue h1 b i))

val carry:
  b:bigint_wide -> ctr:nat{ctr <= norm_length} -> ST unit
    (requires (fun h -> Carriable h b ctr /\ Carried h b ctr))
    (ensures (fun h0 _ h1 -> Carried h1 b norm_length /\ Untouched_2 h0 h1 b ctr
      /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
      /\ modifies !{getRef b} h0 h1
      /\ getLength h1 b = getLength h0 b))
let rec carry b i =
  //@@
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index_wide b i in
    let ri = mod2_51 bi in
    assert(v ri < pow2 (templ i)); 
    upd_wide b i ri; 
    let h1 = ST.get() in
    upd_lemma h0 h1 b i ri; 
    let c = (bi |>> 51) in
    // In the spec of >>
    admitP(True /\ v c < pow2 (platform_wide - 51)); 
    let bip1 = index_wide b (i+1) in
    assert(v bip1 = v (getValue h1 b (i+1))); 
    assert(v bip1 < pow2 (platform_wide - 1)); 
    auxiliary_lemma_1 bip1 c; 
    let z = bip1 |+ c in
    upd_wide b (i+1) z;
    let h2 = ST.get() in
    upd_lemma h1 h2 b (i+1) z; 
    eval_carry_lemma h0 b h2 b i; 
    cut (forall (j:nat). (j > i+1 /\ j <= norm_length) ==> v (getValue h2 b j) < pow2 (platform_wide - 1));
    carry b (i+1)

#reset-options

val carry_top_to_0: b:bigint_wide -> ST unit
    (requires (fun h -> Carried h b norm_length /\ getLength h b >= norm_length+1
      /\ v (getValue h b 0) + 19 * v (getValue h b norm_length) < pow2 (platform_wide-1)))
    (ensures (fun h0 _ h1 -> Carried h0 b norm_length /\ Carried' h1 b 1
      /\ getLength h1 b = getLength h0 b
      /\ eval h1 b norm_length % (reveal prime) = eval h0 b (norm_length+1) % (reveal prime)
      /\ v (getValue h1 b 0) = v (getValue h0 b 0) + 19 * v (getValue h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i > 0 /\ i < getLength h1 b) ==> 
	  v (getValue h1 b i) = v (getValue h0 b i)) ))
let carry_top_to_0 b =
  //@@
  let h0 = ST.get() in
  let b0 = index_wide b 0 in
  let btop = index_wide b norm_length in 
  let btop_19 = times_19 btop in  
  upd_wide b 0 (b0 |+ btop_19); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0

#reset-options

opaque type Carriable2 (h:heap) (b:bigint_wide) (ctr:nat{ctr<=norm_length}) =
  live h b /\ getLength h b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h b i))} i < ctr ==> v (getValue h b i) < pow2 51)
  /\ (forall (i:nat). {:pattern (v (getValue h b i))} (i > ctr /\ i < norm_length) ==> v (getValue h b i) < pow2 51)
  /\ (ctr < norm_length ==> v (getValue h b norm_length) = 0)
  /\ (ctr = norm_length ==> v (getValue h b norm_length) < 2)
  /\ v (getValue h b ctr) < pow2 51 + pow2 32
  /\ (v (getValue h b ctr) >= pow2 51 ==> (
      forall (i:nat). {:pattern (v (getValue h b i))} (i < ctr /\ i > 0) ==> v (getValue h b i) < pow2 32))
  /\ ((ctr = norm_length /\ v (getValue h b norm_length) = 1) ==> 
      (forall (i:nat). {:pattern (v (getValue h b i))} (i > 0 /\ i < norm_length) ==> v (getValue h b i) < pow2 32))

val helper_lemma_20: a:wide -> b:wide -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 32))
  (ensures (v a + v b < pow2 52 
	    /\ v a + v b / pow2 51 < 2 
	    /\ (v a + v b >= pow2 51 ==> (v a + v b) % pow2 51 < pow2 32) ))
let helper_lemma_20 a b = admit() 

val helper_lemma_21: a:wide -> Lemma (requires (v a < pow2 51 + pow2 32))
				    (ensures (v a < pow2 52 /\ v a / pow2 51 < 2))
let helper_lemma_21 a = 
  //@@
  Lemmas.pow2_double_sum 51; pow2_increases_lemma 51 32

val carry2: b:bigint_wide -> ctr:nat{ctr <= norm_length} -> ST unit
  (requires (fun h -> Carriable2 h b ctr))
  (ensures (fun h0 _ h1 -> Carriable2 h0 b ctr /\ Carriable2 h1 b norm_length
    /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
    /\ getLength h1 b = getLength h0 b
    /\ modifies !{getRef b} h0 h1))
let rec carry2 b i = 
  //@@
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index_wide b i in
    let ri = mod2_51 bi in
    assert(v ri < pow2 (templ i)); 
    upd_wide b i ri; 
    let h1 = ST.get() in
    upd_lemma h0 h1 b i ri; 
    let bip1 = index_wide b (i+1) in
    let c = (bi |>> 51) in 
    helper_lemma_21 bi;
    helper_lemma_20 bip1 c; 
    (* // In the spec of >> *)
    (* admitP(True /\ v c < pow2 (platform_wide - 51));  *)
    assert(v bip1 = v (getValue h1 b (i+1))); 
    pow2_increases_lemma (platform_wide-1) 51;
    assert(v bip1 < pow2 (platform_wide - 1)); 
    auxiliary_lemma_1 bip1 c; 
    let z = bip1 |+ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 51); 
    cut (v z >= pow2 51 ==> v c = 1); 
    cut (v c > 0 ==> v (getValue h0 b i) / (pow2 51) > 0 ==> v (getValue h0 b i) >= pow2 51); 
    cut (v z >= pow2 51 ==> v (getValue h1 b i) < pow2 32); 
    upd_wide b (i+1) z;
    let h2 = ST.get() in
    upd_lemma h1 h2 b (i+1) z; 
    cut (v z >= pow2 51 ==> v c = 1 /\ True); 
    eval_carry_lemma h0 b h2 b i;
    carry2 b (i+1)

val helper_lemma_30: a:wide -> b:wide -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 37))
  (ensures (v a + v b < pow2 52 
	    /\ v a + v b / pow2 51 < 2 
	    /\ (v a + v b >= pow2 51 ==> (v a + v b) % pow2 51 < pow2 37) ))
let helper_lemma_30 a b = admit() 

val helper_lemma_32: a:wide -> Lemma (requires (v a < pow2 52))
				   (ensures (v a / pow2 51 = 1 ==> v a >= pow2 51))
let helper_lemma_32 a =
  Lemmas.pow2_double_sum 51

val helper_lemma_33: a:wide -> b:wide -> Lemma (requires (v a < pow2 51 /\ v b < 2 /\ 
  (v b = 1 ==> v a < pow2 32)))
  (ensures (v a + v b < pow2 51))
let helper_lemma_33 a b = pow2_increases_lemma 51 33; Lemmas.pow2_double_sum 26

val last_carry: b:bigint_wide{getTemplate b = templ} -> ST unit
  (requires (fun h -> Carriable2 h b norm_length))
  (ensures (fun h0 _ h1 -> Carriable2 h0 b norm_length /\ Standardized h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies !{getRef b} h0 h1))
let last_carry b =
  //@@
  let h0 = ST.get() in
  let b0 = index_wide b 0 in
  let btop = index_wide b norm_length in
  cut (v b0 < pow2 51 /\ v btop < 2); 
  pow2_5_lemma ();
  cut (19 * v btop < pow2 5 /\ True);
  pow2_increases_lemma 51 5;
  Lemmas.pow2_double_sum 51;
  pow2_increases_lemma platform_wide 52;
  pow2_increases_lemma platform_wide 51;
  cut (v b0 + 19 * v btop < pow2 52 /\ True); 
  let btop_19 = times_19 btop in  
  let bi = (b0 |+ btop_19) in
  (* upd_wide b 0 (b0 |+ btop_19);  *)
  upd_wide b 0 bi;
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0; 
  upd_wide b norm_length zero_wide;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length; 
  cut (eval h2 b (norm_length+1) = eval h1 b norm_length /\ True); 
  (* let bi = index_wide b 0 in  *)
  let ri = mod2_51 bi in
  upd_wide b 0 ri; 
  let h3 = ST.get() in
  let c = (bi |>> 51) in 
  Lemmas.pow2_exp_1 32 5;
  cut (v bi < pow2 51 + 19 /\ True); 
  cut (v bi >= pow2 51 ==> v (getValue h3 b 1) < pow2 32); 
  helper_lemma_30 b0 btop_19; 
  helper_lemma_32 bi;
  let bip1 = index_wide b 1 in 
  cut (v bi >= pow2 51 ==> v bip1 < pow2 32); 
  cut (v c = 1 ==> v bip1 < pow2 32); 
  cut (v c = (v b0 + v btop_19) / pow2 51 /\ v bip1 < pow2 51); 
  helper_lemma_33 bip1 c; 
  let z = bip1 |+ c in 
  upd_wide b 1 z;
  let h4 = ST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut (True /\ v (getValue h4 b 1) < pow2 51);
  cut (Standardized h4 b)

#reset-options

val lemma_helper_40: h:heap -> b:bigint_wide -> Lemma
  (requires (live h b /\ getLength h b >= norm_length + 1 /\ v (getValue h b norm_length) < pow2 77
	    /\ v (getValue h b 0) < pow2 51))
  (ensures (live h b /\ getLength h b >= norm_length + 1 
    /\ v (getValue h b 0) + 19 * v (getValue h b norm_length) < pow2 (platform_wide - 1)
    /\ v (getValue h b 0) + 19 * v (getValue h b norm_length) < pow2 83))
let lemma_helper_40 h b = 
  pow2_5_lemma ();
  Lemmas.pow2_exp_1 5 77;
  pow2_increases_lemma 82 51;
  pow2_increases_lemma (platform_wide-1) 83;
  Lemmas.pow2_double_sum 82

val lemma_helper_41: a:wide -> Lemma (requires (v a < pow2 83))
				    (ensures (v a / pow2 51 < pow2 32))
let lemma_helper_41 a = 
  admit(); 
  ()

val lemma_helper_42: a:wide -> b:wide -> Lemma (requires (v a < pow2 51 /\ v b < pow2 32))
					      (ensures (v a + v b < pow2 52 
						       /\ v a + v b < pow2 platform_wide))
let lemma_helper_42 a b = pow2_increases_lemma platform_wide 52; pow2_increases_lemma 51 32

val freduce_coefficients: b:bigint_wide -> ST unit
  (requires (fun h -> Carriable h b 0))
  (ensures (fun h0 _ h1 -> Carriable h0 b 0 /\ Standardized h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
let freduce_coefficients b =
  //@@ timeout 100
  let h = ST.get() in
  upd_wide b norm_length zero_wide;
  let h' = ST.get() in
  eval_eq_lemma h h' b b norm_length;
  eval_definition h' b (norm_length+1);
  cut (True /\ eval h' b (norm_length+1) = eval h b norm_length);
  carry b 0;
  let h = ST.get() in
  lemma_helper_40 h b;
  carry_top_to_0 b;
  let h1 = ST.get() in
  upd_wide b norm_length zero_wide;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  eval_definition h2 b (norm_length+1);
  let b0 = index_wide b 0 in
  let b1 = index_wide b 1 in
  let r0 = mod2_51 b0 in
  let c0 = b0 |>> 51 in
  lemma_helper_41 b0; 
  lemma_helper_42 b1 c0;
  let h = ST.get() in
  upd_wide b 0 r0; 
  upd_wide b 1 (b1 |+ c0); 
  let h' = ST.get() in
  eval_carry_lemma h b h' b 0; 
  carry2 b 1; 
  last_carry b
  
#reset-options

opaque val gaddition_lemma: a:limb -> m:nat -> b:limb -> n:nat -> 
  GLemma unit (requires (bitsize (v a) m /\ bitsize (v b) n))
	(ensures (bitsize (v a + v b) (max m n + 1))) []
let gaddition_lemma a m b n = add_lemma m (v a) n (v b)

val addition_lemma: a:limb -> m:nat -> b:limb -> n:nat -> 
  Lemma (requires (bitsize (v a) m /\ bitsize (v b) n))
	(ensures (bitsize (v a + v b) (max m n + 1))) 
let addition_lemma a m b n = 
  coerce 
    (requires (bitsize (v a) m /\ bitsize (v b) n))
    (ensures (bitsize (v a + v b) (max m n + 1))) 
    (fun _ -> gaddition_lemma a m b n)

val aux_lemma_1: unit -> Lemma (requires (True)) (ensures (pow2 52 - 2 >= pow2 51 /\ pow2 52 - 38 >= pow2 51))
let aux_lemma_1 () =
  cut (pow2 6 = 64 /\ pow2 2 = 4);
  Lemmas.pow2_increases_1 51 6; Lemmas.pow2_increases_1 51 2;
  Lemmas.pow2_double_sum 51

#reset-options

val add_big_zero_core: b:bigint -> ST unit
  (requires (fun h -> Standardized h b))
  (ensures (fun h0 _ h1 -> Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b
			 /\ Filled h1 b ndiff' ndiff
			 /\ v (getValue h1 b 0) = v (getValue h0 b 0) + (pow2 52 - 38)
			 /\ v (getValue h1 b 1) = v (getValue h0 b 1) + (pow2 52 - 2)
			 /\ v (getValue h1 b 2) = v (getValue h0 b 2) + (pow2 52 - 2)
			 /\ v (getValue h1 b 3) = v (getValue h0 b 3) + (pow2 52 - 2)
			 /\ v (getValue h1 b 4) = v (getValue h0 b 4) + (pow2 52 - 2)
			 /\ modifies !{getRef b} h0 h1))
let add_big_zero_core b =
  //@@
  let h0 = ST.get() in
  let two52m38 = to_limb "0xfffffffffffda" in // pow2 52 - 38
  let two52m2 =  to_limb "0xffffffffffffe" in // pow2 52 - 2
  admitP(v two52m38 = pow2 52 - 38 /\ v two52m2 = pow2 52 - 2); 
  let b0 = index_limb b 0 in 
  cut(True /\ v b0 = v (getValue h0 b 0)); 
  cut(forall (i:nat). {:pattern (v (getValue h0 b i))} i < norm_length ==> bitsize (v (getValue h0 b i)) (templ i)); 
  cut(forall (i:nat). i < norm_length ==> v (getValue h0 b i) < pow2 (templ i)); 
  cut (v b0 < pow2 51 /\ v two52m38 < pow2 52); 
  addition_lemma b0 51 two52m38 52;
  Lemmas.pow2_increases_1 platform_size 53; 
  upd_limb b 0 (add_limb b0 two52m38); 

  let h1 = ST.get() in
  upd_lemma h0 h1 b 0 (add_limb b0 two52m38); 
  let b1 = index_limb b 1 in
  cut (v b1 = v (getValue h0 b 1) /\ v b1 < pow2 51 /\ v two52m2 < pow2 52); 
  addition_lemma b1 51 two52m2 52;
  Lemmas.pow2_increases_1 platform_size 53; 
  upd_limb b 1 (add_limb b1 two52m2); 
  
  let h2 = ST.get() in
  upd_lemma h1 h2 b 1 (add_limb b1 two52m2); 
  let b2 = index_limb b 2 in
  cut (v b2 = v (getValue h1 b 2) /\ v (getValue h1 b 2) = v (getValue h0 b 2) /\ v b2 < pow2 51);
  addition_lemma b2 51 two52m2 52;
  Lemmas.pow2_increases_1 platform_size 53; 
  upd_limb b 2 (add_limb b2 two52m2); 

  let h3 = ST.get() in
  upd_lemma h2 h3 b 2 (add_limb b2 two52m2); 
  let b3 = index_limb b 3 in
  cut (v b3 = v (getValue h2 b 3) /\ v (getValue h2 b 3) = v (getValue h1 b 3) /\ v (getValue h1 b 3) = v (getValue h0 b 3) /\ v b3 < pow2 51);
  addition_lemma b3 51 two52m2 52;
  Lemmas.pow2_increases_1 platform_size 53; 
  upd_limb b 3 (add_limb b3 two52m2); 
  
  let h4 = ST.get() in
  upd_lemma h3 h4 b 3 (add_limb b3 two52m2); 
  let b4 = index_limb b 4 in
  cut (v b4 = v (getValue h3 b 4) /\ v (getValue h3 b 4) = v (getValue h2 b 4) /\ v (getValue h2 b 4) = v (getValue h1 b 4) /\ v (getValue h1 b 4) = v (getValue h0 b 4) /\ v b4 < pow2 51);
  addition_lemma b4 51 two52m2 52;
  Lemmas.pow2_increases_1 platform_size 53; 
  upd_limb b 4 (add_limb b4 two52m2);
  let h5 = ST.get() in 
  upd_lemma h4 h5 b 4 (add_limb b4 two52m2);
  cut (v (getValue h5 b 0) = v (getValue h0 b 0) + (pow2 52 - 38) /\ True); 
  cut (v (getValue h5 b 1) = v (getValue h0 b 1) + (pow2 52 - 2) /\ True); 
  cut (v (getValue h5 b 2) = v (getValue h0 b 2) + (pow2 52 - 2) /\ True); 
  cut (v (getValue h5 b 3) = v (getValue h0 b 3) + (pow2 52 - 2) /\ True); 
  cut (v (getValue h5 b 4) = v (getValue h0 b 4) + (pow2 52 - 2) /\ True); 
  cut (forall (i:nat). {:pattern (v (getValue h5 b i))} i < 5 ==> v (getValue h5 b i) < pow2 ndiff); 
  aux_lemma_1 (); 
  cut (forall (i:nat). {:pattern (v (getValue h5 b i))} i < 5 ==> v (getValue h5 b i) >= pow2 ndiff'); 
  cut (norm_length = 5 /\ True); 
  cut(Filled h5 b ndiff' ndiff)

#reset-options

val aux_lemma_2: a:int -> b:int -> c:int -> d:int -> e:int ->
  Lemma (pow2 204 * (a + pow2 52 - 2) + pow2 153 * (b + pow2 52 - 2) + pow2 102 * (c + pow2 52 - 2) 
	 + pow2 51 * (d + pow2 52 - 2) + (e + pow2 52 - 38) =
	 pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 256 - 38)
let aux_lemma_2 a b c d e =
  //@@
  let v = pow2 204 * (a + pow2 52 - 2) + pow2 153 * (b + pow2 52 - 2) + pow2 102 * (c + pow2 52 - 2) 
	 + pow2 51 * (d + pow2 52 - 2) + (e + pow2 52 - 38) in
  cut (True /\ v = pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 204 * pow2 52 - pow2 204 * 2 + pow2 153 * pow2 52 - pow2 153 * 2 + pow2 102 * pow2 52 - pow2 102 * 2 + pow2 51 * pow2 52 - pow2 51 * 2 + pow2 52 - 38); 
  cut (True /\ pow2 1 = 2); 
  Lemmas.pow2_exp_1 204 52; Lemmas.pow2_exp_1 204 2; 
  Lemmas.pow2_exp_1 153 52; Lemmas.pow2_exp_1 153 2; 
  Lemmas.pow2_exp_1 102 52; Lemmas.pow2_exp_1 102 2; 
  Lemmas.pow2_exp_1 51 52; Lemmas.pow2_exp_1 51 2

#reset-options

// Missing modulo spec, to be added to the axioms
assume val modulo_lemma_2: a:int -> b:pos -> Lemma ( (a + 2 * b) % b = a % b)

opaque val gaux_lemma_3: a:int -> GLemma unit (requires (True)) (ensures ((a + pow2 256 - 38) % reveal prime = a % reveal prime)) []
let gaux_lemma_3 a =
  //@@
  Lemmas.pow2_double_mult 255;
  cut (True /\ 2 * reveal prime = pow2 256 - 38);
  modulo_lemma_2 a (reveal prime)

val aux_lemma_3: a:int -> Lemma (requires (True)) (ensures ( (a + pow2 256 - 38) % reveal prime = a % reveal prime))
let aux_lemma_3 a = 
  coerce (requires (True)) (ensures ( (a + pow2 256 - 38) % reveal prime = a % reveal prime))
    (fun _ -> gaux_lemma_3 a)

#reset-options

opaque val gadd_big_zero_lemma: h0:heap -> h1:heap -> b:bigint -> 
  GLemma unit (requires (Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b 
		  /\ Filled h1 b ndiff' ndiff
		  /\ v (getValue h1 b 0) = v (getValue h0 b 0) + (pow2 52 - 38)
		  /\ v (getValue h1 b 1) = v (getValue h0 b 1) + (pow2 52 - 2)
		  /\ v (getValue h1 b 2) = v (getValue h0 b 2) + (pow2 52 - 2)
		  /\ v (getValue h1 b 3) = v (getValue h0 b 3) + (pow2 52 - 2)
		  /\ v (getValue h1 b 4) = v (getValue h0 b 4) + (pow2 52 - 2) ))
	(ensures (Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b
		 /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime)) []
let gadd_big_zero_lemma h0 h1 b =
  //@@
  cut (bitweight templ 0 = 0 /\ bitweight templ 1 = 51 /\ bitweight templ 2 = 102 /\ bitweight templ 3 = 153 /\ bitweight templ 4 = 204); 
  cut (True /\ eval h1 b norm_length = pow2 204 * (v (getValue h0 b 4) + pow2 52 - 2) + eval h1 b 4); 
  cut (True /\ eval h1 b 4 = pow2 153 * (v (getValue h0 b 3) + pow2 52 - 2) + eval h1 b 3); 
  cut (True /\ eval h1 b 3 = pow2 102 * (v (getValue h0 b 2) + pow2 52 - 2) + eval h1 b 2); 
  cut (True /\ eval h1 b 2 = pow2 51 * (v (getValue h0 b 1) + pow2 52 - 2) + eval h1 b 1); 
  cut (True /\ eval h1 b 1 = (v (getValue h0 b 0) + pow2 52 - 38)); 
  cut (eval h1 b norm_length = 
	    pow2 204 * (v (getValue h0 b 4) + pow2 52 - 2) 
	    + pow2 153 * (v (getValue h0 b 3) + pow2 52 - 2) 
	    + pow2 102 * (v (getValue h0 b 2) + pow2 52 - 2) 
	    + pow2 51 * (v (getValue h0 b 1) + pow2 52 - 2) 
	    + (v (getValue h0 b 0) + pow2 52 - 38) /\ True); 
  cut (True /\ eval h0 b norm_length = pow2 204 * v (getValue h0 b 4)  + eval h0 b 4); 
  cut (True /\ eval h0 b 4 = pow2 153 * v (getValue h0 b 3)  + eval h0 b 3); 
  cut (True /\ eval h0 b 3 = pow2 102 * v (getValue h0 b 2) + eval h0 b 2); 
  cut (True /\ eval h0 b 2 = pow2 51 * v (getValue h0 b 1) + eval h0 b 1); 
  cut (True /\ eval h0 b 1 = v (getValue h0 b 0) ); 
  cut (True /\ eval h0 b norm_length = pow2 204 * v (getValue h0 b 4) + pow2 153 * v (getValue h0 b 3)  
			       + pow2 102 * v (getValue h0 b 2) + pow2 51 * v (getValue h0 b 1) 
			       + v (getValue h0 b 0)); 
  aux_lemma_2 (v (getValue h0 b 4)) (v (getValue h0 b 3)) (v (getValue h0 b 2)) (v (getValue h0 b 1)) (v (getValue h0 b 0));
  let a = pow2 204 * v (getValue h0 b 4) + pow2 153 * v (getValue h0 b 3)  
			       + pow2 102 * v (getValue h0 b 2) + pow2 51 * v (getValue h0 b 1) 
			       + v (getValue h0 b 0) in
  aux_lemma_3 a			       

val add_big_zero_lemma: h0:heap -> h1:heap -> b:bigint -> 
  Lemma (requires (Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b 
		  /\ Filled h1 b ndiff' ndiff
		  /\ v (getValue h1 b 0) = v (getValue h0 b 0) + (pow2 52 - 38)
		  /\ v (getValue h1 b 1) = v (getValue h0 b 1) + (pow2 52 - 2)
		  /\ v (getValue h1 b 2) = v (getValue h0 b 2) + (pow2 52 - 2)
		  /\ v (getValue h1 b 3) = v (getValue h0 b 3) + (pow2 52 - 2)
		  /\ v (getValue h1 b 4) = v (getValue h0 b 4) + (pow2 52 - 2) ))
	(ensures (Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b
		 /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
let add_big_zero_lemma h0 h1 b =
  coerce (requires (Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b 
		  /\ Filled h1 b ndiff' ndiff
		  /\ v (getValue h1 b 0) = v (getValue h0 b 0) + (pow2 52 - 38)
		  /\ v (getValue h1 b 1) = v (getValue h0 b 1) + (pow2 52 - 2)
		  /\ v (getValue h1 b 2) = v (getValue h0 b 2) + (pow2 52 - 2)
		  /\ v (getValue h1 b 3) = v (getValue h0 b 3) + (pow2 52 - 2)
		  /\ v (getValue h1 b 4) = v (getValue h0 b 4) + (pow2 52 - 2) ))
         (ensures (Standardized h0 b /\ live h1 b /\ getLength h1 b = getLength h0 b
		 /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
	 (fun _ -> gadd_big_zero_lemma h0 h1 b)

#reset-options

let n0 = ndiff'
let n1 = ndiff

let add_big_zero b =
  let h0 = ST.get() in
  add_big_zero_core b;
  let h1 = ST.get() in
  add_big_zero_lemma h0 h1 b

#reset-options

(* Not verified *)
let normalize (b:bigint) =
  admit();
  let two51m1 = to_limb "0x7ffffffffffff" in // pow2 51 - 1
  let two51m19 = to_limb "0x7ffffffffffed" in // pow2 51 - 19
  let b4 = (index_limb b 4) in
  let b3 = (index_limb b 3) in
  let b2 = (index_limb b 2) in
  let b1 = (index_limb b 1) in
  let b0 = (index_limb b 0) in  
  let mask = eq_limb b4 two51m1 in
  let mask = log_and_limb mask (eq_limb b3 two51m1) in
  let mask = log_and_limb mask (eq_limb b2 two51m1) in
  let mask = log_and_limb mask (eq_limb b1 two51m1) in
  let mask = log_and_limb mask (gte_limb b0 two51m19) in
  let sub_mask = log_and_limb mask two51m1 in
  let sub_mask2 = log_and_limb mask two51m19 in
  // Conditionally substract 2^255 - 19 
  let b4 = index_limb b 4 in
  upd_limb b 4 (sub_limb b4 sub_mask);
  let b3 = index_limb b 3 in
  upd_limb b 3 (sub_limb b3 sub_mask);
  let b2 = index_limb b 2 in
  upd_limb b 2 (sub_limb b2 sub_mask);
  let b1 = index_limb b 1 in
  upd_limb b 1 (sub_limb b1 sub_mask);
  let b0 = index_limb b 0 in
  upd_limb b 0 (sub_limb b0 sub_mask2)

#reset-options

val lemma_helper_100: a:nat -> b:nat -> c:pos -> d:pos -> Lemma (requires (a <= c /\ b < d))
							  (ensures  (a * b < c * d))
let lemma_helper_100 a b c d = ()

val lemma_satisfies_0: a:nat -> Lemma (requires (a <= pow2 122))
				   (ensures  (a * 20 < pow2 (platform_wide - 1)))
let lemma_satisfies_0 a = 
  pow2_5_lemma ();
  lemma_helper_100 a 20 (pow2 122) (pow2 5);
  pow2_exp_lemma 5 122

val lemma_satisfies: h:heap -> b:bigint_wide -> n:nat -> Lemma
  (requires (live h b /\ (forall (i:nat). i < getLength h b ==> v (getValue h b i) < pow2 n)))
  (ensures  (live h b /\ maxValue h b < pow2 n))
let lemma_satisfies h b n = ()  

let sum_satisfies_constraints h0 h1 cpy a b =
  //@@
  Lemmas.pow2_double_sum 51;
  cut (forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < norm_length 
	    ==> v (getValue h1 cpy i) < pow2 52);
  cut (forall (i:nat). {:pattern (v (getValue h1 cpy i))} (i >= norm_length /\ i < getLength h1 cpy)
	    ==> v (getValue h1 cpy i) = 0);
  cut(forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < getLength h1 cpy
	   ==> v (getValue h1 cpy i) < pow2 52);
  lemma_satisfies h1 cpy 52;
  pow2_increases_lemma 122 52;
  lemma_satisfies_0 (maxValue h1 cpy)

let difference_satisfies_constraints h0 h1 cpy a b =
  //@@
  cut(forall (i:nat). {:pattern (v (getValue h1 cpy i))} i < getLength h1 cpy
	   ==> v (getValue h1 cpy i) < pow2 53);
  lemma_satisfies h1 cpy 53;
  pow2_increases_lemma 122 53;
  lemma_satisfies_0 (maxValue h1 cpy)
  
val lemma_satisfies_2: h:heap -> b:bigint -> Lemma 
  (requires (Standardized h b))
  (ensures  (Standardized h b /\ maxValueNorm h b < pow2 51))
let lemma_satisfies_2 h b = ()

val lemma_satisfies_4: a:nat -> b:nat -> c:pos -> d:pos -> Lemma (requires (a < c /\ b < d))
							    (ensures (a * b < c * d))
let lemma_satisfies_4 a b c d = ()

val lemma_satisfies_3: b:nat -> c:nat -> Lemma
  (requires (b < pow2 51 /\ c < pow2 51))
  (ensures (norm_length * b * c <= pow2 105))
let lemma_satisfies_3 b c = 
  cut (True /\ 8 = pow2 3);
  pow2_exp_lemma 51 51;
  pow2_exp_lemma 3 102;
  Axiomatic.paren_mul_right norm_length b c;
  lemma_satisfies_4 b c (pow2 51) (pow2 51)

let mul_satisfies_constraints h0 h1 res a b =
  lemma_satisfies_2 h0 a;
  lemma_satisfies_2 h0 b;
  lemma_satisfies_3 (maxValueNorm h0 a) (maxValueNorm h0 b);
  pow2_increases_lemma 122 105;
  lemma_satisfies_0 (maxValue h1 res)
