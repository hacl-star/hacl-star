module Hacl.EC.Curve25519.Bignum.Fdifference.Lemmas

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib
open FStar.Math.Lemmas

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum.Lemmas.Utils

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

let addedZero h0 h1 (b:bigint) : GTot Type0 =
  norm h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) + (pow2 52 - 38)
  /\ v (get h1 b 1) = v (get h0 b 1) + (pow2 52 - 2)
  /\ v (get h1 b 2) = v (get h0 b 2) + (pow2 52 - 2)
  /\ v (get h1 b 3) = v (get h0 b 3) + (pow2 52 - 2)
  /\ v (get h1 b 4) = v (get h0 b 4) + (pow2 52 - 2)

val lemma_pow2_52m38: unit -> Lemma (0xfffffffffffda = pow2 52 - 38)
let lemma_pow2_52m38 () = assert_norm(0xfffffffffffda = pow2 52 - 38)

val lemma_pow2_52m2: unit -> Lemma (0xffffffffffffe = pow2 52 - 2)
let lemma_pow2_52m2 () = assert_norm(0xffffffffffffe = pow2 52 - 2)

val lemma_add_big_zero_core:
  b0:H64.t -> b1:H64.t -> b2:H64.t -> b3:H64.t -> b4:H64.t ->
  Lemma 
    (requires (v b0 < pow2 51 /\ v b1 < pow2 51 /\ v b2 < pow2 51 /\ v b3 < pow2 51 /\ v b4 < pow2 51))
    (ensures  (v b0 + pow2 52 - 38 < pow2 64
      /\ v b1 + pow2 52 - 2 < pow2 64
      /\ v b2 + pow2 52 - 2 < pow2 64
      /\ v b3 + pow2 52 - 2 < pow2 64
      /\ v b4 + pow2 52 - 2 < pow2 64))
let lemma_add_big_zero_core b0 b1 b2 b3 b4 =
  assert_norm(pow2 1 = 2);
  pow2_lt_compat 52 1;
  pow2_double_sum 51;
  pow2_double_sum 52;
  pow2_lt_compat 64 53

let bound53 h (b:bigint) : GTot Type0 =
  live h b
  /\ v (get h b 0) < pow2 53
  /\ v (get h b 1) < pow2 53
  /\ v (get h b 2) < pow2 53
  /\ v (get h b 3) < pow2 53
  /\ v (get h b 4) < pow2 53

(* module U32 = FStar.UInt32 *)

(* let op_Plus_Bar = U32.add *)
(* let op_Subtraction_Bar = U32.sub *)

(* val helper_lemma_1: *)
(*   i:nat -> len:nat -> x:nat ->  *)
(*   Lemma (requires (i < len /\ len <= x)) (ensures (i < x)) *)
(* let helper_lemma_1 i len v = ()   *)

(* (\* #reset-options *\) *)
(* val fdifference_aux_1: a:bigint -> b:bigint{disjoint a b} -> ctr:u32{U32.v ctr < norm_length} -> STL unit *)
(*     (requires (fun h -> live h a /\ live h b /\ norm_length <= length a /\ norm_length <= length b *)
(*               /\ (forall (i:nat{ i >= U32.v ctr /\ i < norm_length}). v (get h b i) >= v (get h a i)))) *)
(*     (ensures (fun h0 _ h1 ->  *)
(*       live h0 a /\ live h1 a /\ live h0 b /\ live h1 b *)
(*       /\ length a = length a /\ length b = length b *)
(*       /\ norm_length <= length a /\ norm_length <= length b /\ modifies_1 a h0 h1 *)
(*       /\ (forall (i:nat). *)
(* 	((i >= U32.v ctr+1 /\ i < norm_length) ==>  (v (get h1 b i) >= v (get h1 a i) *)
(* 						/\ get h1 a i == get h0 a i)) *)
(* 	/\ (((i<U32.v ctr \/ i>=norm_length) /\ i<length a) ==> get h1 a i == get h0 a i)) *)
(*       /\ v (get h1 a (U32.v ctr)) = v (get h0 b (U32.v ctr)) - v (get h0 a (U32.v ctr)))) *)

(* let fdifference_aux_1 a b ctr = *)
(*   //@@ *)
(*   let h0 = HST.get() in *)
(*   let i = ctr in *)
(*   (\* FdifferenceLemmas.helper_lemma_3 i norm_length;  *\) *)
(*   helper_lemma_1 (U32.v i) norm_length (length a); *)
(*   helper_lemma_1 (U32.v i) norm_length (length b); *)
(*   let ai = index a i in  *)
(*   let bi = index b i in  *)
(*   assert(U32.v i >= U32.v ctr /\ U32.v i < norm_length);  *)
(*   cut(b2t(v (get h0 b (U32.v i)) >= v (get h0 a (U32.v i))));  *)
(*   let z = bi -^ ai in  *)
(*   upd a i z; *)
(*   let h1 = HST.get() in *)
(*   (\* upd_lemma h0 h1 a i z; *\) *)
(*   (\* no_upd_lemma h0 h1 b ((only a)) *\) *)
(*   () *)
  
(* val fdifference_aux_2_0: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} ->  *)
(*   ctr:nat{ctr < norm_length} -> Lemma (requires ( *)
(*       live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b *)
(*       /\ modifies_1 a h0 h1 /\ modifies_1 a h1 h2 *)
(*       // Conditions from fdifference_aux *)
(*       /\ (modifies_1 a h1 h2) *)
(*       /\ (forall (i:nat). *)
(* 	  ((i>=ctr+1 /\ i<norm_length) ==> (v (get h2 a i) = v (get h1 b i) - v (get h1 a i))) *)
(* 	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h1 a i))) *)
(*       // Conditions from fdifference_aux_1 *)
(*       /\ (forall (i:nat). *)
(* 	  ((i >= ctr+1 /\ i < norm_length) ==> *)
(* 	    v (get h1 b i) >= v (get h1 a i) /\ get h1 a i == get h0 a i) *)
(* 	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> get h1 a i == get h0 a i)) *)
(*       /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr))) *)
(*     (ensures ( *)
(*       (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b) *)
(*       /\ (modifies_1 a h0 h2) *)
(*       /\ (length a = length a) *)
(*       /\ (forall (i:nat). (i>= ctr /\ i<norm_length) ==> (v (get h2 a i) = v (get h0 b i) - v (get h0 a i))) *)
(*       )) *)
      
(* let fdifference_aux_2_0 h0 h1 h2 a b ctr = *)
(*   //@@ *)
(*   (\* no_upd_lemma h0 h1 b ((only a)); *\) *)
(*   assert(length a = length a); *)
(*   assert(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==> *)
(* 	  (v (get h2 a i) = v (get h1 b i) - v (get h1 a i)));   *)
(*   assert(forall (i:nat). (i>=ctr+1 /\ i < norm_length) ==> get h1 a i == get h0 a i);  *)
(*   assert(get h2 a ctr == get h1 a ctr);  *)
(*   assert(v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)); *)
(*   cut(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==> *)
(* 	  (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)));  *)
(*   cut(True /\ v (get h2 a ctr) = v (get h0 b ctr) - v (get h0 a ctr));  *)
(*   (\* FdifferenceLemmas.helper_lemma_5 ctr norm_length; *\) *)
(*   assert(forall (i:nat). (i>=ctr /\ i < norm_length) ==> *)
(* 	   (v (get h2 a i) = v (get h0 b i) - v (get h0 a i))) *)

(* (\* #reset-options *\) *)

(* val fdifference_aux_2_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} ->  *)
(*   ctr:nat{ctr < norm_length} -> *)
(*   Lemma  *)
(*     (requires ( *)
(*       live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b *)
(*       /\ modifies_1 a h0 h1 /\ modifies_1 a h1 h2 *)
(*       /\ length a = length a /\ length a = length a *)
(*       /\ length b = length b /\ length b = length b *)
(*       /\ (norm_length <= length a /\ norm_length <= length b) *)
(*       // Conditions from fdifference_aux *)
(*       /\ (modifies_1 a h1 h2) *)
(*       /\ (forall (i:nat). *)
(* 	  ((i>=ctr+1 /\ i<norm_length) ==> (v (get h2 a i) = v (get h1 b i) - v (get h1 a i))) *)
(* 	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h1 a i))) *)
(*       // Conditions from fdifference_aux_1 *)
(*       /\ (forall (i:nat). *)
(* 	  ((i >= ctr+1 /\ i < norm_length) ==> *)
(* 	    v (get h1 b i) >= v (get h1 a i) /\ get h1 a i == get h0 a i) *)
(* 	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> get h1 a i == get h0 a i)) *)
(*       /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr))) *)
(*     (ensures ( *)
(*       (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b) *)
(*       /\ (norm_length <= length a /\ norm_length <= length b) *)
(*       /\ (modifies_1 a h0 h2) *)
(*       /\ (length a = length a) *)
(*       /\ (forall (i:nat). ((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h0 a i)) *)
(*     )) *)
(* let fdifference_aux_2_1 h0 h1 h2 a b ctr =  *)
(*   //@@ *)
(*   () *)

(* val fdifference_aux_2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} ->  *)
(*   ctr:nat{ctr < norm_length} -> Lemma *)
(*     (requires ( *)
(*       live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b *)
(*       /\ modifies_1 a h0 h1 /\ modifies_1 a h1 h2 *)
(*       /\ length a = length a /\ length a = length a *)
(*       /\ length b = length b /\ length b = length b *)
(*       /\ (norm_length <= length a /\ norm_length <= length b) *)
(*       // Conditions from fdifference_aux *)
(*       /\ (modifies_1 a h1 h2) *)
(*       /\ (forall (i:nat).  *)
(* 	  ((i>= ctr+1 /\ i<norm_length) ==> *)
(* 	    (v (get h2 a i) = v (get h1 b i) - v (get h1 a i))) *)
(* 	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h1 a i))) *)
(*       // Conditions from fdifference_aux_1 *)
(*       /\ (forall (i:nat). *)
(* 	  ((i >= ctr+1 /\ i < norm_length) ==> v (get h1 b i) >= v (get h1 a i) *)
(* 						/\ get h1 a i == get h0 a i) *)
(* 	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> get h1 a i == get h0 a i)) *)
(*       /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr))) *)
(*     (ensures ( *)
(*       (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b) *)
(*       /\ (norm_length <= length a /\ norm_length <= length b) *)
(*       /\ (modifies_1 a h0 h2) *)
(*       /\ (length a = length a) *)
(*       /\ (forall (i:nat). *)
(* 	  ((i>= ctr /\ i<norm_length) ==>  *)
(* 	    (v (get h2 a i) = v (get h0 b i) - v (get h0 a i))) *)
(* 	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h0 a i))) *)
(*       ))       *)
(* let fdifference_aux_2 h0 h1 h2 a b ctr = *)
(*   //@@ *)
(*   fdifference_aux_2_0 h0 h1 h2 a b ctr; *)
(*   fdifference_aux_2_1 h0 h1 h2 a b ctr *)

(* (\* #reset-options *\) *)

(* val fdifference_aux: a:bigint -> b:bigint{disjoint a b} -> ctr:u32{U32.v ctr <= norm_length } -> STL unit *)
(*     (requires (fun h -> live h a /\ live h b *)
(*       /\ (forall (i:nat). (i >= U32.v ctr /\ i < norm_length) ==> (v (get h b i) >= v (get h a i))) )) *)
(*     (ensures (fun h0 _ h1 ->  *)
(*       (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b) *)
(*       /\ (norm_length <= length a /\ norm_length <= length b) *)
(*       /\ (modifies_1 a h0 h1) *)
(*       /\ (length a = length a) *)
(*       /\ (forall (i:nat).  *)
(* 	  ((i>= U32.v ctr /\ i<norm_length) ==>   *)
(* 	    (v (get h1 a i) = v (get h0 b i) - v (get h0 a i))) *)
(* 	  /\ (((i<U32.v ctr \/ i >= norm_length) /\ i<length a) ==> (get h1 a i == get h0 a i))) *)
(*     )) *)
(* let rec fdifference_aux a b ctr = *)
(*   //@@ *)
(*   let h0 = HST.get() in *)
(*   if U32.eq ctr nlength then () *)
(*   else begin *)
(*       fdifference_aux_1 a b ctr;  *)
(*       let h1 = HST.get() in *)
(*       (\* no_upd_lemma h0 h1 b ((only a)); *\) *)
(*       fdifference_aux a b (ctr+|1ul);  *)
(*       let h2 = HST.get() in *)
(*       fdifference_aux_2 h0 h1 h2 a b (U32.v ctr) *)
(*   end *)
  
(* (\* #reset-options *\) *)

(* val subtraction_lemma_aux: h0:heap ->  h1:heap -> a:bigint{live h0 a /\ live h1 a} ->  *)
(*   b:bigint{live h0 b} -> len:pos{len <= length a /\ len <= length b *)
(*     /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } -> *)
(*   Lemma (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1)) *)
(* 		/\ (v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))) ) ) *)
(*     (ensures (eval h0 b len - eval h0 a len = eval h1 a len)) *)
(* let subtraction_lemma_aux h0 h1 a b len = *)
(*   //@@ *)
(*   eval_def h1 a len; *)
(*   assert(eval h1 a len = pow2 (bitweight (templ) (len-1)) * v (get h1 a (len-1)) + eval h1 a (len-1)); *)
(*   assert(v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1)));  *)
(*   Math.Axioms.distributivity_sub_right (pow2 (bitweight (templ) (len-1))) (v (get h0 b (len-1)))  (v (get h0 a (len-1)));  *)
(*   assert(eval h1 a len = (pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1)) - pow2 (bitweight (templ) (len-1)) * v (get h0 a (len-1))) + eval h1 a (len-1)); *)
(*   (\* FdifferenceLemmas.helper_lemma_2  *\) *)
(*   (\* 		(pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1))) *\) *)
(*   (\* 		(pow2 (bitweight (templ) (len-1)) * v (get h0 a (len-1))) *\) *)
(*   (\* 		(eval h0 b (len-1)) *\) *)
(*   (\* 		(eval h0 a (len-1)); *\) *)
(*   eval_def h0 a len; *)
(*   eval_def h0 b len *)

(* (\* #reset-options *\) *)

(* val subtraction_lemma: *)
(*   h0:heap -> h1:heap -> a:bigint{live h0 a /\ live h1 a} -> b:bigint{live h0 b} -> *)
(*   len:nat{len <= length a /\ len <= length b *)
(*   /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } -> Lemma *)
(*     (requires (True)) *)
(*     (ensures ( eval h0 b len - eval h0 a len = eval h1 a len )) *)
(* let rec subtraction_lemma h0 h1 a b len = *)
(*   //@@ *)
(*   match len with *)
(*   | 0 -> () *)
(*   | _ -> subtraction_lemma h0 h1 a b (len-1); *)
(*     subtraction_lemma_aux h0 h1 a b len *)

(* (\* #reset-options *\) *)

(* val subtraction_max_value_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a} ->  *)
(*   b:bigint{live h0 b /\ length a = length b} -> *)
(*   c:bigint{live h1 c /\ length c = length a *)
(*    /\ (forall (i:nat). (i<length c) ==> v (get h1 c i) = v (get h0 b i) - v (get h0 a i)) } -> *)
(*   Lemma *)
(*     (requires (True)) *)
(*     (ensures (maxValue h1 c (length c) <= maxValue h0 b (length c))) *)
(* let subtraction_max_value_lemma h0 h1 a b c =  *)
(*   //@@ *)
(*   () *)

(* (\* #reset-options *\) *)

(* val max_value_lemma: h:heap -> a:bigint{live h a} -> m:nat ->Lemma  *)
(*     (requires (forall (n:nat). n < length a ==> v (get h a n) <= m)) *)
(*     (ensures (maxValue h a (length a) <= m)) *)
(* let max_value_lemma h a m =  *)
(*   //@@ *)
(*   () *)

(* val subtraction_max_value_lemma_extended: h0:heap -> h1:heap -> a:bigint{live h0 a} ->  *)
(*   b:bigint{live h0 b} -> *)
(*   c:bigint{live h1 c /\ length a = length c} ->  *)
(*   Lemma *)
(*     (requires ((forall (i:nat). (i<norm_length) ==>  *)
(* 		  v (get h1 c i) = v (get h0 b i) - v (get h0 a i)) *)
(* 	       /\ (forall (i:nat). (i < length c /\ i >= norm_length) ==> *)
(* 		   v (get h1 c i) = v (get h0 a i)))) *)
(*     (ensures (maxValue h1 c (length c) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b)))) *)
(* let subtraction_max_value_lemma_extended h0 h1 a b c =  *)
(*   //@@ *)
(*   cut ( forall (i:nat). (i < length c /\ i >= norm_length) *)
(* 	==> (v (get h1 c i) = v (get h0 a i) /\ v (get h1 c i) <= maxValue h0 a (length a))); *)
(*   cut ( forall (i:nat). (i < length c /\ i >= norm_length) *)
(*   	==> v (get h1 c i) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b)));	 *)
(*   assert ( forall (i:nat). (i < norm_length) *)
(* 	==> v (get h1 c i) = v (get h0 b i) - v (get h0 a i)); *)
(*   (\* assert(forall (i:nat). (i < norm_length) ==> v (get h1 c i) = v (get h0 b i) - v (get h0 a i) ==> v (get h1 c i) <= v (get h0 b i) ==> v (get h1 c i) <= maxValue h0 b);  *\) *)
(*   (\* cut ( forall (i:nat). (i < norm_length) *\) *)
(*   (\* 	==> v (get h1 c i) <= maxValue h0 b);  *\) *)
(*   (\* cut ( forall (i:nat). (i < norm_length) *\) *)
(*   (\* 	==> (v (get h0 a i) <= maxValue h0 a /\ v (get h0 b i) <= maxValue h0 b));  *\) *)
(*   cut ( forall (i:nat). (i < norm_length) *)
(* 	==> v (get h1 c i) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b))) *)

(* (\* #reset-options *\) *)

(* val auxiliary_lemma_2: ha:heap -> a:bigint{norm ha a} -> hb:heap -> b:bigint{filled hb b} ->  *)
(*   i:nat{i < norm_length} -> Lemma (v (get hb b i) - v (get ha a i) < pow2 (templ i + 1)) *)
(* let auxiliary_lemma_2 ha a hb b i = () *)
(*   //@@ *)
(*   (\* assert(True /\ bitsize (v (get hb b i)) max);  *\) *)
(*   (\* Lemmas.pow2_increases_2 min (templ i);  *\) *)
(*   (\* assert(bitsize (v (get ha a i)) (templ i));  *\) *)
(*   (\* assert(v (get ha a i) < pow2 (templ i));  *\) *)
(*   (\* cut(True /\ v (get ha a i) < pow2 min);  *\) *)
(*   (\* assert(bitsize (v (get ha a i)) min);  *\) *)
(*   (\* UInt.sub_lemma #max (v (get hb b i)) (v (get ha a i)) *\) *)

(* (\* #reset-options *\) *)

(* val auxiliary_lemma_0: ha:heap -> a:bigint{norm ha a} -> hb:heap -> b:bigint{filled hb b} -> *)
(*   Lemma (forall (i:nat). i < norm_length ==> v (get hb b i) - v (get ha a i) < pow2 (templ i + 1)) *)
(* let auxiliary_lemma_0 ha a hb b =  *)
(*   //@@ *)
(*   () *)

(* (\* #reset-options *\) *)

(* (\* val auxiliary_lemma_1: h0:heap -> h1:heap -> mods:FStar.Set.set abuffer -> b:bigint{filled h0 b} -> *\) *)
(* (\*   Lemma (requires (live h1 b /\ modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods))) *\) *)
(* (\* 	(ensures (filled h1 b)) *\) *)
(* (\* let auxiliary_lemma_1 h0 h1 mods min max b =  *\) *)
(* (\*   //@@ *\) *)
(* (\*   assert(FStar.Seq.Eq (sel h0 (getRef b)) (sel h1 (getRef b)));  *\) *)
(* (\*   () *\) *)

(* (\* #reset-options *\) *)

(* val fdifference': a:bigint -> b:bigint{disjoint a b} -> STL unit *)
(*     (requires (fun h -> norm h a /\ filled h b)) *)
(*     (ensures (fun h0 u h1 -> norm h0 a /\ filled h0 b /\ filled h1 b /\ live h1 a  *)
(*       /\ modifies_1 a h0 h1 *)
(*       /\ eval h1 a norm_length = eval h0 b norm_length - eval h0 a norm_length *)
(*       /\ (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i))  )) *)
(* let fdifference' a b = *)
(*   //@@ *)
(*   let h0 = HST.get() in *)
(*   auxiliary_lemma_0 h0 a h0 b;  *)
(*   fdifference_aux a b 0ul;  *)
(*   let h1 = HST.get() in *)
(*   (\* auxiliary_lemma_1 h0 h1 ((only a)) min max b ;  *\) *)
(*   subtraction_lemma h0 h1 a b norm_length *)


