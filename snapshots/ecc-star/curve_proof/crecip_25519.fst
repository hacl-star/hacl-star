(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum --lax;
    variables:BIGNUM=../bignum_proof MATH=../math_interfaces;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $MATH/definitions.fst $MATH/field.fst $MATH/curve.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst $BIGNUM/modulo.fsti $BIGNUM/bignum.fsti;
  --*)

module Crecip

open Parameters
open Bigint
open Bignum

val loop:
  tmp:bigint -> v:bigint -> ctr:nat -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let rec loop tmp v ctr =
  match ctr with
  | 0 -> ()
  | _ ->
    fsquare tmp v;
    fsquare v tmp;
    loop tmp v (ctr-1)

val crecip':
  output:bigint -> z:bigint -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let crecip' output z = 
  let z2 = Bigint.create_limb norm_length in
  let z9 = Bigint.create_limb norm_length in
  let z11 = Bigint.create_limb norm_length in
  let z2_5_0 = Bigint.create_limb norm_length in
  let z2_10_0 = Bigint.create_limb norm_length in
  let z2_20_0 = Bigint.create_limb norm_length in
  let z2_50_0 = Bigint.create_limb norm_length in
  let z2_100_0 = Bigint.create_limb norm_length in
  let t0 = Bigint.create_limb norm_length in
  let t1 = Bigint.create_limb norm_length in
  fsquare z2 z;  (* 2 *)
  fsquare t1 z2;  (* 4 *)
  fsquare t0 t1;   (* 8 *)
  fmul z9 t0 z;  (* 9 *)
  fmul z11 z9 z2;  (* 11 *)
  fsquare t0 z11;  (* 22 *)
  fmul z2_5_0 t0 z9;  (* 2^5 - 2^0 = 31 *)	  
  fsquare t0 z2_5_0;  (* 2^6 - 2^1 *)
  fsquare t1 t0;  (* 2^7 - 2^2 *)
  fsquare t0 t1;  (* 2^8 - 2^3 *)
  fsquare t1 t0;  (* 2^9 - 2^4 *)
  fsquare t0 t1;  (* 2^10 - 2^5 *)
  fmul z2_10_0 t0 z2_5_0;  (* 2^10 - 2^0 *)	  
  fsquare t0 z2_10_0;  (* 2^11 - 2^1 *)
  fsquare t1 t0;  (* 2^12 - 2^2 *)
  loop t0 t1 4;  (* 2^20 - 2^10 *)	  
  fmul z2_20_0 t1 z2_10_0;  (* 2^20 - 2^0 *)   
  fsquare t0 z2_20_0;  (* 2^21 - 2^1 *) 
  fsquare t1 t0;  (* 2^22 - 2^2 *) 
  loop t0 t1 9;  (* 2^40 - 2^20 *)
  fmul t0 t1 z2_20_0;  (* 2^40 - 2^0 *)   
  fsquare t1 t0;  (* 2^41 - 2^1 *) 
  fsquare t0 t1;  (* 2^42 - 2^2 *) 
  loop t1 t0 4;  (* 2^50 - 2^10 *)  
  fmul z2_50_0 t0 z2_10_0;  (* 2^50 - 2^0 *)   
  fsquare t0 z2_50_0;  (* 2^51 - 2^1 *) 
  fsquare t1 t0;  (* 2^52 - 2^2 *) 
  loop t0 t1 24;  (* 2^100 - 2^50 *)  
  fmul z2_100_0 t1 z2_50_0;  (* 2^100 - 2^0 *)   
  fsquare t1 z2_100_0;  (* 2^101 - 2^1 *) 
  fsquare t0 t1;  (* 2^102 - 2^2 *) 
  loop t1 t0 49;  (* 2^200 - 2^100 *)  
  fmul t1 t0 z2_100_0;  (* 2^200 - 2^0 *) 
  fsquare t0 t1;  (* 2^201 - 2^1 *) 
  fsquare t1 t0;  (* 2^202 - 2^2 *) 
  loop t0 t1 24;  (* 2^250 - 2^50 *)  
  fmul t0 t1 z2_50_0;  (* 2^250 - 2^0 *)   
  fsquare t1 t0;  (* 2^251 - 2^1 *) 
  fsquare t0 t1;  (* 2^252 - 2^2 *) 
  fsquare t1 t0;  (* 2^253 - 2^3 *) 
  fsquare t0 t1;  (* 2^254 - 2^4 *) 
  fsquare t1 t0;  (* 2^255 - 2^5 *) 
  fmul output t1 z11  (* 2^255 - 21 *) 
