module Hacl.EC.Curve25519.Bignum.Fsum

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64
(* open Hacl.SBuffer *)
open FStar.Buffer
open FStar.Math.Lib
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

val fsum_index_aux:
  a:bigint ->
  b:bigint{disjoint a b} ->
  ctr:u32{U32.v ctr < norm_length} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ norm_length <= length a /\ norm_length <= length b
      (* /\ willNotOverflow h a b (U32.v ctr) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      (* let ctr = U32.v ctr in *)
      (* live h0 a /\ live h1 a /\ live h0 b /\ live h1 b *)
      (* /\ length a = length a /\ length b = length b *)
      (* /\ norm_length <= length a /\ norm_length <= length b /\ modifies_1 a h0 h1 *)
      (* /\ (willNotOverflow h1 a b (ctr+1)) *)
      (* /\ (notModified h0 h1 a (ctr)) *)
      (* /\ v (get h1 a (ctr)) = v (get h0 a ctr) + v (get h0 b ctr) *)
    ))
let fsum_index_aux a b ctr =
  let ai = a.(ctr) in
  let bi = b.(ctr) in
  (* assert(U32.v ctr < norm_length); *)
  (* assert(b2t(v (get h0 a (U32.v ctr)) + v (get h0 b (U32.v ctr)) < pow2 platform_size));  *)
  (* let z = ai +^ bi in *)
  a.(ctr) <- (ai +%^ bi);
  (* let h1 = HST.get() in *)
  (* (\* upd_lemma h0 h1 a ctr z;  *\) *)
  (* assert(v (get h1 a (U32.v ctr)) = v (get h0 a (U32.v ctr)) + v (get h0 b (U32.v ctr)));  *)
  (* assert(notModified h0 h1 a (U32.v ctr));  *)
  (* assert(willNotOverflow h1 a b ((U32.v ctr)+1)); *)
  (* no_upd_lemma h0 h1 b (only a) *)
  ()

val fsum_index:
  a:bigint ->
  b:bigint{disjoint a b} ->
  ctr:u32{U32.v ctr <= norm_length } ->
  Stack unit
    (requires (fun h -> live h a /\ live h b
      (* /\ (forall (i:nat). (i >= U32.v ctr /\ i < norm_length) ==> *)
      (* 	  (v (get h a i) + v (get h b i) < pow2 platform_size)) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      (* let ctr = U32.v ctr in *)
      (* live h0 a /\ live h0 b /\ live h1 a /\ live h1 b *)
      (* /\ modifies_1 a h0 h1 *)
      (* /\ isSum h0 h1 a b ctr *)
      (* /\ notModified2 h0 h1 a ctr *)
    ))
let rec fsum_index a b ctr =
  (* //@@ *)
  (* let h0 = HST.get() in *)
  if U32 (nlength =^ ctr) then ()
  else (
    fsum_index_aux a b ctr;
    (* let h1 = HST.get() in *)
    (* no_upd_lemma h0 h1 b (only a);  *)
    (* FsumLemmas.auxiliary_lemma_6 norm_length ctr;  *)
    fsum_index a b (U32 (ctr +^ 1ul))
    (* let h2 = HST.get() in *)
    (* fsum_index_lemma h0 h1 h2 a b (U32.v ctr) *)
  )

val fsum':
  a:bigint ->
  b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b
      (* norm h a /\ norm h b *)
    ))
    (ensures (fun h0 u h1 -> live h1 a /\ modifies_1 a h0 h1
      (* /\ norm h0 a /\ norm h0 b /\ norm h1 b /\ live h1 a *)
      (* /\ modifies_1 a h0 h1 *)
      (* /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length *)
      (* /\ isSum h0 h1 a b 0 *)
    ))
let fsum' a b =
  (* let h0 = HST.get() in *)
  (* auxiliary_lemma_0 h0 a h0 b; *)
  fsum_index a b 0ul
  (* let h1 = HST.get() in *)
  (* no_upd_lemma h0 h1 b (only a); *)
  (* auxiliary_lemma_1 h0 h1 b; *)
  (* auxiliary_lemma_3 h0 h1 a b; *)
  (* addition_lemma h0 h1 a b norm_length; *)
  (* cut(forall (i:nat). (i >= 0 /\ i < norm_length) ==> i < norm_length); *)
  (* () *)
