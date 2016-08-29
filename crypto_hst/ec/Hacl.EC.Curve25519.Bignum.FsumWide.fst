module Hacl.EC.Curve25519.Bignum.FsumWide

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt128
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

val fsum_index:
  a:bigint_wide -> a_idx:u32 ->
  b:bigint_wide{disjoint a b} -> b_idx:u32 -> len:u32 ->
  ctr:u32{U32.v ctr <= U32.v len} -> STL unit
    (requires (fun h -> live h a /\ live h b
      /\ U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+U32.v len <= length b
      (* /\ (forall (i:nat). {:pattern (i+U32.v a_idx); (i+U32.v b_idx)} (i >= U32.v ctr /\ i < U32.v len) *)
      (* 	   ==> (v (get h a (i+U32.v a_idx)) + v (get h b (i+U32.v b_idx)) < pow2 platform_wide))  *)
    ))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      (* live h0 a /\ live h0 b /\ live h1 a /\ live h1 b *)
      (* /\ U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+U32.v len <= length b *)
      (* /\ modifies_1 a h0 h1 *)
      (* /\ (forall (i:nat). (i>= U32.v ctr /\ i<U32.v len) ==> *)
      (* 	  (v (get h1 a (i+U32.v a_idx)) = v (get h0 a (i+U32.v a_idx)) + v (get h0 b (i+U32.v b_idx))) ) *)
      (* /\ (forall (i:nat). ((i<U32.v ctr \/ i >= U32.v len) /\ i<length a-U32.v a_idx) ==> *)
      (* 	  (get h1 a (i+U32.v a_idx) == get h0 a (i+U32.v a_idx))) *)
    ))
let rec fsum_index a a_idx b b_idx len ctr =
  (* let h0 = HST.get() in *)
  if U32 (len =^ ctr) then ()
  else begin
    let i = ctr in
    (* FsumLemmas.helper_lemma_1 a_idx i len (length a); *)
    (* FsumLemmas.helper_lemma_1 b_idx i len (length b); *)
    let ai = a.(U32 (i +^ a_idx)) in
    let bi = b.(U32 (i +^ b_idx)) in
    (* assert(U32.v i >= U32.v ctr /\ U32.v i < U32.v len);  *)
    (* cut(b2t(v (get h0 a (U32.v i+U32.v a_idx)) + v (get h0 b (U32.v i+U32.v b_idx)) < pow2 platform_wide)); *)
    (* let z = ai +^ bi in *)
    upd a (U32 (a_idx +^ i)) (ai +%^ bi);
    (* let h1 = HST.get() in *)
    (* upd_lemma h0 h1 a (i+|a_idx) z;  *)
    (* no_upd_lemma h0 h1 b (only a);  *)
    (* cut(True /\ live h1 a);  *)
    (* cut(True /\ live h1 b);  *)
    (* cut(U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+len <= length b);  *)
    (* cut(forall (i:nat). (i >= ctr+1 /\ i < len) ==>  *)
    (*   (v (get h1 a (i+a_idx)) + v (get h1 b (i+b_idx)) < pow2 platform_wide)); *)
    (* FsumLemmas.auxiliary_lemma_0 len ctr; *)
    fsum_index a a_idx b b_idx len (U32 (ctr +^ 1ul))
    (* let h2 = HST.get() in *)
    (* no_upd_lemma h1 h2 b (only a);       *)
    (* cut (forall (i:nat). *)
    (*   (i<>ctr+a_idx /\ i < length a) ==> get h0 a (i) == get h1 a (i));  *)
    (* FsumLemmas.auxiliary_lemma_5 ctr (elength a) a_idx; *)
    (* cut (forall (i:nat). *)
    (*   (i<>ctr /\ i < length a - a_idx) ==> get h0 a (i+a_idx) == get h1 a (i+a_idx)); *)
    (* fsum_index_lemma h0 h1 h2 a (U32.v a_idx) b (U32.v b_idx) (U32.v len) (U32.v ctr) *)
  end

val fsum':
  a:bigint_wide -> b:bigint_wide{disjoint a b} -> STL unit
    (requires (fun h -> live h a /\ live h b
      (* norm_wide h a /\ norm_wide h b *)
    ))
    (ensures (fun h0 u h1 -> live h1 a /\ modifies_1 a h0 h1
      (* /\ norm_wide h0 a /\ norm_wide h0 b /\ norm_wide h1 b /\ live h1 a *)
      (* /\ modifies_1 a h0 h1 *)
      (* /\ eval_wide h1 a norm_length = eval_wide h0 a norm_length + eval_wide h0 b norm_length *)
      (* /\ (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i))  *)
    ))
let fsum' a b =
  //@@
  (* admitP(True /\ pow2 platform_size < pow2 platform_wide); *)
  (* let h0 = HST.get() in *)
  (* auxiliary_lemma_0 h0 a h0 b; *)
  fsum_index a 0ul b 0ul nlength 0ul
  (* let h1 = HST.get() in *)
  (* (\* no_upd_lemma h0 h1 b (only a); *\) *)
  (* auxiliary_lemma_1 h0 h1 b; *)
  (* auxiliary_lemma_3 h0 h1 a b; *)
  (* addition_lemma h0 h1 a b norm_length; *)
  (* () *)

