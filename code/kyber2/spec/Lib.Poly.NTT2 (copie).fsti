module Lib.Poly.NTT2

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics
open FStar.Tactics.Typeclasses

//open Lib.ModularArithmetic
//open Lib.ModularArithmetic.Lemmas

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Lib.Poly.NTT

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

val lib_ntt:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0} 
  -> zeta:a
  -> p:lib_poly a n
  -> Tot (p':lib_poly a n)

(*
val lib_ntt_lemma:
  #n:size_nat 
  -> #m:nat{m>1} 
  -> omega:field m 
  -> psi:field m
  -> p:lib_poly n m
  -> p':lib_poly n m{p' == lib_ntt omega psi p}
  -> Lemma (forall (k:nat{k<n}). p'.[k] = modular_sum_n (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p))
  *)

val lib_nttinv: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0} 
  -> halfninv:a
  -> zetainv:a 
  -> (p:lib_poly a n) 
  -> Tot (p':lib_poly a n)

(*
val lib_nttinv_lemma:
  #n:size_nat 
  -> #m:nat{m>n /\ m>1} 
  -> ninv:field m
  -> omegainv:field m 
  -> psiinv:field m
  -> p:lib_poly n m
  -> p':lib_poly n m{p' == lib_nttinv ninv omegainv psiinv p}
  -> Lemma (forall (k:nat{k<n}). p'.[k] = ninv *% (psiinv^%k) *% modular_sum_n (mapi (fun j g -> g *% (omegainv ^% (k*j))) p))
*)

val lib_ntt_inversion_lemma1: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0} 
  -> halfninv:a{mul halfninv (repeat_plus one (n/2)) == one}
  -> zeta:a{exp zeta n == one /\ (forall (nn:nat{nn<n}). (exp zeta nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp zeta nn) one)) ==> nn = 0))} 
  -> zetainv:a{mul zetainv zeta == one /\ mul zeta zetainv == one}
  -> p:lib_poly a n  
  -> Lemma(lib_nttinv halfninv zetainv (lib_ntt zeta p) == p)

val lib_ntt_inversion_lemma2: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0} 
  -> halfninv:a{mul halfninv (repeat_plus one (n/2)) == one}
  -> zeta:a{exp zeta n == one /\ (forall (nn:nat{nn<n}). (exp zeta nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp zeta nn) one)) ==> nn = 0))} 
  -> zetainv:a{mul zetainv zeta == one /\ mul zeta zetainv == one}
  -> p:lib_poly a n  
  -> Lemma(lib_ntt zeta (lib_nttinv halfninv zetainv p) == p)

val lib_ntt_ring : (#a:Type0) -> (#[tcresolve ()] r:ring a) -> (#n:size_nat{n%2=0}) -> (zeta:a{forall (x:a). mul x zeta == mul zeta x}) -> ring (lib_poly a n)
