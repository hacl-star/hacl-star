module Lib.Poly.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

type lib_poly n m = set n m

val powers: 
  #m:nat{m>1}
  -> n:size_nat
  -> o:field m 
  -> p:lib_poly n m{forall (k:nat{k<n}). p.[k] = o ^% k}

val sum_nth_root_unity_lemma: 
  #q:nat{q>1} 
  -> n:size_nat 
  -> o:field q{o ^% n = 1 /\ o<>1 /\ is_invertible (o-%1)} 
  -> Lemma (modular_sum_n (powers n o) = 0)

val lib_ntt: 
  #n:size_nat 
  -> #m:nat{m>1} 
  -> omega:field m 
  -> psi:field m
  -> p:lib_poly n m
  -> Tot (p':lib_poly n m)

val lib_ntt_lemma:
  #n:size_nat 
  -> #m:nat{m>1} 
  -> omega:field m 
  -> psi:field m
  -> p:lib_poly n m
  -> p':lib_poly n m{p' == lib_ntt omega psi p}
  -> Lemma (forall (k:nat{k<n}). p'.[k] = modular_sum_n (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p))

val lib_nttinv: 
  #n:size_nat
  -> #m:nat{m>n /\ m>1}
  -> ninv:field m
  -> omegainv:field m 
  -> psiinv:field m
  -> (p:lib_poly n m) 
  -> Tot (p':lib_poly n m)

val lib_nttinv_lemma:
  #n:size_nat 
  -> #m:nat{m>n /\ m>1} 
  -> ninv:field m
  -> omegainv:field m 
  -> psiinv:field m
  -> p:lib_poly n m
  -> p':lib_poly n m{p' == lib_nttinv ninv omegainv psiinv p}
  -> Lemma (forall (k:nat{k<n}). p'.[k] = ninv *% (psiinv^%k) *% modular_sum_n (mapi (fun j g -> g *% (omegainv ^% (k*j))) p))

val lib_ntt_inversion_lemma_with_explicit_inverses: 
  #n:size_nat
  -> #m:nat{m>n /\ m>1}
  -> ninv:field m{n *% ninv = 1}
  -> omega:field m{omega ^% n = 1 /\ (forall (nn:field n). (omega ^% nn = 1 ==> nn = 0) /\ (~(is_invertible((omega ^% nn) -%1)) ==> nn = 0))} 
  -> omegainv:field m{omega *% omegainv = 1}
  -> psi:field m
  -> psiinv:field m{psi *% psiinv = 1}
  -> p:lib_poly n m  
  -> Lemma(lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) == p)

val lib_ntt_inversion_lemma: 
  #n:size_nat
  -> #m:nat{m>n /\ m>1 /\ is_invertible #m n}
  -> omega:field m{is_invertible omega /\ omega ^% n = 1 /\ (forall (nn:field n). (omega ^% nn = 1 ==> nn = 0) /\ (~(is_invertible((omega ^% nn) -%1)) ==> nn = 0))} 
 -> psi:field m{is_invertible psi} 
 -> p:lib_poly n m  
 -> Lemma(lib_nttinv (invert_mod n) (invert_mod omega) (invert_mod psi) (lib_ntt omega psi p) == p)
