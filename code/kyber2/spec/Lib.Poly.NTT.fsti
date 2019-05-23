module Lib.Poly.NTT

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

open Lib.Poly

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

type lib_poly a len = lseq a len

val powers:
  #a: Type0
  -> #[tcresolve ()] r: ring a
  -> n:size_nat
  -> o:a
  -> p:lib_poly a n{forall (k:nat{k<n}). p.[k] == exp #a o k}

val sum_nth_root_unity_lemma: 
  #a: Type0
  -> #[tcresolve ()] r: ring a
  -> n:size_nat 
  -> o:a{exp o n == one /\ ~(o == one) /\ is_invertible (minus o one)} 
  -> Lemma (sum_n #a #add_ag.g.m (powers n o) == zero)

val lib_ntt: 
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat
  -> omega:a 
  -> psi:a
  -> p:lib_poly a n
  -> Tot (p':lib_poly a n)

val lib_ntt_lemma_instantiate:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat 
  -> omega:a 
  -> psi:a
  -> p:lib_poly a n
  -> p':lib_poly a n{p' == lib_ntt omega psi p}
  -> k:nat{k<n}
  -> Lemma (p'.[k] == sum_n #a #add_ag.g.m (mapi (fun j g -> mul (exp psi j) (mul g (exp omega (k*j)))) p))

val lib_ntt_lemma:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat 
  -> omega:a 
  -> psi:a
  -> p:lib_poly a n
  -> p':lib_poly a n{p' == lib_ntt omega psi p}
  -> Lemma (forall (k:nat{k<n}). p'.[k] == sum_n #a #add_ag.g.m (mapi (fun j g -> mul (exp psi j) (mul g (exp omega (k*j)))) p))

val lib_nttinv: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv:a
  -> omegainv:a 
  -> psiinv:a
  -> (p:lib_poly a n) 
  -> Tot (p':lib_poly a n)

val lib_nttinv_lemma_instantiate:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat 
  -> ninv:a
  -> omegainv:a 
  -> psiinv:a
  -> p:lib_poly a n
  -> p':lib_poly a n{p' == lib_nttinv ninv omegainv psiinv p}
  -> k:nat{k<n}
  -> Lemma (p'.[k] == mul #a ninv (mul (exp psiinv k) (sum_n #a #add_ag.g.m (mapi (fun j g -> mul g (exp omegainv (k*j))) p)))) 

val lib_nttinv_lemma:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat 
  -> ninv:a
  -> omegainv:a 
  -> psiinv:a
  -> p:lib_poly a n
  -> p':lib_poly a n{p' == lib_nttinv ninv omegainv psiinv p}
  -> Lemma (forall (k:nat{k<n}). p'.[k] == mul #a ninv (mul (exp psiinv k) (sum_n #a #add_ag.g.m (mapi (fun j g -> mul g (exp omegainv (k*j))) p)))) 

val lib_ntt_inversion_lemma1: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv:a{mul ninv (repeat_plus one n) == one}
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))} 
  -> omegainv:a{mul omega omegainv == one}
  -> psi:a
  -> psiinv:a{mul psiinv psi == one}
  -> p:lib_poly a n
  -> Lemma(lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) == p)


val lib_ntt_inversion_lemma2: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv:a{mul ninv (repeat_plus one n) == one}
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))} 
  -> omegainv:a{mul omegainv omega == one}
  -> psi:a
  -> psiinv:a{mul psi psiinv == one}
  -> p:lib_poly a n
  -> Lemma(lib_ntt omega psi (lib_nttinv ninv omegainv psiinv p) == p)
