module Spec.P256.MontgomeryMultiplication.PointDouble

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Spec.P256.Lemmas
open Spec.P256.Definitions

open Lib.Sequence

open Spec.P256.MontgomeryMultiplication
open FStar.Mul
open Spec.P256


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0" 

let prime = prime256

val lemma_xToSpecification: pxD: nat {pxD < prime256} -> pyD: nat {pyD < prime256} -> pzD: nat  {pzD < prime256} -> 
  s: nat{fromDomain_ s = 4 * pxD * pyD * pyD % prime} -> 
  m: nat{fromDomain_ m = (((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD)) % prime} -> 
  x3: nat{
    let mD = fromDomain_ m in 
    let sD = fromDomain_ s in 
    fromDomain_ x3 = (mD * mD - 2*sD) % prime} -> 
  Lemma 
    (
      let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in 
      fromDomain_ x3 = xN
    )

let lemma_xToSpecification pxD pyD pzD s m x3 = ()


val lemma_yToSpecification: pxD: nat {pxD < prime256} -> pyD: nat {pyD < prime256} -> pzD: nat  {pzD < prime256} ->
  s: nat {s = toDomain_ (4 * pxD * pyD * pyD % prime)} -> 
  m: nat {m = toDomain_ (((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime)} ->
  x3: nat{
    let mD = fromDomain_ m in 
    let sD = fromDomain_  s in 
    fromDomain_ x3 = (mD * mD - 2 * sD) % prime} -> 
  y3: nat{
    let mD = fromDomain_ m in 
    let sD = fromDomain_ s in 
    let x3D = fromDomain_ x3 in 
    fromDomain_ y3 = ((mD * (sD - x3D) - (8 * pyD * pyD * pyD * pyD)) % prime)} -> 
  Lemma
    (
      let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in 
      fromDomain_ y3 = yN
    )  
      
let lemma_yToSpecification pxD pyD pzD s m x3 y3 = ()


val lemma_zToSpecification: pxD: nat {pxD < prime256} -> pyD: nat {pyD < prime256} -> pzD: nat {pzD < prime256} ->
  z3: nat{fromDomain_ z3 = 2 * pyD * pzD % prime} -> 
  Lemma (
    let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in 
    fromDomain_ z3 = zN
  )

let lemma_zToSpecification pxD pyD pzD z3 = ()
