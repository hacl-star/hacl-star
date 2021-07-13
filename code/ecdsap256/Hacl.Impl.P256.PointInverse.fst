module Hacl.Impl.P256.PointInverse

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer
open Spec.P256

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256.MontgomeryMultiplication

open FStar.Mul 


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val copyH: a: felem -> b: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b == as_nat h0 a /\ 
    fromDomain_ (as_nat h1 b) == fromDomain_ (as_nat h0 a))

let copyH a b = 
  assert_norm (pow2 64 * pow2 64 == pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 == pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);

  let a0 = index a (size 0) in 
  let a1 = index a (size 1) in 
  let a2 = index a (size 2) in 
  let a3 = index a (size 3) in 
  
  upd b (size 0) a0;
  upd b (size 1) a1;
  upd b (size 2) a2;
  upd b (size 3) a3

val point_inv: p: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result)  h0 h1 /\  
    as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime /\ (
  
    let x, y, z = gsub p (size 0) (size 4),  gsub p (size 4) (size 4), gsub p (size 8) (size 4) in 
    let x3, y3, z3 = gsub result (size 0) (size 4), gsub result (size 4) (size 4), gsub result (size 8) (size 4) in 
      
    let xD, yD, zD = fromDomain_ (as_nat h0 x), fromDomain_ (as_nat h0 y), fromDomain_ (as_nat h0 z) in 
    let x3D, y3D, z3D = fromDomain_ (as_nat h1 x3), fromDomain_ (as_nat h1 y3), fromDomain_ (as_nat h1 z3) in
      
    let xN, yN, zN = _point_inverse (xD, yD, zD) in 
    x3D == xN /\ y3D == yN /\ z3D == zN)) 


let point_inv p result tempBuffer = 
  let h0 = ST.get() in 
  
  let temp4 = sub tempBuffer (size 0) (size 4) in 
  let yP = sub p (size 4) (size 4) in 
  let yResult = sub result (size 4) (size 4) in 

  Hacl.Impl.P256.LowLevel.PrimeSpecific.p256_sub_zero yP yResult temp4;
  copyH (sub p (size 0) (size 4)) (sub result (size 0) (size 4)); 
  copyH (sub p (size 8) (size 4)) (sub result (size 8) (size 4));

  let h1 = ST.get() in 
  lemmaFromDomain 0;
  FStar.Math.Lemmas.small_mod 0 prime256


friend Hacl.Impl.P256.PointAdd8
open  Hacl.Impl.P256.Core
open Hacl.Impl.P256.PointAdd8
open Lib.ByteSequence 

let point_inv8 result p = 
  push_frame();
    let tempBuffer = create (size 112) (u64 0) in 
    let h0 = ST.get() in 
    let pU64 = sub tempBuffer (size 0) (size 12) in 
    let resultU64 = sub tempBuffer (size 12) (size 12) in 
    let tB88 = sub tempBuffer (size 24) (size 88) in 

    toFormPoint p pU64; 
    pointToDomain pU64 pU64;
    
    point_inv pU64 resultU64 tB88;
    
    norm resultU64 resultU64 tB88;
    fromFormPoint resultU64 result;
  pop_frame()
