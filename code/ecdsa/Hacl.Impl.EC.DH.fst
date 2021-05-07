module Hacl.Impl.EC.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECC
open Spec.ECDSA
open Hacl.Spec.EC.Definition
open Spec.DH
open Hacl.Spec.ECDSA.Definition
open Hacl.EC.Lemmas

open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.EC.Core
open Hacl.Impl.P256.Signature.Common

open Hacl.Impl.EC.Intro


#set-options " --z3rlimit 200 --max_fuel 0 --max_ifuel 0"

open FStar.Mul 

val ecp256_dh_i_: #c: curve -> resultBuffer: point c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) 
  -> scalar: scalar_t #MUT #c -> result: pointAffine8 c -> 
  Stack bool
  (requires fun h -> live h resultBuffer /\ live h tempBuffer /\ live h scalar /\ live h result /\
    disjoint resultBuffer result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc resultBuffer])
  (ensures fun h0 r h1 -> modifies (loc result |+| loc tempBuffer |+| loc resultBuffer) h0 h1 /\ (
    let pointX, pointY, flag = ecp256_dh_i #c (as_seq h0 scalar) in 
    let coordinateX_u8, coordinateY_u8 = getXAff8 #c result, getYAff8 #c result in
    let scalarX, scalarY = as_seq h1 (coordinateX_u8), as_seq h1 (coordinateY_u8) in 
    pointX == scalarX /\ pointY == scalarY /\ r == flag))


let ecp256_dh_i_ #c resultBuffer tempBuffer scalar result = 
  secretToPublic #c resultBuffer scalar tempBuffer;
    let h1 = ST.get() in 
  let r = isPointAtInfinityPrivate #c resultBuffer in 
    let h2 = ST.get() in 
  fromFormPoint #c resultBuffer result;
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 resultBuffer;

  let open Hacl.Impl.EC.LowLevel.RawCmp in 
  unsafe_bool_of_u64 r


let ecp256dh_i c result scalar =
  push_frame();
  let len = getCoordinateLenU64 c in 
  let tempBuffer = create (size 20 *! len) (u64 0) in
  let resultBuffer = create (size 3 *! len) (u64 0) in
    let h0 = ST.get() in 
  let flag = ecp256_dh_i_ resultBuffer tempBuffer scalar result in 
  pop_frame();
  flag

[@ (Comment "  This code is not side channel resistant on pubKey")]
val _ecp256dh_r: #c: curve 
  -> result: point c
  -> pubKey: point c
  -> scalar: scalar_t #MUT #c -> 
  Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ 
     LowStar.Monotonic.Buffer.all_disjoint [loc pubKey;  loc scalar; loc result] /\ (
    let pk = as_nat c h (getX pubKey), as_nat c h (getY pubKey), as_nat c h (getZ pubKey) in 
    ~ (isPointAtInfinity pk) /\ as_nat c h (getZ pubKey) == 1 /\
    as_nat c h (getX result) == 0 /\ as_nat c h (getY result) == 0 /\ as_nat c h (getZ result) == 0))
  (ensures fun h0 r h1 -> modifies (loc result |+| loc pubKey) h0 h1 /\ point_eval c h1 result /\ (
    let pk = as_nat c h0 (getX pubKey), as_nat c h0 (getY pubKey), as_nat c h0 (getZ pubKey) in 
    let x3, y3, z3 = point_as_nat c h1 result in
    if not (verifyQValidCurvePointSpec #c pk) then
      r = false /\ x3 == 0 /\ y3 == 0
    else begin
      let xN, yN, zN = scalar_multiplication #c (as_seq h0 scalar) pk in
      xN == x3 /\ yN == y3 /\ zN == z3 /\ (
      if isPointAtInfinity (xN, yN, zN) then
	r == false
      else
	r == true) end))


let _ecp256dh_r #c result pubKey scalar =
    let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (size 20 *! len) (u64 0) in
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_getZ_noChangeInState c h0 h1 pubKey;
  let publicKeyCorrect = verifyQValidCurvePoint #c pubKey tempBuffer in 
  if publicKeyCorrect then
    begin
        let h2 = ST.get() in 
	Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 pubKey;
	scalarMultiplication #c #MUT pubKey result scalar tempBuffer; 
	  let h3 = ST.get() in 
	let flag = isPointAtInfinityPrivate #c result in 
	pop_frame();
	  let h4 = ST.get() in 
	  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h3 h4 result;
	let open Hacl.Impl.EC.LowLevel.RawCmp in 
	unsafe_bool_of_u64 flag
    end
  else
    begin
      pop_frame();
	let h2 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
      false
    end

val lemma_zero_point_zero_coordinates: c: curve -> h: mem -> p: point c -> 
  Lemma (requires lseq_as_nat (as_seq h p) == 0)
  (ensures (as_nat c h (getX p) == 0) /\ (as_nat c h (getY p) == 0) /\ (as_nat c h (getZ p) == 0) /\ point_eval c h p)
    

let lemma_zero_point_zero_coordinates c h p = 
  let yz = gsub p (getCoordinateLenU64 c) (size 2 *! getCoordinateLenU64 c) in 
  lemma_test (as_seq h p) (v (getCoordinateLenU64 c));
  lemma_test (as_seq h yz) (v (getCoordinateLenU64 c));
  Hacl.Impl.P.PointAdd.Aux.lemma_point_eval_if_zero c p h


val ecp256_dh_r_: #c: curve -> result: pointAffine8 c 
  -> pubKey: pointAffine8 c 
  -> scalar: scalar_t #MUT #c
  -> pkF: point c
  -> rF: point c ->
  Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ live h pkF /\ live h rF /\
    disjoint pubKey pkF /\ point_eval c h rF /\ disjoint rF result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc rF; loc pkF; loc scalar] /\
    as_nat c h (getX rF) == 0 /\ as_nat c h (getY rF) == 0 /\ as_nat c h (getZ rF) == 0
  )
  (ensures fun h0 r h1 -> modifies (loc result |+| loc pkF |+| loc rF) h0 h1 /\ (
    let pubKeyX, pubKeyY = getXAff8 pubKey, getYAff8 pubKey in
    let pointX, pointY, flag = ecp256_dh_r #c (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
    let resultX, resultY = as_seq h1 (getXAff8 result), as_seq h1 (getYAff8 result) in 
    r == flag /\ resultX == pointX /\ resultY == pointY))

let ecp256_dh_r_ #c result pubKey scalar pkF rF = 
    let h0 = ST.get() in 
  toFormPoint pubKey pkF; 
    let h1 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 rF; 
  let flag = _ecp256dh_r #c rF pkF scalar in 
  fromFormPoint rF result; 
  flag



let ecp256dh_r #c result pubKey scalar =
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 

    let rF = create (size 3 *! len) (u64 0) in
    let pkF = create (size 3 *! len) (u64 0) in
    let h1 = ST.get() in 

    lemma_create_zero_buffer #U64 (3 * v len) c;
    lemma_zero_point_zero_coordinates c h1 rF;
  let flag = ecp256_dh_r_ #c result pubKey scalar pkF rF in 

  pop_frame();
  flag
