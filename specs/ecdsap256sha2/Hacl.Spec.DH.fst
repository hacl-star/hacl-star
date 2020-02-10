module Hacl.Spec.DH

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Spec.P256
open Hacl.Spec.P256.Definitions

(* the code for initiator of DH key exchange *)

val ecp256_dh_i: s: lbytes 32 -> Tot (tuple3 (xN: nat {xN < prime256}) (yN: nat {yN < prime256}) (uint64)) 

let ecp256_dh_i s = 
  let xN, yN, zN = secret_to_public s in 
  if isPointAtInfinity (xN, yN, zN) then 
    xN, yN, u64 (pow2 64 - 1)
  else 
    xN, yN, u64 0
