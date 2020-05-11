module Hacl.Interface.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.DH
open Spec.ECDSAP256.Definition


let ecp256dh_i result scalar = Hacl.Impl.P256.DH.ecp256dh_i result scalar

let ecp256dh_r result pubKey scalar = Hacl.Impl.P256.DH.ecp256dh_r result pubKey scalar
