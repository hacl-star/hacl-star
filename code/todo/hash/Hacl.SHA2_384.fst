module Hacl.SHA2_384

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Impl.SHA2_384


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module ST = FStar.HyperStack.ST
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_384
module Hash = Hacl.Impl.SHA2_384


#reset-options "--max_fuel 0  --z3rlimit 100"

let alloc () = Hash.alloc ()

let init state = Hash.init state

let update state data_8 = Hash.update state data_8

let update_multi state data n = Hash.update_multi state data n

let update_last state data len = Hash.update_last state data len

let finish state hash = Hash.finish state hash

let hash hash input len = Hash.hash hash input len
