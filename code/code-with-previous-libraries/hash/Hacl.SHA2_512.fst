module Hacl.SHA2_512

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

open Hacl.Impl.SHA2_512


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

module ST = FStar.HyperStack.ST
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_512
module Hash = Hacl.Impl.SHA2_512


(* Definitions of aliases for functions *)
private let u8_to_h8 = Cast.uint8_to_sint8
private let u32_to_h32 = Cast.uint32_to_sint32
private let u32_to_u64 = FStar.Int.Cast.uint32_to_uint64

private let u32_to_h64 = Cast.uint32_to_sint64

private let h32_to_h8  = Cast.sint32_to_sint8

private let h32_to_h64 = Cast.sint32_to_sint64

private let u32_to_h128 = Cast.uint32_to_sint128

private let u64_to_u32 = FStar.Int.Cast.uint64_to_uint32

private let u64_to_h64 = Cast.uint64_to_sint64

private let u64_to_h128 = Cast.uint64_to_sint128

private let h64_to_h128 = Cast.sint64_to_sint128



//
// SHA-512
//

#reset-options "--max_fuel 0  --z3rlimit 50"

[@"c_inline"]
let alloc () = alloc ()

#reset-options "--max_fuel 0  --z3rlimit 50"

let init state = init state

#reset-options "--max_fuel 0  --z3rlimit 200"

let update state data = update state data

#reset-options "--max_fuel 0  --z3rlimit 200"

let update_multi state data n = update_multi state data n

#reset-options "--max_fuel 0  --z3rlimit 200"

let update_last state data len = update_last state data len

let finish state hash = finish state hash

#reset-options "--max_fuel 0  --z3rlimit 50"

let hash hash input len = Hash.hash hash input len
