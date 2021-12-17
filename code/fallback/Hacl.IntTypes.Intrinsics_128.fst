module Hacl.IntTypes.Intrinsics_128

open Hacl.IntTypes.Intrinsics

open Lib.IntTypes
open Lib.Buffer

(* Versions of add_carry_u64 and sub_borrow_u64 that rely on uint128 *)

val add_carry_u64: add_carry_st U64
let add_carry_u64 = add_carry U64 U128 64ul

val sub_borrow_u64: sub_borrow_st U64
let sub_borrow_u64 = sub_borrow U64 U128 64ul 128ul
