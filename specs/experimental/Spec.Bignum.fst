module Spec.Bignum

open FStar.Seq
open FStar.Mul
open FStar.UInt
open Spec.Seq.Lib

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

(* BIGNUM; make abstract type *)
type bignum = nat
type elem (n:pos) = e:bignum{e < n}
let bignum_to_uint8 x = U8.uint_to_t (to_uint_t 8 x)  (* bignum_to_bytes *)
let uint8_to_bignum x = U8.v x
let bignum_mul x y = (op_Multiply x y) (* use for extended_eucl & for mult by 256 *)
let bignum_mod x y = x % y (* use for extended_eucl & mod 256 *)
let bignum_div x y = x / y (* use for extended_eucl & div 256 *)
(* NEED TO IMPLEMENT: *)
let bignum_add x y = x + y (* bytes_to_bignum *)
let bignum_sub x y = x - y (* use for extended_eucl *)
let bignum_mul_mod x y m = (x * y) % m
let bignum_is_even x = (x % 2) = 0
let bignum_div2 x = x / 2