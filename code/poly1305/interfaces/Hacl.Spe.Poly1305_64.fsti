module Hacl.Spe.Poly1305_64

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Seq
open FStar.Endianness
open FStar.Int.Cast

open Hacl.Cast
open Hacl.Spec.Bignum.AddAndMultiply
open Spec.Poly1305
open Hacl.Spec.Poly1305_64

module H8   = Hacl.UInt8
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


let invariant (st:poly1305_state_) : GTot Type0 =
  let acc = (MkState?.h st) in let r = (MkState?.r st) in let log = MkState?.log st in
  seval r < pow2 130 - 5 /\  red_44 r /\ red_45 acc /\ selem acc = poly log (seval r)
