module Hacl.Spec.Poly1305_64

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Seq
open FStar.Endianness
open FStar.Int.Cast

open Hacl.Cast

module Spec = Spec.Poly1305

module H8   = Hacl.UInt8
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


(* Types from Low-level crypto *)
type byte = Hacl.UInt8.t
type bytes = seq byte
type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type tag = word_16


type word' = Spec.word
type text = Spec.text

let log_t = text

let elem : Type0 = b:int{ b >= 0 /\ b < Spec.prime }

type seqelem = s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}


inline_for_extraction let red_44 s = Hacl.Spec.Bignum.AddAndMultiply.red_44 s
inline_for_extraction let red_45 s = Hacl.Spec.Bignum.AddAndMultiply.red_45 s

inline_for_extraction let p42  = Hacl.Spec.Bignum.AddAndMultiply.p42
inline_for_extraction let p44  = Hacl.Spec.Bignum.AddAndMultiply.p44

noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> log:log_t -> poly1305_state_

val seval: seqelem -> GTot nat
val selem: seqelem -> GTot elem
