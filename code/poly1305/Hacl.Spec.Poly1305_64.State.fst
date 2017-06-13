module Hacl.Spec.Poly1305_64.State

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq

open Hacl.Spec.Bignum.Bigint

module Spec = Spec.Poly1305

#reset-options "--max_fuel 0 --z3rlimit 20"

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

inline_for_extraction let seqelem = s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}


inline_for_extraction let p42 : p:pos{p = 0x40000000000} = assert_norm (pow2 42 = 0x40000000000);
  pow2 42
inline_for_extraction let p44 : p:pos{p = 0x100000000000} = assert_norm (pow2 44 = 0x100000000000);
  pow2 44
inline_for_extraction let p45 : p:pos{p = 0x200000000000} = assert_norm (pow2 45 = 0x200000000000);
  pow2 45

open Hacl.UInt64

let red_44 (s:seqelem) =
  v (Seq.index s 0) < p44 /\ v (Seq.index s 1) < p44 /\ v (Seq.index s 2) < p44
let red_45 (s:seqelem) =
  v (Seq.index s 0) < p45 /\ v (Seq.index s 1) < p45 /\ v (Seq.index s 2) < p45

noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> log:log_t -> poly1305_state_

let seval = Hacl.Spec.Bignum.Bigint.seval

let selem (s:seqelem) : GTot Spec.elem = seval s % Spec.prime

let invariant (st:poly1305_state_) : GTot Type0 =
  let acc = (MkState?.h st) in let r = (MkState?.r st) in let log = MkState?.log st in
  seval r < pow2 130 - 5 /\  red_44 r /\ red_45 acc /\ selem acc = Spec.poly log (seval r)
