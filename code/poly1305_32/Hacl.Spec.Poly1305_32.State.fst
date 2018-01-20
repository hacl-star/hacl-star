module Hacl.Spec.Poly1305_32.State

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq

open Hacl.Bignum.Parameters
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

inline_for_extraction let seqelem = s:Seq.seq limb{Seq.length s = 5}

inline_for_extraction let p26 : p:pos{p = 0x4000000} = assert_norm (pow2 26 = 0x4000000);
  pow2 26
inline_for_extraction let p27 : p:pos{p = 0x8000000} = assert_norm (pow2 27 = 0x8000000);
  pow2 27
inline_for_extraction let p28 : p:pos{p = 0x10000000} = assert_norm (pow2 28 = 0x10000000);
  pow2 28
inline_for_extraction let p29 : p:pos{p = 0x20000000} = assert_norm (pow2 29 = 0x20000000);
  pow2 29
inline_for_extraction let px : p:pos{p = 134217792} = assert_norm(pow2 27 + pow2 6 = 134217792);
  134217792
inline_for_extraction let py : p:pos{p = 67108928} = assert_norm(pow2 26 + pow2 6 = 67108928);
  67108928

let red_26 (s:seqelem) =
  v (Seq.index s 0) < p26 /\ v (Seq.index s 1) < p26 /\ v (Seq.index s 2) < p26 /\ v (Seq.index s 3) < p26 /\ v (Seq.index s 4) < p26

let red_27 (s:seqelem) =
  v (Seq.index s 0) < p27 /\ v (Seq.index s 1) < p27 /\ v (Seq.index s 2) < p27 /\ v (Seq.index s 3) < p27 /\ v (Seq.index s 4) < p27

let red_28 (s:seqelem) =
  v (Seq.index s 0) < p28 /\ v (Seq.index s 1) < p28 /\ v (Seq.index s 2) < p28 /\ v (Seq.index s 3) < p28 /\ v (Seq.index s 4) < p28

let red_x (s:seqelem) =
  v (Seq.index s 0) < px /\ v (Seq.index s 1) < px /\ v (Seq.index s 2) < px /\ v (Seq.index s 3) < px /\ v (Seq.index s 4) < px

let red_y (s:seqelem) =
  v (Seq.index s 0) < py /\ v (Seq.index s 1) < py /\ v (Seq.index s 2) < py /\ v (Seq.index s 3) < py /\ v (Seq.index s 4) < py

noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> log:log_t -> poly1305_state_

let seval = Hacl.Spec.Bignum.Bigint.seval

let selem (s:seqelem) : GTot Spec.elem = seval s % Spec.prime

let invariant (st:poly1305_state_) : GTot Type0 =
  let acc = (MkState?.h st) in let r = (MkState?.r st) in let log = MkState?.log st in
  seval r < pow2 130 - 5 /\  red_26 r /\ red_y acc /\ selem acc = Spec.poly log (seval r)
