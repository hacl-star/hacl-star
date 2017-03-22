module Hacl.Spec.Poly1305_64.Lemmas1

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Endianness

open Spec.Poly1305
open Spec.Chacha20Poly1305


module U8 = FStar.UInt8


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

module U32 = FStar.UInt32

val encode_bytes_append: len:nat -> s:Seq.seq U8.t -> w:word -> Lemma
  (requires (0 < Seq.length w /\ Seq.length s == len /\ len % 16 == 0))
  (ensures  (Seq.equal (encode_bytes ((Seq.append s w)))
                      (Seq.cons (w) (encode_bytes (s)))))
  (decreases (Seq.length s))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_encode_bytes_append: s1:Seq.seq U8.t -> s2:Seq.seq U8.t -> l:nat{l * 16 = length s1} ->
  Lemma (requires (True))
        (ensures (encode_bytes (s1 @| s2) == encode_bytes s2 @| encode_bytes s1))
        (decreases (l))
