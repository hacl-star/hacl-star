module Hacl.Bignum.AddAndMultiply

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Bignum.Fsum
open Hacl.Bignum.Fmul

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

[@"c_inline"]
val add_and_multiply:
  acc:felem ->
  block:felem{Buffer.disjoint acc block} ->
  r:felem{Buffer.disjoint acc r} ->
  Stack unit
    (requires (fun h -> live h acc /\ live h block /\ live h r
      /\ red_45 (as_seq h acc) /\ red_44 (as_seq h block) /\ red_44 (as_seq h r)))
    (ensures  (fun h0 _ h1 -> live h0 acc /\ live h0 block /\ live h0 r
      /\ red_45 (as_seq h0 acc) /\ red_44 (as_seq h0 block) /\ red_44 (as_seq h0 r)
      /\ live h1 acc /\ modifies_1 acc h0 h1
      /\ red_45 (as_seq h1 acc)
      /\ as_seq h1 acc == add_and_multiply_tot (as_seq h0 acc) (as_seq h0 block) (as_seq h0 r)
      ))
[@"c_inline"]
let add_and_multiply acc block r =
  assert_norm(pow2 63 = 0x8000000000000000);
  let h0 = ST.get() in
  lemma_fsum_def (as_seq h0 acc) (as_seq h0 block);
  Hacl.Bignum.Fsum.fsum_ acc block;
  let h1 = ST.get() in
  fmul_46_44_is_fine (as_seq h1 acc) (as_seq h1 r);
  Hacl.Bignum.Fmul.fmul acc acc r
