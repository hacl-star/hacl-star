module Hacl.Hash.Core.Blake2

open Lib.IntTypes

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module SB2 = Spec.Blake2
module B2 = Hacl.Impl.Blake2.Generic
module CB2 = Hacl.Impl.Blake2.Core

friend Spec.Agile.Hash

#push-options "--ifuel 0 --fuel 0"

let alloca_blake2s () =
  let h0 = ST.get() in
  let (s:CB2.state_p SB2.Blake2S CB2.M32) = Lib.Buffer.create 16ul (u32 0) in
  B2.blake2_init_hash #SB2.Blake2S #CB2.M32 s (size 0) (size 32);
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  s, (u64 0)

let init_blake2s s =
  B2.blake2_init_hash #SB2.Blake2S #CB2.M32 s (size 0) (size 32);
  (u64 0)

let update_blake2s s totlen block =
  ST.push_frame();
  let wv = Lib.Buffer.create 16ul (u32 0) in
  B2.blake2_update_block #SB2.Blake2S #CB2.M32 wv s false totlen block;
  assert (64 == size_block Blake2S);
  ST.pop_frame();
  totlen +. u64 64

let alloca_blake2b () =
  let h0 = ST.get() in
  let (s:CB2.state_p SB2.Blake2B CB2.M32) = Lib.Buffer.create 16ul (u64 0) in
  B2.blake2_init_hash #SB2.Blake2B #CB2.M32 s (size 0) (size 64);
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  s, (u128 0)

let init_blake2b s =
  B2.blake2_init_hash #SB2.Blake2B #CB2.M32 s (size 0) (size 64);
  u128 0

let update_blake2b s totlen block =
  ST.push_frame();
  let wv = Lib.Buffer.create 16ul (u64 0) in
  B2.blake2_update_block #SB2.Blake2B #CB2.M32 wv s false totlen block;
  assert (128 == size_block Blake2B);
  ST.pop_frame();
  totlen +. u128 128
