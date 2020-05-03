module Hacl.Hash.Core.Blake2

open Lib.IntTypes

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

friend Spec.Agile.Hash

#push-options "--ifuel 0 --fuel 0"

let alloca_blake2s () =
  let h0 = ST.get() in
  let (s:Core.state_p Spec.Blake2S Core.M32) = Lib.Buffer.create 16ul (u32 0) in
  Impl.blake2_init_hash #Spec.Blake2S #Core.M32 s (size 0) (size 32);
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  s, (u64 0)

let init_blake2s s =
  Impl.blake2_init_hash #Spec.Blake2S #Core.M32 s (size 0) (size 32);
  (u64 0)

let update_blake2s s totlen block =
  ST.push_frame();
  let wv = Lib.Buffer.create 16ul (u32 0) in
  Impl.blake2_update_block #Spec.Blake2S #Core.M32 wv s false totlen block;
  assert (64 == size_block Blake2S);
  ST.pop_frame();
  totlen +. u64 64

let pad_blake2s = Hacl.Hash.PadFinish.pad Blake2S

let finish_blake2s = Hacl.Hash.PadFinish.finish Blake2S

let alloca_blake2b () =
  let h0 = ST.get() in
  let (s:Core.state_p Spec.Blake2B Core.M32) = Lib.Buffer.create 16ul (u64 0) in
  Impl.blake2_init_hash #Spec.Blake2B #Core.M32 s (size 0) (size 64);
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  s, (u64 0)

let init_blake2b s =
  Impl.blake2_init_hash #Spec.Blake2B #Core.M32 s (size 0) (size 64);
  u64 0

#push-options "--z3rlimit 20"

let update_blake2b s totlen block =
  ST.push_frame();
  let wv = Lib.Buffer.create 16ul (u64 0) in
  Impl.blake2_update_block #Spec.Blake2B #Core.M32 wv s false (to_u128 totlen) block;
  assert (128 == size_block Blake2B);
  ST.pop_frame();
  totlen +. u64 128

#pop-options

let pad_blake2b = Hacl.Hash.PadFinish.pad Blake2B

let finish_blake2b = Hacl.Hash.PadFinish.finish Blake2B
