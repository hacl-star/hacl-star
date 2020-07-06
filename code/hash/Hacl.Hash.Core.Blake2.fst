module Hacl.Hash.Core.Blake2

open Lib.IntTypes

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

friend Spec.Agile.Hash

#push-options "--ifuel 0 --fuel 0"

noextract inline_for_extraction
val mk_init (a:hash_alg{is_blake a}) : init_st a

let mk_init a s =
  Impl.blake2_init_hash #(to_blake_alg a) #Core.M32 s (size 0)
                        (size (Spec.max_output (to_blake_alg a)));
  nat_to_extra_state a 0

noextract inline_for_extraction
val mk_alloca (a:hash_alg{is_blake a}) : init_st a -> alloca_st a

let mk_alloca a init () =
  let h0 = ST.get() in
  let (s:Core.state_p (to_blake_alg a) Core.M32) =
    Lib.Buffer.create (4ul *. Core.row_len (to_blake_alg a) Core.M32)
                      (Core.zero_element (to_blake_alg a) Core.M32) in
  let es = init s in
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  assert((as_seq h2 s, es) == Spec.Agile.Hash.init a);
  (s <: state a), es

noextract inline_for_extraction
val mk_update (a:hash_alg{is_blake a}) : update_st a

let mk_update a s totlen block =
  ST.push_frame();
  let (wv:Core.state_p (to_blake_alg a) Core.M32) =
    Lib.Buffer.create (4ul *. Core.row_len (to_blake_alg a) Core.M32)
                      (Core.zero_element (to_blake_alg a) Core.M32) in
  let totlen = extra_state_add_size_t totlen (block_len a) in
  Impl.blake2_update_block #(to_blake_alg a) #Core.M32 wv s false totlen block;
  ST.pop_frame();
  totlen

let init_blake2s = mk_init Blake2S
let alloca_blake2s = mk_alloca Blake2S (mk_init Blake2S)
let update_blake2s = mk_update Blake2S
let pad_blake2s = Hacl.Hash.PadFinish.pad Blake2S
let finish_blake2s = Hacl.Hash.PadFinish.finish Blake2S

let init_blake2b = mk_init Blake2B
let alloca_blake2b = mk_alloca Blake2B (mk_init Blake2B)
let update_blake2b = mk_update Blake2B
let pad_blake2b = Hacl.Hash.PadFinish.pad Blake2B
let finish_blake2b = Hacl.Hash.PadFinish.finish Blake2B
