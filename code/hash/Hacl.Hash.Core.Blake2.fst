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

let mk_init a m s =
  Impl.blake2_init_hash #(to_blake_alg a) #m s (size 0)
                        (size (Spec.max_output (to_blake_alg a)));
  nat_to_extra_state a 0

let mk_alloca a m init () =
  let h0 = ST.get() in
  let (s:Core.state_p (to_blake_alg a) m) =
    Lib.Buffer.create (4ul *. Core.row_len (to_blake_alg a) m)
                      (Core.zero_element (to_blake_alg a) m) in
  let es = init s in
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  assert((as_seq #a #m h2 s, es) == Spec.Agile.Hash.init a);
  (s <: state a m), es

let mk_update a m s totlen block =
  ST.push_frame();
  let (wv:Core.state_p (to_blake_alg a) m) =
    Lib.Buffer.create (4ul *. Core.row_len (to_blake_alg a) m)
                      (Core.zero_element (to_blake_alg a) m) in
  let totlen = extra_state_add_size_t totlen (block_len a) in
  Impl.blake2_update_block #(to_blake_alg a) #m wv s false totlen block;
  ST.pop_frame();
  totlen

let mk_finish a m =
  Hacl.Hash.PadFinish.finish a m

let init_blake2s_32: init_st Blake2S Core.M32 = mk_init Blake2S Core.M32
let alloca_blake2s_32: alloca_st Blake2S Core.M32 = mk_alloca Blake2S Core.M32 (mk_init Blake2S Core.M32)
let update_blake2s_32: update_st Blake2S Core.M32 = mk_update Blake2S Core.M32
let finish_blake2s_32: finish_st Blake2S Core.M32 = mk_finish Blake2S Core.M32

let init_blake2s_128: init_st Blake2S Core.M128 = mk_init Blake2S Core.M128
let alloca_blake2s_128: alloca_st Blake2S Core.M128 = mk_alloca Blake2S Core.M128 (mk_init Blake2S Core.M128)
let update_blake2s_128: update_st Blake2S Core.M128 = mk_update Blake2S Core.M128
let finish_blake2s_128: finish_st Blake2S Core.M128 = mk_finish Blake2S Core.M128

let pad_blake2s: pad_st Blake2S = Hacl.Hash.PadFinish.pad Blake2S

let init_blake2b_32: init_st Blake2B Core.M32 = mk_init Blake2B Core.M32
let alloca_blake2b_32: alloca_st Blake2B Core.M32 = mk_alloca Blake2B Core.M32 (mk_init Blake2B Core.M32)
let update_blake2b_32: update_st Blake2B Core.M32 = mk_update Blake2B Core.M32
let finish_blake2b_32: finish_st Blake2B Core.M32 = mk_finish Blake2B Core.M32

let init_blake2b_256: init_st Blake2B Core.M256 = mk_init Blake2B Core.M256
let alloca_blake2b_256: alloca_st Blake2B Core.M256 = mk_alloca Blake2B Core.M256 (mk_init Blake2B Core.M256)
let update_blake2b_256: update_st Blake2B Core.M256 = mk_update Blake2B Core.M256
let finish_blake2b_256: finish_st Blake2B Core.M256 = mk_finish Blake2B Core.M256

let pad_blake2b: pad_st Blake2B = Hacl.Hash.PadFinish.pad Blake2B
