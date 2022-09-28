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
  Impl.blake2_init #(to_blake_alg a) #m s (size 0)
                        (size (Spec.max_output (to_blake_alg a)));
  initial_extra_state a

let state_p_len (a:Spec.alg) (m:Core.m_spec) : size_t =
  match a,m with
  | Spec.Blake2S,Core.M128 -> 4ul
  | Spec.Blake2S,Core.M256 -> 4ul
  | Spec.Blake2B,Core.M256 -> 4ul
  | _ -> 16ul

inline_for_extraction
let state_p_to_state (#a:hash_alg{is_blake a}) (#m:Core.m_spec)
                     (s : Core.state_p (to_blake_alg a) m) :
  Tot (state (mk_impl a m)) =
  s

let mk_alloca a m init () =
  [@inline_let] let i = mk_impl a m in
  let h0 = ST.get() in
  (**) normalize_term_spec (state_p_len (to_blake_alg a) m);
  [@inline_let] let state_len = normalize_term (state_p_len (to_blake_alg a) m) in
  (**) normalize_term_spec (Core.zero_element (to_blake_alg a) m);
  [@inline_let] let zero_elem = normalize_term (Core.zero_element (to_blake_alg a) m) in
  let (s:Core.state_p (to_blake_alg a) m) = 
    Lib.Buffer.create state_len zero_elem in
  [@inline_let] let s : state i = state_p_to_state s in
  let es = init s in
  let h2 = ST.get() in
  B.modifies_only_not_unused_in (B.loc_none) h0 h2;
  assert((as_seq #i h2 s, es) == Spec.Agile.Hash.init a);
  (s <: state i), es

type state (i:impl) =
  b:B.buffer (impl_word i) { B.length b = impl_state_length i }

#push-options "--z3rlimit 50"
let mk_update a m s totlen block =
  ST.push_frame();
  (**) normalize_term_spec (state_p_len (to_blake_alg a) m);
  [@inline_let] let state_len = normalize_term (state_p_len (to_blake_alg a) m) in
  (**) normalize_term_spec (Core.zero_element (to_blake_alg a) m);
  [@inline_let] let zero_elem = normalize_term (Core.zero_element (to_blake_alg a) m) in
  let (wv:Core.state_p (to_blake_alg a) m) = 
    Lib.Buffer.create state_len zero_elem in
  [@inline_let] let wv = state_p_to_state wv in
  let totlen = extra_state_add_size_t totlen (block_len a) in
  Impl.blake2_update_block #(to_blake_alg a) #m wv s false totlen block;
  ST.pop_frame();
  totlen
#pop-options

let mk_finish a m =
  Hacl.Hash.PadFinish.finish (mk_impl a m)

let init_blake2s_32 = mk_init Blake2S Core.M32

let alloca_blake2s_32 = mk_alloca Blake2S Core.M32 (mk_init Blake2S Core.M32)

let update_blake2s_32 = mk_update Blake2S Core.M32

let finish_blake2s_32 = mk_finish Blake2S Core.M32

let init_blake2b_32 = mk_init Blake2B Core.M32

let alloca_blake2b_32 = mk_alloca Blake2B Core.M32 (mk_init Blake2B Core.M32)

let update_blake2b_32 = mk_update Blake2B Core.M32

let finish_blake2b_32 = mk_finish Blake2B Core.M32
