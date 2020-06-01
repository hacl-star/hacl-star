module Hacl.Streaming.Blake2s_32

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module P = Hacl.Impl.Poly1305
module ST = FStar.HyperStack.ST

module Agile = Spec.Agile.Hash
module Hash = Spec.Hash.Definitions

open LowStar.BufferOps
open FStar.Mul

/// Opening a bunch of modules for Blake2
/// =======================================

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
module Core = Hacl.Impl.Blake2.Core
open Hacl.Impl.Blake2.Generic
module Impl = Hacl.Impl.Blake2.Generic
module Incr = Spec.Hash.Incremental

//open Hacl.Blake2s_32

/// An instance of the stateful type class for blake2
/// =========================================================

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
let a = Spec.Blake2S

inline_for_extraction noextract
let m = M32

inline_for_extraction noextract
let s = state_p a m

/// Small helper which facilitates inferencing implicit arguments for buffer
/// operations
inline_for_extraction noextract
let state_to_lbuffer (s : s) :
  B.lbuffer (element_t a m) (4 * U32.v (row_len a m)) =
  s

inline_for_extraction noextract
let stateful_blake2s_32: I.stateful unit =
  I.Stateful
    (fun () -> s) (* s *)
    (fun #_ _ s -> B.loc_addr_of_buffer (state_to_lbuffer s)) (* footprint *)
    (fun #_ _ s -> B.freeable (state_to_lbuffer s)) (* freeable *)
    (fun #_ h s -> B.live h (state_to_lbuffer s)) (* invariant *)
    (fun () -> Spec.state a) (* t *)
    (fun () h s -> Core.state_v h s) (* v *)
    (fun #_ _ _ -> ()) (* invariant_loc_in_footprint *)
    (fun #_ l s h0 h1 -> ()) (* frame_invariant *)
    (fun #_ _ _ _ _ -> ()) (* frame_freeable *)
    (fun () -> alloc_state a m) (* alloca *)
    (* create_in *)
    (fun () r -> B.malloc r (zero_element a m) U32.(4ul *^ row_len a m))
    (fun _ s -> B.free (state_to_lbuffer s)) (* free *)
    (* copy *)
    (fun _ src dst ->
      B.blit (state_to_lbuffer src) 0ul (state_to_lbuffer dst) 0ul
             U32.(4ul *^ row_len a m)
    )

/// Note that the key size could be parameterized 
inline_for_extraction noextract
let k (key_size : nat{0 < key_size /\ key_size <= Spec.max_key a}) =
  I.stateful_buffer uint8 (U32.uint_to_t key_size) (Lib.IntTypes.u8 0)

let max_input (key_size : nat) : nat =
  if key_size = 0 then Spec.max_limb a
  else Spec.max_limb a - Spec.size_block a

/// Interlude for spec equivalence proofs
/// =====================================

inline_for_extraction noextract
let block = (block: S.seq uint8 { S.length block = Spec.size_block a })

inline_for_extraction noextract
let key_size = Spec.max_key a

inline_for_extraction noextract
let output_length = Spec.max_output a

inline_for_extraction noextract
let output_len = U32.uint_to_t output_length

let to_hash_alg (a : Spec.alg) =
  match a with
  | Spec.Blake2S -> Hash.Blake2S
  | Spec.Blake2B -> Hash.Blake2B

//let init_s = Agile.init (to_hash_alg a)
let init_s () key = Spec.blake2_init a key_size key output_length

let update_s () acc = Agile.update (to_hash_alg a)
let update_multi_s () = Agile.update_multi (to_hash_alg a)
let update_last_s () = Spec.Hash.Incremental.update_last (to_hash_alg a)
let finish_s () = Spec.Hash.PadFinish.finish (to_hash_alg a)

inline_for_extraction noextract
let blake2s_32 : I.block unit =
  I.Block
    I.Erased (* key management *)
    
    stateful_blake2s_32 (* state *)
    (k key_size) (* key *)
    
    (fun () -> max_input (Spec.max_key a)) (* max_input_length *)
    (fun () -> output_len) (* output_len *)
    (fun () -> Core.size_block a) (* block_len *)
    
    (fun () k -> init_s () k) (* init_s *)
    (fun () s input -> update_multi_s () s input) (* update_multi_s *)
    (fun () s prevlen input -> update_last_s () s prevlen input) (* update_last_s *)
    (fun () k s -> finish_s () s) (* finish_s *)
    (fun () -> admit()) (* spec_s *)

    (fun () -> admit()) (* update_multi_zero *)
    (fun () -> admit()) (* update_multi_associative *)
    (fun () -> admit()) (* spec_is_incremental *)
    (fun u -> admit()) (* index_of_state *)

    (fun u -> admit()) (* init *)
    (fun u -> admit()) (* update_multi *)
    (fun u -> admit()) (* update_last *)
    (fun u -> admit()) (* finish *)
