module Hacl.Streaming.SHA2_256

open FStar.HyperStack.ST

/// A streaming version of SHA256.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

open Spec.Hash.Definitions

/// Maximum input length, but fitting on a 64-bit integer (since the streaming
/// module doesn't bother taking into account lengths that are greater than
/// that). The comment previously was:
///
/// Note that we keep the total length at run-time, on 64 bits, but require that
/// it abides by the size requirements for the smaller hashes -- we're not
/// interested at this stage in having an agile type for lengths that would be
/// up to 2^125 for SHA384/512.

inline_for_extraction noextract
let max_input_length64 a: x:nat { 0 < x /\ x < pow2 64 /\ x <= max_input_length a } =
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64); pow2 61 - 1
  | SHA2_384 | SHA2_512 -> assert_norm (pow2 64 < pow2 125 - 1); pow2 64 - 1
  | Blake2S -> pow2 64 - 1
  | Blake2B -> assert_norm (pow2 64 < pow2 128); pow2 64 - 1

// Local redefinition to have the shape desired by the type class.
let update_multi_associative (i: hash_alg) =
  Lib.UpdateMulti.update_multi_associative (block_length i) (Spec.Agile.Hash.update i)

open Hacl.Streaming.Interface

inline_for_extraction noextract
let b = stateful_buffer (word SHA2_256) (Hacl.Hash.Definitions.hash_word_len SHA2_256) (Lib.IntTypes.u32 0)

#push-options "--ifuel 1"

inline_for_extraction noextract
let hacl_sha2_256: block unit =
  Block
    Erased
    b
    (stateful_unused unit)

    (fun () -> max_input_length64 SHA2_256)
    (fun () -> Hacl.Hash.Definitions.hash_len SHA2_256)
    (fun () -> Hacl.Hash.Definitions.block_len SHA2_256)

    (fun () _ -> fst (Spec.Agile.Hash.(init SHA2_256)))
    (fun () acc blocks -> fst Spec.Agile.Hash.(update_multi SHA2_256 (acc, ()) blocks))
    (fun () acc prevlen input -> fst Spec.Hash.Incremental.(update_last SHA2_256 (acc, ()) prevlen input))
    (fun () _ acc -> Spec.Hash.PadFinish.(finish SHA2_256 (acc, ())))
    (fun () _ s -> Spec.Agile.Hash.(hash SHA2_256 s))

    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (fun _ _ input -> Spec.Hash.Incremental.hash_is_hash_incremental SHA2_256 input)

    (fun _ _ -> ())
    (fun _ _ s -> Hacl.Hash.SHA2.init_256 s)
    (fun _ s blocks len -> Hacl.Hash.SHA2.update_multi_256 s () blocks (len `U32.div` Hacl.Hash.Definitions.(block_len SHA2_256)))
    (fun _ s last total_len ->
      [@inline_let]
      let block_len64 = 64UL in
      assert_norm (U64.v block_len64 == block_length SHA2_256);
      let last_len: len_t SHA2_256 = U64.(total_len `rem` block_len64) in
      let prev_len = U64.(total_len `sub` last_len) in
      let last_len = FStar.Int.Cast.Full.uint64_to_uint32 last_len in
      assert (U64.v prev_len % block_length SHA2_256 = 0);
      Hacl.Hash.SHA2.update_last_256 s () prev_len last last_len)
    (fun _ _ s dst -> Hacl.Hash.SHA2.finish_256 s () dst)

/// An instantiation of the streaming functor for a specialized hash algorithm.
///
/// Some remarks:
///
/// - rather than copy/pasting the type class above, we could make it generic
///   over the hash algorithm, but still get specialized instances
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

let create_in = F.create_in hacl_sha2_256 () (b.s ()) (G.erased unit)
let init = F.init hacl_sha2_256 (G.hide ()) (b.s ()) (G.erased unit)
let update = F.update hacl_sha2_256 (G.hide ()) (b.s ()) (G.erased unit)
let finish = F.mk_finish hacl_sha2_256 () (b.s ()) (G.erased unit)
let free = F.free hacl_sha2_256 (G.hide ()) (b.s ()) (G.erased unit)
