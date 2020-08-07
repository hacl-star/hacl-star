module Hacl.Streaming.SHA2

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

open Hacl.Streaming.Interface

open Hacl.Hash.Definitions
module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

let alg = a:hash_alg{is_sha2 a}

let init_elem (a : alg) : word a =
  match a with
  | SHA2_224 | SHA2_256 -> Lib.IntTypes.u32 0
  | SHA2_384 | SHA2_512 -> Lib.IntTypes.u64 0

inline_for_extraction noextract
let state_t (a : alg) = stateful_buffer (word a) (D.impl_state_len (|a, ()|)) (init_elem a)

inline_for_extraction noextract
let update_multi_s (a : alg) () acc (prevlen : nat) input =
  fst Agile.(update_multi a (acc, ()) input)

noextract
let update_multi_zero (a : alg) () acc (prevlen : nat) :
  Lemma(update_multi_s a () acc prevlen S.empty == acc) = ()
  
#push-options "--ifuel 1"

noextract
let update_multi_associative (a : alg) () acc (prevlen1 prevlen2 : nat)
                             (input1 input2 : S.seq uint8) :
    Lemma
    (requires (
      S.length input1 % U32.v (D.block_len a) = 0 /\
      S.length input2 % U32.v (D.block_len a) = 0))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v (D.block_len a) = 0 /\
      update_multi_s a () (update_multi_s a () acc prevlen1 input1) prevlen2 input2 ==
        update_multi_s a () acc prevlen1 input)) =
  Spec.Hash.Lemmas.update_multi_associative a (acc, ()) input1 input2
#pop-options


/// This proof usually succeeds fast but we increase the rlimit for safety
#push-options "--z3rlimit 200 --ifuel 1"
inline_for_extraction noextract
let hacl_sha2 (a:alg) : block unit =
  Block
    Erased
    (state_t a)
    (stateful_unused unit)

    (fun () -> max_input_length64 a)
    (fun () -> Hacl.Hash.Definitions.hash_len a)
    (fun () -> Hacl.Hash.Definitions.block_len a)

    (fun () _ -> fst (Spec.Agile.Hash.init a))
    (fun () acc prevlen blocks -> update_multi_s a () acc prevlen blocks)
    (fun () acc prevlen input -> fst Spec.Hash.Incremental.(update_last a (acc, ()) prevlen input))
    (fun () _ acc -> Spec.Hash.PadFinish.(finish a (acc, ())))
    (fun () _ s -> Spec.Agile.Hash.(hash a s))

    (fun i h prevlen -> update_multi_zero a i h prevlen) (* update_multi_zero *)
    (fun i acc prevlen1 prevlen2 input1 input2 ->
      update_multi_associative a i acc prevlen1 prevlen2 input1 input2) (* update_multi_associative *)
    (fun _ _ input -> Spec.Hash.Incremental.hash_is_hash_incremental a input)

    (fun _ _ -> ())

    (fun _ _ s ->
      match a with
      | SHA2_224 -> Hacl.Hash.SHA2.init_224 s
      | SHA2_256 -> Hacl.Hash.SHA2.init_256 s
      | SHA2_384 -> Hacl.Hash.SHA2.init_384 s
      | SHA2_512 -> Hacl.Hash.SHA2.init_512 s)

    (fun _ s prevlen blocks len ->
      [@inline_let]
      let update_multi : update_multi_st (|a,()|) =
        match a with
        | SHA2_224 -> Hacl.Hash.SHA2.update_multi_224
        | SHA2_256 -> Hacl.Hash.SHA2.update_multi_256
        | SHA2_384 -> Hacl.Hash.SHA2.update_multi_384
        | SHA2_512 -> Hacl.Hash.SHA2.update_multi_512
      in
      update_multi s () blocks (len `U32.div` Hacl.Hash.Definitions.(block_len a)))

    (fun _ s prevlen last last_len ->
      [@inline_let]
      let update_last : update_last_st (|a,()|) =
        match a with
        | SHA2_224 -> Hacl.Hash.SHA2.update_last_224
        | SHA2_256 -> Hacl.Hash.SHA2.update_last_256
        | SHA2_384 -> Hacl.Hash.SHA2.update_last_384
        | SHA2_512 -> Hacl.Hash.SHA2.update_last_512
      in
      [@inline_let]
      let prevlen =
        match a with
        | SHA2_224 | SHA2_256 -> prevlen
        | SHA2_384 | SHA2_512 -> FStar.Int.Cast.Full.uint64_to_uint128 prevlen
      in
      update_last s () prevlen last last_len)

    (fun _ _ s dst ->
      [@inline_let]
      let finish : finish_st (|a,()|) =
        match a with
        | SHA2_224 -> Hacl.Hash.SHA2.finish_224
        | SHA2_256 -> Hacl.Hash.SHA2.finish_256
        | SHA2_384 -> Hacl.Hash.SHA2.finish_384
        | SHA2_512 -> Hacl.Hash.SHA2.finish_512
      in
      finish s () dst)
#pop-options


/// Instantiations of the streaming functor for specialized hash algorithms.
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_sha2_224 = hacl_sha2 SHA2_224
inline_for_extraction noextract
let hacl_sha2_256 = hacl_sha2 SHA2_256
inline_for_extraction noextract
let hacl_sha2_384 = hacl_sha2 SHA2_384
inline_for_extraction noextract
let hacl_sha2_512 = hacl_sha2 SHA2_512

inline_for_extraction noextract
let state_t_224 = state_t SHA2_224
inline_for_extraction noextract
let state_t_256 = state_t SHA2_256
inline_for_extraction noextract
let state_t_384 = state_t SHA2_384
inline_for_extraction noextract
let state_t_512 = state_t SHA2_512

let create_in_224 = F.create_in hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let init_224 = F.init hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)
let update_224 = F.update hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)
let finish_224 = F.mk_finish hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let free_224 = F.free hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)

let create_in_256 = F.create_in hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let init_256 = F.init hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let update_256 = F.update hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let finish_256 = F.mk_finish hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let free_256 = F.free hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)

let create_in_384 = F.create_in hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let init_384 = F.init hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)
let update_384 = F.update hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)
let finish_384 = F.mk_finish hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let free_384 = F.free hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)

let create_in_512 = F.create_in hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let init_512 = F.init hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
let update_512 = F.update hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
let finish_512 = F.mk_finish hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let free_512 = F.free hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
