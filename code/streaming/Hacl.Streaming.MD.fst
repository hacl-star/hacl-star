module Hacl.Streaming.MD

open FStar.HyperStack.ST

/// This file is poorly named. It contains a generic type class instantiation
/// for the streaming functor for any algorithm that fits within the agile hash
/// infrastructure.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

module ST = FStar.HyperStack.ST

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
let max_input_length64 a: x:nat { 0 < x /\ x < pow2 64 /\ x `less_than_max_input_length` a } =
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64); pow2 61 - 1
  | SHA2_384 | SHA2_512 -> assert_norm (pow2 64 < pow2 125 - 1); pow2 64 - 1
  | Blake2S -> pow2 64 - 1
  | Blake2B -> assert_norm (pow2 64 < pow2 128); pow2 64 - 1
  | SHA3_256 -> pow2 64 - 1 // TODO: relax this?

open Hacl.Streaming.Interface

open Hacl.Hash.Definitions
module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

inline_for_extraction noextract
let alg = a:hash_alg{not (is_blake a)}

let _: squash (inversion hash_alg) = allow_inversion hash_alg

inline_for_extraction noextract
let init_elem (a : alg) : word a =
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> Lib.IntTypes.u32 0
  | SHA2_384 | SHA2_512 -> Lib.IntTypes.u64 0
  | SHA3_256 -> Lib.IntTypes.u64 0

inline_for_extraction noextract
let state_t (a : alg) = stateful_buffer (word a) (D.impl_state_len (|a, ()|)) (init_elem a)

inline_for_extraction noextract
let update_multi_s (a : alg) () acc (prevlen : nat) input =
  fst Agile.(update_multi a (acc, ()) input)

noextract
let update_multi_zero (a : alg) () acc (prevlen : nat) :
  Lemma(update_multi_s a () acc prevlen S.empty == acc) = ()

#push-options "--ifuel 1"

// TODO: this is the third copy of this lemma!! why?!
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
let hacl_md (a:alg)// : block unit =
  =
  assert_norm (word SHA3_256 == Lib.IntTypes.uint64);
  Block
    Erased
    (state_t a)
    (stateful_unused unit)

    (fun () -> max_input_length64 a)
    (fun () -> Hacl.Hash.Definitions.hash_len a)
    (fun () -> Hacl.Hash.Definitions.block_len a)
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
      | MD5 -> Hacl.Hash.MD5.legacy_init s
      | SHA1 -> Hacl.Hash.SHA1.legacy_init s
      | SHA2_224 -> Hacl.Hash.SHA2.init_224 s
      | SHA2_256 -> Hacl.Hash.SHA2.init_256 s
      | SHA2_384 -> Hacl.Hash.SHA2.init_384 s
      | SHA2_512 -> Hacl.Hash.SHA2.init_512 s
      | SHA3_256 -> Hacl.Hash.SHA3.init_256 s)

    (fun _ s prevlen blocks len ->
      [@inline_let]
      let update_multi : update_multi_st (|a,()|) =
        match a with
        | MD5 -> Hacl.Hash.MD5.legacy_update_multi
        | SHA1 -> Hacl.Hash.SHA1.legacy_update_multi
        | SHA2_224 -> Hacl.Hash.SHA2.update_multi_224
        | SHA2_256 -> Hacl.Hash.SHA2.update_multi_256
        | SHA2_384 -> Hacl.Hash.SHA2.update_multi_384
        | SHA2_512 -> Hacl.Hash.SHA2.update_multi_512
        | SHA3_256 -> Hacl.Hash.SHA3.update_multi_256
      in
      update_multi s () blocks (len `U32.div` Hacl.Hash.Definitions.(block_len a)))

    (fun _ s prevlen last last_len ->
      [@inline_let]
      let update_last : update_last_st (|a,()|) =
        match a with
        | MD5 -> Hacl.Hash.MD5.legacy_update_last
        | SHA1 -> Hacl.Hash.SHA1.legacy_update_last
        | SHA2_224 -> Hacl.Hash.SHA2.update_last_224
        | SHA2_256 -> Hacl.Hash.SHA2.update_last_256
        | SHA2_384 -> Hacl.Hash.SHA2.update_last_384
        | SHA2_512 -> Hacl.Hash.SHA2.update_last_512
        | SHA3_256 -> Hacl.Hash.SHA3.update_last_256
      in
      [@inline_let]
      let prevlen =
        match a with
        | MD5 | SHA1
        | SHA2_224 | SHA2_256 -> prevlen
        | SHA2_384 | SHA2_512 -> FStar.Int.Cast.Full.uint64_to_uint128 prevlen
        | SHA3_256 -> ()
      in
      update_last s () prevlen last last_len)

    (fun _ _ s dst ->
      [@inline_let]
      let finish : finish_st (|a,()|) =
        match a with
        | MD5 -> Hacl.Hash.MD5.legacy_finish
        | SHA1 -> Hacl.Hash.SHA1.legacy_finish
        | SHA2_224 -> Hacl.Hash.SHA2.finish_224
        | SHA2_256 -> Hacl.Hash.SHA2.finish_256
        | SHA2_384 -> Hacl.Hash.SHA2.finish_384
        | SHA2_512 -> Hacl.Hash.SHA2.finish_512
        | SHA3_256 -> Hacl.Hash.SHA3.finish_256
      in
      finish s () dst)
#pop-options
