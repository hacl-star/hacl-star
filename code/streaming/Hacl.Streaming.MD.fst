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

open Hacl.Streaming.Block
module Block = Hacl.Streaming.Block

open Hacl.Hash.Definitions
module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

let _: squash (inversion hash_alg) = allow_inversion hash_alg

inline_for_extraction noextract
let alg = md_alg

inline_for_extraction noextract
let init_elem (a : alg) : word a =
  match a with
  | MD5 | SHA1 | SHA2_256 | SHA2_224 -> Lib.IntTypes.u32 0
  | SHA2_384 | SHA2_512 -> Lib.IntTypes.u64 0

inline_for_extraction noextract
let state_len (a : alg) = D.impl_state_len (|a, ()|)

inline_for_extraction noextract
let state_t (a : alg) = Stateful.index_buffer (word a) (state_len a)

inline_for_extraction noextract
let update_multi_s (a : alg) acc (prevlen : nat) input =
  Agile.(update_multi a acc () input)

noextract
let update_multi_zero (a : alg) acc (prevlen : nat) :
  Lemma(update_multi_s a acc prevlen S.empty == acc) = Spec.Hash.Lemmas.update_multi_zero a acc

#push-options "--ifuel 1"

// TODO: this is the third copy of this lemma!! why?!
noextract
let update_multi_associative (a : alg) acc (prevlen1 prevlen2 : nat)
                             (input1 input2 : S.seq uint8) :
    Lemma
    (requires (
      S.length input1 % U32.v (D.block_len a) = 0 /\
      S.length input2 % U32.v (D.block_len a) = 0))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v (D.block_len a) = 0 /\
      update_multi_s a (update_multi_s a acc prevlen1 input1) prevlen2 input2 ==
        update_multi_s a acc prevlen1 input)) =
  Spec.Hash.Lemmas.update_multi_associative a acc input1 input2
#pop-options

inline_for_extraction noextract
let md_prevlen (a: alg) (len: D.(len: U64.t { U64.v len % U32.v (block_len a) = 0 })): D.prev_len_t a =
  if a = SHA2_384 || a = SHA2_512 then FStar.Int.Cast.Full.uint64_to_uint128 len else len

/// This proof usually succeeds fast but we increase the rlimit for safety
#push-options "--z3rlimit 500"
inline_for_extraction noextract
let hacl_md_index (a:alg) : Block.index = {
  km = Erased;
  state = state_t a;
  key = Stateful.index_unused unit;

  output_length_t = unit;

  max_input_len = max_input_len64 a;
  output_length = (fun () -> Spec.Hash.Definitions.hash_length a);
  block_len = Hacl.Hash.Definitions.block_len a;
  blocks_state_len = Hacl.Hash.Definitions.block_len a;
  init_input_len = 0ul;

  init_input_s = (fun _k -> S.empty);
  init_s = (fun _ -> Spec.Agile.Hash.init a);
  update_multi_s = (fun acc prevlen blocks -> update_multi_s a acc prevlen blocks);
  update_last_s = (fun acc prevlen input -> Spec.Hash.Incremental.(update_last a acc prevlen input));
  finish_s = (fun _ acc () -> Spec.Agile.Hash.(finish a acc ()));

  spec_s = (fun _ s () -> Spec.Agile.Hash.(hash a s));

  update_multi_zero = (fun h prevlen -> update_multi_zero a h prevlen);

  update_multi_associative =
    (fun acc prevlen1 prevlen2 input1 input2 ->
     update_multi_associative a acc prevlen1 prevlen2 input1 input2);

  spec_is_incremental =
    (fun key input () ->
      let input1 = S.append S.empty input in
      assert (S.equal input1 input);
      Spec.Hash.Incremental.hash_is_hash_incremental' a input ());
}
#pop-options

inline_for_extraction noextract
let hacl_md_init (a : alg) : Block.init_st (hacl_md_index a) = fun _ _ s ->
  match a with
  | MD5 -> Hacl.Hash.MD5.legacy_init s
  | SHA1 -> Hacl.Hash.SHA1.legacy_init s
  | SHA2_224 -> Hacl.Hash.SHA2.init_224 s
  | SHA2_256 -> Hacl.Hash.SHA2.init_256 s
  | SHA2_384 -> Hacl.Hash.SHA2.init_384 s
  | SHA2_512 -> Hacl.Hash.SHA2.init_512 s

inline_for_extraction noextract
let hacl_md_update_multi (a : alg) : Block.update_multi_st (hacl_md_index a) = fun s prevlen blocks len ->
  [@inline_let]
  let update_multi : update_multi_st (|a,()|) =
    match a with
    | MD5 -> Hacl.Hash.MD5.legacy_update_multi
    | SHA1 -> Hacl.Hash.SHA1.legacy_update_multi
    | SHA2_224 -> Hacl.Hash.SHA2.update_multi_224
    | SHA2_256 -> Hacl.Hash.SHA2.update_multi_256
    | SHA2_384 -> Hacl.Hash.SHA2.update_multi_384
    | SHA2_512 -> Hacl.Hash.SHA2.update_multi_512
  in
  update_multi s () blocks (len `U32.div` Hacl.Hash.Definitions.(block_len a))

inline_for_extraction noextract
let hacl_md_update_last (a : alg) : Block.update_last_st (hacl_md_index a) = fun s prevlen last last_len ->
  [@inline_let]
  let update_last : update_last_st (|a,()|) =
    match a with
    | MD5 -> Hacl.Hash.MD5.legacy_update_last
    | SHA1 -> Hacl.Hash.SHA1.legacy_update_last
    | SHA2_224 -> Hacl.Hash.SHA2.update_last_224
    | SHA2_256 -> Hacl.Hash.SHA2.update_last_256
    | SHA2_384 -> Hacl.Hash.SHA2.update_last_384
    | SHA2_512 -> Hacl.Hash.SHA2.update_last_512
  in
  update_last s (md_prevlen a prevlen) last last_len

inline_for_extraction noextract
let hacl_md_finish (a : alg) : Block.finish_st (hacl_md_index a) = fun _ s dst _ ->
  [@inline_let]
  let finish : finish_st (|a,()|) =
    match a with
    | MD5 -> Hacl.Hash.MD5.legacy_finish
    | SHA1 -> Hacl.Hash.SHA1.legacy_finish
    | SHA2_224 -> Hacl.Hash.SHA2.finish_224
    | SHA2_256 -> Hacl.Hash.SHA2.finish_256
    | SHA2_384 -> Hacl.Hash.SHA2.finish_384
    | SHA2_512 -> Hacl.Hash.SHA2.finish_512
  in
  finish s dst

// Putting some type abbreviations here, so that they appear in a separate file that can then be included by all streaming algorithms, rather than having e.g. SHA1 depend on e.g. MD5

// Could be anything that's 32-bit
inline_for_extraction noextract
let hacl_sha2_256 = hacl_md_index SHA2_256

let state_32 = F.state_s hacl_sha2_256 (state_t SHA2_256).s (G.erased unit)

inline_for_extraction noextract
let hacl_sha2_512 = hacl_md_index SHA2_512

let state_64 = F.state_s hacl_sha2_512 (state_t SHA2_512).s (G.erased unit)

/// Helpers
inline_for_extraction noextract
let mk_alloca (a : alg) : F.alloca_st (hacl_md_index a) =
  F.mk_alloca #(hacl_md_index a)
    (hacl_md_init a)
    (Stateful.copy_unused #(word a))
    (Stateful.alloca_unused #(word a))
    (Stateful.alloca_buffer #(word a) #(state_len a) #(init_elem a))

inline_for_extraction noextract
let mk_create_in (a : alg) : F.create_in_st (hacl_md_index a) =
  F.mk_create_in #(hacl_md_index a)
    (hacl_md_init a)
    (Stateful.copy_unused #(word a))
    (Stateful.create_in_unused #(word a))
    (Stateful.create_in_buffer #(word a) #(state_len a) #(init_elem a))

inline_for_extraction noextract
let mk_init (a : alg) : F.init_st (hacl_md_index a) =
  F.mk_init #(hacl_md_index a)
    (Stateful.copy_unused #(word a))
    (hacl_md_init a)

inline_for_extraction noextract
let mk_update (a : alg) : F.update_st (hacl_md_index a) =
  F.mk_update #(hacl_md_index a) (hacl_md_update_multi a)

inline_for_extraction noextract
let mk_finish (a : alg) : F.finish_st (hacl_md_index a) =
  F.mk_finish #(hacl_md_index a)
    (hacl_md_finish a)
    (hacl_md_update_last a)
    (hacl_md_update_multi a)
    (Stateful.copy_buffer #(word a) #(state_len a))
    (Stateful.alloca_buffer #(word a) #(state_len a) #(init_elem a))

inline_for_extraction noextract
let mk_free (a : alg) : F.free_st (hacl_md_index a) =
  F.mk_free #(hacl_md_index a)
    (Stateful.free_buffer #(word a) #(state_len a))
    (Stateful.free_unused #(word a))

inline_for_extraction noextract
let mk_copy (a : alg) : F.copy_st (hacl_md_index a) =
  F.mk_copy #(hacl_md_index a)
    (Stateful.copy_unused #(word a))
    (Stateful.create_in_unused #(word a))
    (Stateful.copy_buffer #(word a) #(state_len a))
    (Stateful.create_in_buffer #(word a) #(state_len a) #(init_elem a))
