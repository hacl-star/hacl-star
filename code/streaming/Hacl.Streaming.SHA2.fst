module Hacl.Streaming.SHA2

// NOTE: if you get errors trying to load this file in interactive mode because
// a tactic fails in Hacl.Streaming.MD (even though Hacl.Streaming.MD works
// totally fine in interactive mode!!), run:
//     NODEPEND=1 make -j obj/Hacl.Streaming.MD.fst.checked

open FStar.HyperStack.ST

/// A streaming version of MD-based hashes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

open Spec.Hash.Definitions
open Hacl.Streaming.Interface
open Hacl.Streaming.MD

/// Instantiations of the streaming functor for specialized SHA2 algorithms.
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_sha2_224 = hacl_md SHA2_224
inline_for_extraction noextract
let hacl_sha2_256 = hacl_md SHA2_256
inline_for_extraction noextract
let hacl_sha2_384 = hacl_md SHA2_384
inline_for_extraction noextract
let hacl_sha2_512 = hacl_md SHA2_512

inline_for_extraction noextract
let state_t_224 = state_t SHA2_224
inline_for_extraction noextract
let state_t_256 = state_t SHA2_256
inline_for_extraction noextract
let state_t_384 = state_t SHA2_384
inline_for_extraction noextract
let state_t_512 = state_t SHA2_512

/// Type abbreviations - for pretty code generation
let state_sha2_224 = F.state_s hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let state_sha2_256 = F.state_s hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let state_sha2_384 = F.state_s hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let state_sha2_512 = F.state_s hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)

open Lib.Buffer
open Lib.IntTypes

// Slightly rewritten spec to remove any mention of multibuffer-isms
inline_for_extraction noextract
let hash_t (a: sha2_alg) =
  dst:lbuffer uint8 (Hacl.Hash.Definitions.hash_len a) -> input_len:size_t -> input:lbuffer uint8 input_len ->
    Stack unit
    (requires fun h0 -> v input_len `less_than_max_input_length` a /\
      live h0 input /\ live h0 dst /\ disjoint dst input)
    (ensures  fun h0 _ h1 -> modifies (loc dst) h0 h1 /\
      as_seq h1 dst == Spec.Agile.Hash.hash a (as_seq h0 input))

inline_for_extraction noextract
let alloca_224 = F.alloca hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let create_in_224 = F.create_in hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let init_224 = F.init hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update_224 = F.update hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)
let finish_224 = F.mk_finish hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let free_224 = F.free hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)

open Lib.NTuple
open Lib.MultiBuffer
open Hacl.Spec.SHA2.Vec
open Hacl.SHA2.Scalar32
open Hacl.Impl.SHA2.Generic
module ST = FStar.HyperStack.ST

val sha224: hash_t SHA2_224
let sha224 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_224 #M32 sha224_init sha224_update_nblocks sha224_update_last sha224_finish rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_224 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)

inline_for_extraction noextract
let alloca_256 = F.alloca hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let create_in_256 = F.create_in hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let init_256 = F.init hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update_256 = F.update hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let finish_256 = F.mk_finish hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let free_256 = F.free hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)

val sha256: hash_t SHA2_256
let sha256 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_256 #M32 sha256_init sha256_update_nblocks sha256_update_last sha256_finish rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_256 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)

inline_for_extraction noextract
let alloca_384 = F.alloca hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let create_in_384 = F.create_in hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let init_384 = F.init hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update_384 = F.update hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)
let finish_384 = F.mk_finish hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let free_384 = F.free hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)

val sha384: hash_t SHA2_384
let sha384 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_384 #M32 sha384_init sha384_update_nblocks sha384_update_last sha384_finish rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_384 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)

inline_for_extraction noextract
let alloca_512 = F.alloca hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let create_in_512 = F.create_in hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let init_512 = F.init hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update_512 = F.update hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
let finish_512 = F.mk_finish hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let free_512 = F.free hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)

val sha512: hash_t SHA2_512
let sha512 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_512 #M32 sha512_init sha512_update_nblocks sha512_update_last sha512_finish rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_512 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)
