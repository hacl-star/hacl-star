module EverCrypt.Hash.Incremental

open FStar.Mul

// Watch out: keep the module declarations in sync between fsti and fst
// (otherwise interleaving issues may bite).
module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module G = FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Definitions
friend Spec.Agile.Hash

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let evercrypt_hash: Hacl.Streaming.Interface.block Spec.Hash.Definitions.hash_alg =
  Hacl.Streaming.Interface.Block
    EverCrypt.Hash.state
    (fun #i h s -> EverCrypt.Hash.footprint s h)
    EverCrypt.Hash.freeable
    (fun #i h s -> EverCrypt.Hash.invariant s h)
    EverCrypt.Hash.alg_of_state
    Spec.Hash.Definitions.words_state
    (fun #i h s -> EverCrypt.Hash.repr s h)
    Hacl.Streaming.SHA256.max_input_length64
    Hacl.Hash.Definitions.hash_len
    Hacl.Hash.Definitions.block_len
    Spec.Agile.Hash.init
    Spec.Agile.Hash.update_multi
    Spec.Hash.Incremental.update_last
    Spec.Hash.PadFinish.finish
    Spec.Agile.Hash.hash
    Spec.Hash.Lemmas.update_multi_zero
    Spec.Hash.Lemmas.update_multi_associative'
    Spec.Hash.Lemmas.hash_is_hash_incremental
    (fun #i h s -> EverCrypt.Hash.invariant_loc_in_footprint s h)
    (fun #i l s h0 h1 ->
      EverCrypt.Hash.frame_invariant l s h0 h1;
      EverCrypt.Hash.frame_invariant_implies_footprint_preservation l s h0 h1)
    (fun #i l s h0 h1 -> ())
    EverCrypt.Hash.alloca
    EverCrypt.Hash.create_in
    (fun i -> EverCrypt.Hash.init #i)
    (fun i -> EverCrypt.Hash.update_multi #i)
    (fun i -> EverCrypt.Hash.update_last #i)
    (fun i -> EverCrypt.Hash.finish #i)
    (fun i -> EverCrypt.Hash.free #i)
    (fun i -> EverCrypt.Hash.copy #i)

let state_s a = F.state_s evercrypt_hash a (EverCrypt.Hash.state a)

let freeable #a = F.freeable evercrypt_hash a

let footprint_s #a = F.footprint_s evercrypt_hash a

let invariant_s #a = F.invariant_s evercrypt_hash a

let invariant_loc_in_footprint #a = F.invariant_loc_in_footprint evercrypt_hash a

let hashed #a = F.seen evercrypt_hash a

let hash_fits #a = F.seen_bounded evercrypt_hash a

let alg_of_state a = F.index_of_state evercrypt_hash a (EverCrypt.Hash.state a)

let frame_invariant #i = F.frame_invariant evercrypt_hash i

let frame_hashed #i = F.frame_seen evercrypt_hash i

let frame_freeable #a = F.frame_freeable evercrypt_hash a

let create_in a = F.create_in evercrypt_hash a (EverCrypt.Hash.state a)

let init a = F.init evercrypt_hash a (EverCrypt.Hash.state a)

let update i s data len =
  let _ = allow_inversion Spec.Agile.Hash.hash_alg in
  assert_norm (pow2 61 - 1 < pow2 64);
  assert_norm (pow2 64 < pow2 125 - 1);
  F.update evercrypt_hash i (EverCrypt.Hash.state i) s data len

/// The wrapper pattern, to ensure that the stack-allocated state is properly
/// monomorphized.
let finish_md5: finish_st MD5 = F.mk_finish evercrypt_hash MD5 (EverCrypt.Hash.state MD5)
let finish_sha1: finish_st SHA1 = F.mk_finish evercrypt_hash SHA1 (EverCrypt.Hash.state SHA1)
let finish_sha224: finish_st SHA2_224 = F.mk_finish evercrypt_hash SHA2_224 (EverCrypt.Hash.state SHA2_224)
let finish_sha256: finish_st SHA2_256 = F.mk_finish evercrypt_hash SHA2_256 (EverCrypt.Hash.state SHA2_256)
let finish_sha384: finish_st SHA2_384 = F.mk_finish evercrypt_hash SHA2_384 (EverCrypt.Hash.state SHA2_384)
let finish_sha512: finish_st SHA2_512 = F.mk_finish evercrypt_hash SHA2_512 (EverCrypt.Hash.state SHA2_512)

let finish a s dst =
  let a = alg_of_state a s in
  match a with
  | MD5 -> finish_md5 s dst
  | SHA1 -> finish_sha1 s dst
  | SHA2_224 -> finish_sha224 s dst
  | SHA2_256 -> finish_sha256 s dst
  | SHA2_384 -> finish_sha384 s dst
  | SHA2_512 -> finish_sha512 s dst

let free i = F.free evercrypt_hash i (EverCrypt.Hash.state i)
