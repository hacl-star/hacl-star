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
open Hacl.Streaming.Interface

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

let agile_state: stateful hash_alg =
  Stateful
    EverCrypt.Hash.state

    (fun #i h s -> EverCrypt.Hash.footprint s h)
    EverCrypt.Hash.freeable
    (fun #i h s -> EverCrypt.Hash.invariant s h)

    Spec.Hash.Definitions.words_state
    (fun i h s -> EverCrypt.Hash.repr s h)

    (fun #i h s -> EverCrypt.Hash.invariant_loc_in_footprint s h)
    (fun #i l s h0 h1 ->
      EverCrypt.Hash.frame_invariant l s h0 h1;
      EverCrypt.Hash.frame_invariant_implies_footprint_preservation l s h0 h1)
    (fun #i l s h0 h1 -> ())
    EverCrypt.Hash.alloca
    EverCrypt.Hash.create_in
    (fun i -> EverCrypt.Hash.free #i)
    (fun i -> EverCrypt.Hash.copy #i)

inline_for_extraction noextract
let evercrypt_hash: block hash_alg =
  Block
    Erased
    agile_state
    (stateful_unused hash_alg)

    Hacl.Streaming.SHA2_256.max_input_length64
    Hacl.Hash.Definitions.hash_len
    Hacl.Hash.Definitions.block_len

    (fun a _ -> Spec.Agile.Hash.init a)
    Spec.Agile.Hash.update_multi
    Spec.Hash.Incremental.update_last
    (fun a _ -> Spec.Hash.PadFinish.finish a)

    (fun a _ -> Spec.Agile.Hash.hash a)

    Spec.Hash.Lemmas.update_multi_zero
    (fun _ _ _ _ -> ()) // relying on the pattern in Hacl.Streaming.SHA256 here
    (fun a _ -> Spec.Hash.Lemmas.hash_is_hash_incremental a)

    EverCrypt.Hash.alg_of_state
    (fun i _ -> EverCrypt.Hash.init #i)
    (fun i -> EverCrypt.Hash.update_multi #i)
    (fun i -> EverCrypt.Hash.update_last #i)
    (fun i _ -> EverCrypt.Hash.finish #i)

let create_in a = F.create_in evercrypt_hash a (EverCrypt.Hash.state a)

let init (a: G.erased hash_alg) = F.init evercrypt_hash a (EverCrypt.Hash.state a) ()

let update (i: G.erased hash_alg) =
  let _ = allow_inversion Spec.Agile.Hash.hash_alg in
  assert_norm (pow2 61 - 1 < pow2 64);
  assert_norm (pow2 64 < pow2 125 - 1);
  F.update evercrypt_hash i (EverCrypt.Hash.state i)

let finish_st a = F.finish_st evercrypt_hash a (EverCrypt.Hash.state a)

/// The wrapper pattern, to ensure that the stack-allocated state is properly
/// monomorphized.
let finish_md5: finish_st MD5 = F.mk_finish evercrypt_hash MD5 (EverCrypt.Hash.state MD5)
let finish_sha1: finish_st SHA1 = F.mk_finish evercrypt_hash SHA1 (EverCrypt.Hash.state SHA1)
let finish_sha224: finish_st SHA2_224 = F.mk_finish evercrypt_hash SHA2_224 (EverCrypt.Hash.state SHA2_224)
let finish_sha256: finish_st SHA2_256 = F.mk_finish evercrypt_hash SHA2_256 (EverCrypt.Hash.state SHA2_256)
let finish_sha384: finish_st SHA2_384 = F.mk_finish evercrypt_hash SHA2_384 (EverCrypt.Hash.state SHA2_384)
let finish_sha512: finish_st SHA2_512 = F.mk_finish evercrypt_hash SHA2_512 (EverCrypt.Hash.state SHA2_512)

let alg_of_state (a: G.erased hash_alg) = F.index_of_state evercrypt_hash a (EverCrypt.Hash.state a)

val finish: a:G.erased hash_alg -> finish_st a
let finish a s dst =
  let a = alg_of_state a s in
  match a with
  | MD5 -> finish_md5 s dst
  | SHA1 -> finish_sha1 s dst
  | SHA2_224 -> finish_sha224 s dst
  | SHA2_256 -> finish_sha256 s dst
  | SHA2_384 -> finish_sha384 s dst
  | SHA2_512 -> finish_sha512 s dst

let free (i: G.erased hash_alg) = F.free evercrypt_hash i (EverCrypt.Hash.state i)

/// Finally, a few helpers predicates to make things easier for clients...

let state (a: hash_alg) = F.state evercrypt_hash a (EverCrypt.Hash.state a)

let hashed #a (h: HS.mem) (s: state a) =
  F.seen evercrypt_hash a h s
