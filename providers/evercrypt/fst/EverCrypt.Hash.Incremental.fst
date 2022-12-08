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

include Spec.Hash.Definitions
include Hacl.Hash.Definitions

open Spec.Hash.Lemmas

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
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

(* Adding some non-inlined definitions to factorize code *)
let hash_len a = Hacl.Hash.Definitions.hash_len a
let block_len a = Hacl.Hash.Definitions.block_len a

inline_for_extraction noextract
let extra_state_of_nat (a: hash_alg) (i: nat { i % U32.v (block_len a) = 0 }):
  Spec.Hash.Definitions.extra_state a
=
  if is_blake a then
    i
  else
    ()

inline_for_extraction noextract
let prev_length_of_nat (a: hash_alg) (i: nat { i % U32.v (block_len a) = 0 }):
  Spec.Hash.Incremental.prev_length_t a
=
  if is_sha3 a then
    ()
  else
    i

inline_for_extraction noextract
let evercrypt_hash : block hash_alg =
  Block
    Erased
    agile_state
    (stateful_unused hash_alg)

    (* TODO: this general max length definition shouldn't be in the MD file! *)
    Hacl.Streaming.MD.max_input_len64
    hash_len
    block_len
    block_len // No vectorization

    (fun a _ -> Spec.Agile.Hash.init a)
    (fun a s prevlen input ->
      let prevlen = extra_state_of_nat a prevlen in
      Spec.Agile.Hash.update_multi a s prevlen input)
    (fun a s prevlen input ->
      let prevlen = prev_length_of_nat a prevlen in
      Spec.Hash.Incremental.update_last a s prevlen input)
    (fun a _ s -> Spec.Hash.PadFinish.finish a s)

    (fun a _ -> Spec.Agile.Hash.hash a)

    (fun a s prevlen ->
      if is_blake a then
        Spec.Hash.Lemmas.update_multi_zero_blake a prevlen s
      else
        Spec.Hash.Lemmas.update_multi_zero a s)
    (* update_multi_associative *)
    (fun a s prevlen1 prevlen2 input1 input2 ->
       if is_blake a then
         Spec.Hash.Lemmas.update_multi_associative_blake a s prevlen1 prevlen2 input1 input2
       else
         Spec.Hash.Lemmas.update_multi_associative a s input1 input2)
    (* spec_is_incremental *)
    (fun a _ input ->
        Spec.Hash.Incremental.hash_is_hash_incremental a input)

    EverCrypt.Hash.alg_of_state
    (fun i _ -> EverCrypt.Hash.init #i)
    (fun i s prevlen blocks len -> EverCrypt.Hash.update_multi #i s prevlen blocks len)
    (fun i s prevlen last last_len ->
       EverCrypt.Hash.update_last #i s prevlen last last_len)
    (fun i _ -> EverCrypt.Hash.finish #i)

let create_in a = F.create_in evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit) ()

let init (a: G.erased hash_alg) = F.init evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit) ()

let update (i: G.erased hash_alg)
  (s:F.state evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit))
  (data: B.buffer uint8)
  (len: UInt32.t):
  Stack EverCrypt.Error.error_code
    (requires fun h0 -> F.update_pre evercrypt_hash i s data len h0)
    (ensures fun h0 e h1 ->
      match e with
      | EverCrypt.Error.Success ->
          S.length (F.seen evercrypt_hash i h0 s) + U32.v len <= U64.v (evercrypt_hash.max_input_len i) /\
          F.update_post evercrypt_hash i s data len h0 h1
      | EverCrypt.Error.MaximumLengthExceeded ->
          h0 == h1 /\
          not (S.length (F.seen evercrypt_hash i h0 s) + U32.v len <= U64.v (evercrypt_hash.max_input_len i))
      | _ -> False)
=
  match F.update evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit) s data len with
  | 0ul -> EverCrypt.Error.Success
  | 1ul -> EverCrypt.Error.MaximumLengthExceeded

inline_for_extraction noextract
let finish_st a = F.finish_st evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

/// The wrapper pattern, to ensure that the stack-allocated state is properly
/// monomorphized.
let finish_md5: finish_st MD5 = F.mk_finish evercrypt_hash MD5 (EverCrypt.Hash.state MD5) (G.erased unit)
let finish_sha1: finish_st SHA1 = F.mk_finish evercrypt_hash SHA1 (EverCrypt.Hash.state SHA1) (G.erased unit)
let finish_sha224: finish_st SHA2_224 = F.mk_finish evercrypt_hash SHA2_224 (EverCrypt.Hash.state SHA2_224) (G.erased unit)
let finish_sha256: finish_st SHA2_256 = F.mk_finish evercrypt_hash SHA2_256 (EverCrypt.Hash.state SHA2_256) (G.erased unit)
let finish_sha3_256: finish_st SHA3_256 = F.mk_finish evercrypt_hash SHA3_256 (EverCrypt.Hash.state SHA3_256) (G.erased unit)
let finish_sha384: finish_st SHA2_384 = F.mk_finish evercrypt_hash SHA2_384 (EverCrypt.Hash.state SHA2_384) (G.erased unit)
let finish_sha512: finish_st SHA2_512 = F.mk_finish evercrypt_hash SHA2_512 (EverCrypt.Hash.state SHA2_512) (G.erased unit)
let finish_blake2s: finish_st Blake2S = F.mk_finish evercrypt_hash Blake2S (EverCrypt.Hash.state Blake2S) (G.erased unit)
let finish_blake2b: finish_st Blake2B = F.mk_finish evercrypt_hash Blake2B (EverCrypt.Hash.state Blake2B) (G.erased unit)

let alg_of_state (a: G.erased hash_alg) = F.index_of_state evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

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
  | SHA3_256 -> finish_sha3_256 s dst
  | Blake2S -> finish_blake2s s dst
  | Blake2B -> finish_blake2b s dst

let free (i: G.erased hash_alg) = F.free evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit)

/// Finally, a few helpers predicates to make things easier for clients...

let state (a: hash_alg) = F.state evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

let hashed #a (h: HS.mem) (s: state a) =
  F.seen evercrypt_hash a h s
