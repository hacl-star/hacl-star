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
let max_input_len64 a: U64.(x:t { 0 < v x /\ v x `less_than_max_input_length` a }) =
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 ->
      assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64);
      normalize_term_spec (pow2 61 - 1);
      U64.uint_to_t (normalize_term (pow2 61 - 1))
  | SHA2_384 | SHA2_512 ->
      assert_norm (pow2 64 < pow2 125 - 1);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2S ->
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2B ->
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | SHA3_256 ->
      // TODO: relax this?
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))

open Hacl.Streaming.Interface

open Hacl.Hash.Definitions
module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

inline_for_extraction noextract
let alg = a:hash_alg{not (is_blake a)}

let _: squash (inversion hash_alg) = allow_inversion hash_alg

// In this module, we re-reroute the agile hash implementation to use sha2_mb.
inline_for_extraction noextract
let is_mb = function SHA2_256 -> true | _ -> false

inline_for_extraction noextract
let word (a: alg) = if is_mb a then Hacl.Spec.SHA2.Vec.(element_t a M32) else word a

inline_for_extraction noextract
let init_elem (a : alg) : word a =
  match a with
  | MD5 | SHA1
  | SHA2_224 -> Lib.IntTypes.u32 0
  | SHA2_256 -> Hacl.Spec.SHA2.Vec.(zero_element SHA2_256 M32)
  | SHA2_384 | SHA2_512 -> Lib.IntTypes.u64 0
  | SHA3_256 -> Lib.IntTypes.u64 0

inline_for_extraction noextract
let sha2_mb_state = Lib.Buffer.lbuffer (Lib.IntVector.vec_t Lib.IntTypes.U32 1) 8ul

let _ = assert_norm (
  let open Hacl.Impl.SHA2.Core in
  let open Hacl.Spec.SHA2.Vec in
  state_t SHA2_256 M32 == sha2_mb_state)

let multiseq_hash_is_hash a: Lemma
  (requires is_mb a)
  (ensures (
    let open Hacl.Impl.SHA2.Core in
    let open Hacl.Spec.SHA2.Vec in
    multiseq (lanes a M32) (hash_length a) == Spec.Agile.Hash.bytes_hash a))
=
  let open Hacl.Impl.SHA2.Core in
  let open Hacl.Spec.SHA2.Vec in
  let open Lib.NTuple in
  let open Lib.Sequence in
  assert (lanes a M32 == 1);
  calc (==) {
    Spec.Hash.Definitions.bytes_hash a;
  (==) { _ by (FStar.Tactics.trefl ()) }
    m:S.seq uint8 { S.length m = Spec.Agile.Hash.hash_length a };
  (==) { }
    m:S.seq uint8 { (S.length m <: nat) == (Spec.Agile.Hash.hash_length a <: nat) };
  (==) { _ by (FStar.Tactics.trefl ()) }
    S.lseq uint8 (hash_length a);
  }

let multibuf_is_buf (len: Lib.IntTypes.size_t): Lemma
  (ensures Lib.MultiBuffer.multibuf 1 len == x:B.buffer uint8 { B.length x == Lib.IntTypes.v len })
=
  let open Lib.Buffer in
  calc (==) {
    Lib.MultiBuffer.multibuf 1 len;
  (==) { }
    Lib.Buffer.lbuffer uint8 len;
  (==) { _ by FStar.Tactics.(norm [ iota; zeta; delta_only [ `%lbuffer; `%lbuffer_t; `%buffer_t ]]; trefl ()) }
    x:B.buffer uint8 { B.length x == Lib.IntTypes.v len };
  }

// Big up for Aymeric who dug this one to help me make the coercion work.
unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

inline_for_extraction noextract
let lib_of_agile (#a: alg { is_mb a }) (x: Spec.Agile.Hash.bytes_hash a):
  y:Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) (Spec.Agile.Hash.hash_length a)) { x === y }
=
  multiseq_hash_is_hash a;
  coerce #Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) (Spec.Agile.Hash.hash_length a)) x

inline_for_extraction noextract
let agile_of_lib (#a: alg { is_mb a }) (y:Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) (Spec.Agile.Hash.hash_length a))):
  x: Spec.Agile.Hash.bytes_hash a { x === y }
=
  multiseq_hash_is_hash a;
  coerce #(Spec.Agile.Hash.bytes_hash a) y

inline_for_extraction noextract
let lib_of_buffer #len (x: B.buffer uint8):
  Pure (Lib.MultiBuffer.multibuf 1 len) (requires B.length x == Lib.IntTypes.v len) (ensures fun _ -> True)
=
  multibuf_is_buf len;
  coerce #(Lib.MultiBuffer.multibuf 1 len) #(x:B.buffer uint8 { B.length x == Lib.IntTypes.v len }) x

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
#push-options "--z3rlimit 400 --ifuel 1"
inline_for_extraction noextract
let hacl_md (a:alg)// : block unit =
  =
  assert_norm (word SHA3_256 == Lib.IntTypes.uint64);
  Block
    Erased
    (state_t a)
    (stateful_unused unit)

    (fun () -> max_input_len64 a)
    (fun () -> Hacl.Hash.Definitions.hash_len a)
    (fun () -> Hacl.Hash.Definitions.block_len a)
    (fun () -> Hacl.Hash.Definitions.block_len a)

    (fun () _ ->
      if is_mb a then
        Hacl.Spec.SHA2.Vec.(init a M32)
      else
        fst (Spec.Agile.Hash.init a))
    (fun () acc prevlen blocks ->
      if is_mb a then
        let open Hacl.Spec.SHA2.Vec in
        update_nblocks #a #M32 (S.length blocks) (blocks <: multiseq 1 (S.length blocks)) acc
      else
        update_multi_s a () acc prevlen blocks)
    (fun () acc prevlen input ->
      if is_mb a then
        let open Hacl.Spec.SHA2 in
        let totlen: len_t a = mk_len_t a (prevlen + S.length input) in
        Hacl.Spec.SHA2.Vec.(update_last #a #M32 totlen (S.length input) (input <: multiseq 1 (S.length input)) acc)
      else
        fst Spec.Hash.Incremental.(update_last a (acc, ()) prevlen input))
    (fun () _ acc ->
      if is_mb a then
        let _ = multiseq_hash_is_hash a in
        agile_of_lib Hacl.Spec.SHA2.Vec.(finish #a #M32 acc)
      else
        Spec.Hash.PadFinish.(finish a (acc, ())))
    (fun () _ s -> Spec.Agile.Hash.(hash a s))

    (fun i h prevlen ->
      if is_mb a then
        admit ()
      else
        update_multi_zero a i h prevlen) (* update_multi_zero *)
    (fun i acc prevlen1 prevlen2 input1 input2 ->
      if is_mb a then
        admit ()
      else
        update_multi_associative a i acc prevlen1 prevlen2 input1 input2) (* update_multi_associative *)
    (fun _ _ input ->
      if is_mb a then
        admit ()
      else
        Spec.Hash.Incremental.hash_is_hash_incremental a input)

    (fun _ _ -> ())

    (fun _ _ s ->
      match a with
      | MD5 -> Hacl.Hash.MD5.legacy_init s
      | SHA1 -> Hacl.Hash.SHA1.legacy_init s
      | SHA2_224 -> Hacl.Hash.SHA2.init_224 s
      | SHA2_256 -> Hacl.Impl.SHA2.Generic.init #SHA2_256 #Hacl.Spec.SHA2.Vec.M32 s
      | SHA2_384 -> Hacl.Hash.SHA2.init_384 s
      | SHA2_512 -> Hacl.Hash.SHA2.init_512 s
      | SHA3_256 -> Hacl.Hash.SHA3.init_256 s)

    (fun _ s prevlen blocks len ->
      if is_mb a then
        let open Hacl.Spec.SHA2.Vec in
        let open Hacl.Impl.SHA2.Generic in
        [@inline_let] let blocks_lib = lib_of_buffer #len blocks in
        admit ();
        update_nblocks #a #M32 (update #a #M32) len blocks_lib s
      else
        [@inline_let]
        let update_multi : update_multi_st (|a,()|) =
          match a with
          | MD5 -> Hacl.Hash.MD5.legacy_update_multi
          | SHA1 -> Hacl.Hash.SHA1.legacy_update_multi
          | SHA2_224 -> Hacl.Hash.SHA2.update_multi_224
          | SHA2_384 -> Hacl.Hash.SHA2.update_multi_384
          | SHA2_512 -> Hacl.Hash.SHA2.update_multi_512
          | SHA3_256 -> Hacl.Hash.SHA3.update_multi_256
        in
        update_multi s () blocks (len `U32.div` Hacl.Hash.Definitions.(block_len a)))

    (fun _ s prevlen last last_len ->
      if is_mb a then
        let open Hacl.Spec.SHA2.Vec in
        let open Hacl.Impl.SHA2.Generic in
        [@inline_let] let last_lib = lib_of_buffer #last_len last in
        update_last #a #M32 (update #a #M32) (Hacl.Hash.MD.len_add32 a prevlen last_len) last_len last_lib s
      else
        [@inline_let]
        let update_last : update_last_st (|a,()|) =
          match a with
          | MD5 -> Hacl.Hash.MD5.legacy_update_last
          | SHA1 -> Hacl.Hash.SHA1.legacy_update_last
          | SHA2_224 -> Hacl.Hash.SHA2.update_last_224
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
      if is_mb a then
        let open Hacl.Spec.SHA2.Vec in
        let open Hacl.Impl.SHA2.Generic in
        [@inline_let] let dst_lib = lib_of_buffer #32ul dst in
        finish #a #M32 s dst_lib
      else
        [@inline_let]
        let finish : finish_st (|a,()|) =
          match a with
          | MD5 -> Hacl.Hash.MD5.legacy_finish
          | SHA1 -> Hacl.Hash.SHA1.legacy_finish
          | SHA2_224 -> Hacl.Hash.SHA2.finish_224
          | SHA2_384 -> Hacl.Hash.SHA2.finish_384
          | SHA2_512 -> Hacl.Hash.SHA2.finish_512
          | SHA3_256 -> Hacl.Hash.SHA3.finish_256
        in
        finish s () dst)
#pop-options
