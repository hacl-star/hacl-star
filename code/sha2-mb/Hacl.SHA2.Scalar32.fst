module Hacl.SHA2.Scalar32

open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Spec.Agile.Hash
open Hacl.Spec.SHA2.Vec
module SpecVec = Hacl.Spec.SHA2.Vec
open Hacl.Impl.SHA2.Generic

// This module only contains internal helpers that are in support of either the
// full hash function, or the streaming functor. The top-level API is now
// exposed in Hacl.Streaming.SHA2.fst

[@CInline] let sha256_init = init #SHA2_256 #M32
[@CInline] let sha256_update = update #SHA2_256 #M32
[@CInline] let sha256_update_nblocks: update_nblocks_vec_t' SHA2_256 M32 =
  update_nblocks #SHA2_256 #M32 sha256_update
[@CInline] let sha256_update_last = update_last #SHA2_256 #M32 sha256_update
[@CInline] let sha256_finish = finish #SHA2_256 #M32

[@CInline] let sha224_init = init #SHA2_224 #M32

inline_for_extraction noextract
val sha224_update: update_vec_t SHA2_224 M32

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let sha224_update b st =
  let open Hacl.SHA2.Scalar32.Lemmas in
  let h0 = ST.get () in
  Hacl.SHA2.Scalar32.Lemmas.lemma_spec_update_vec_224_256 (as_seq_multi h0 b) (as_seq h0 st);
  sha256_update b st

[@CInline]
val sha224_update_nblocks: update_nblocks_vec_t' SHA2_224 M32
let sha224_update_nblocks len b st =
  let h0 = ST.get () in
  Hacl.SHA2.Scalar32.Lemmas.lemma_spec_update_nblocks_vec_224_256 len (as_seq_multi h0 b) (as_seq h0 st);
  sha256_update_nblocks len b st

val sha224_update_last: update_last_vec_t' SHA2_224 M32

let sha224_update_last totlen len b st =
  let open Lib.Sequence in
  let h0 = ST.get () in
  Hacl.SHA2.Scalar32.Lemmas.lemma_spec_update_last_vec_224_256
    totlen len (as_seq_multi h0 b) (as_seq h0 st);
  sha256_update_last totlen len b st

#pop-options

[@CInline] let sha224_finish = finish #SHA2_224 #M32

let sha512_init = init #SHA2_512 #M32
[@CInline] let sha512_update = update #SHA2_512 #M32
[@CInline] let sha512_update_nblocks: update_nblocks_vec_t' SHA2_512 M32 =
  update_nblocks #SHA2_512 #M32 sha512_update
[@CInline] let sha512_update_last = update_last #SHA2_512 #M32 sha512_update
[@CInline] let sha512_finish = finish #SHA2_512 #M32

[@CInline] let sha384_init = init #SHA2_384 #M32

inline_for_extraction noextract
val sha384_update: update_vec_t SHA2_384 M32

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let sha384_update b st =
  let open Hacl.SHA2.Scalar32.Lemmas in
  let h0 = ST.get () in
  Hacl.SHA2.Scalar32.Lemmas.lemma_spec_update_vec_384_512 (as_seq_multi h0 b) (as_seq h0 st);
  sha512_update b st

[@CInline]
val sha384_update_nblocks: update_nblocks_vec_t' SHA2_384 M32
let sha384_update_nblocks len b st =
  let h0 = ST.get () in
  Hacl.SHA2.Scalar32.Lemmas.lemma_spec_update_nblocks_vec_384_512 len (as_seq_multi h0 b) (as_seq h0 st);
  sha512_update_nblocks len b st

val sha384_update_last: update_last_vec_t' SHA2_384 M32

let sha384_update_last totlen len b st =
  let open Lib.Sequence in
  let h0 = ST.get () in
  Hacl.SHA2.Scalar32.Lemmas.lemma_spec_update_last_vec_384_512
    totlen len (as_seq_multi h0 b) (as_seq h0 st);
  sha512_update_last totlen len b st

#pop-options

[@CInline] let sha384_finish = finish #SHA2_384 #M32

// Big up for Aymeric who dug this one to help me make the coercion work.
unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

// Agility patterns for the streaming functor
inline_for_extraction noextract
val init: #a:sha2_alg -> init_vec_t a Hacl.Spec.SHA2.Vec.M32
let init #a =
  match a with
  | SHA2_224 -> coerce sha224_init
  | SHA2_256 -> coerce sha256_init
  | SHA2_384 -> coerce sha384_init
  | SHA2_512 -> coerce sha512_init

inline_for_extraction noextract
val update_nblocks: #a:sha2_alg -> update_nblocks_vec_t' a Hacl.Spec.SHA2.Vec.M32
let update_nblocks #a =
  match a with
  | SHA2_224 -> coerce sha224_update_nblocks
  | SHA2_256 -> coerce sha256_update_nblocks
  | SHA2_384 -> coerce sha384_update_nblocks
  | SHA2_512 -> coerce sha512_update_nblocks

inline_for_extraction noextract
val update_last: #a:sha2_alg -> update_last_vec_t' a Hacl.Spec.SHA2.Vec.M32
let update_last #a =
  match a with
  | SHA2_224 -> coerce sha224_update_last
  | SHA2_256 -> coerce sha256_update_last
  | SHA2_384 -> coerce sha384_update_last
  | SHA2_512 -> coerce sha512_update_last

inline_for_extraction noextract
val finish: #a:sha2_alg -> finish_vec_t a Hacl.Spec.SHA2.Vec.M32
let finish #a =
  match a with
  | SHA2_224 -> coerce sha224_finish
  | SHA2_256 -> coerce sha256_finish
  | SHA2_384 -> coerce sha384_finish
  | SHA2_512 -> coerce sha512_finish
