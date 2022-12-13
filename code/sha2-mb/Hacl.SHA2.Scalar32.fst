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

let state_spec_v_extensionality (a : hash_alg { is_sha2 a })
  (acc1: Hacl.Spec.SHA2.Vec.(state_spec a M32))
  (acc2: Hacl.Spec.SHA2.Vec.(state_spec a M32)) :
  Lemma
  (requires (let open Hacl.Spec.SHA2.Vec in
     Lib.Sequence.index (state_spec_v acc1) 0 ==
     Lib.Sequence.index (state_spec_v acc2) 0))
  (ensures acc1 == acc2) =

  let open Lib.Sequence in
  let open Lib.IntVector in
  let open Hacl.Spec.SHA2.Vec in
  allow_inversion hash_alg;
  let acc1_s = (state_spec_v acc1).[0] <: lseq (word a) 8 in
  let acc2_s = (state_spec_v acc2).[0] <: lseq (word a) 8 in

  let aux (i:nat{i < 8}) : Lemma (acc1.[i] == acc2.[i]) =
    assert (index (vec_v acc1.[i]) 0 == index #(word a) #8 acc1_s i);
    assert (index (vec_v acc2.[i]) 0 == index #(word a) #8 acc2_s i);
    assert (index (vec_v acc1.[i]) 0 == index (vec_v acc2.[i]) 0);
    eq_intro (vec_v acc1.[i]) (vec_v acc2.[i]);
    vecv_extensionality acc1.[i] acc2.[i] in

  Classical.forall_intro aux;
  eq_intro acc1 acc2

let hacl_spec_update_224_256 b st: Lemma (ensures
  Hacl.Spec.SHA2.update SHA2_256 b st ==
  Hacl.Spec.SHA2.update SHA2_224 b st)
=
  calc (==) {
    Hacl.Spec.SHA2.update SHA2_256 b st;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_256 b st }
    Spec.Agile.Hash.update SHA2_256 st b;
  (==) { Spec.SHA2.Lemmas.update_224_256' st b }
    Spec.Agile.Hash.update SHA2_224 st b;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_224 b st }
    Hacl.Spec.SHA2.update SHA2_224 b st;
  }

inline_for_extraction noextract
val sha224_update: update_vec_t SHA2_224 M32

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let sha224_update b st =
  let open Lib.Sequence in
  let h0 = ST.get () in
  sha256_update b st;
  let h1 = ST.get () in
  begin
    let st0: lseq (element_t SHA2_256 M32) 8 = as_seq h0 st in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_256 in
    let b0: multiblock_spec SHA2_256 M32 = as_seq_multi h0 b in
    let st1: lseq (element_t SHA2_256 M32) 8 = as_seq h1 st in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_256 in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update #SHA2_256 b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_lemma_l #SHA2_256 #M32 b0 st0 0 }
      Hacl.Spec.SHA2.update SHA2_256 b0.(|0|) st0_m32;
    (==) { hacl_spec_update_224_256 b0.(|0|) st0_m32 }
      Hacl.Spec.SHA2.update SHA2_224 b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_lemma_l #SHA2_224 #M32 b0 st0 0 }
      (state_spec_v #SHA2_224 #M32 (SpecVec.update #SHA2_224 b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_256
      (SpecVec.update #SHA2_256 b0 st0)
      (SpecVec.update #SHA2_224 #M32 b0 st0)
  end

[@CInline]
val sha224_update_nblocks: update_nblocks_vec_t' SHA2_224 M32
let sha224_update_nblocks len b st =
  let open Lib.Sequence in
  let h0 = ST.get () in
  sha256_update_nblocks len b st;
  let h1 = ST.get () in
  begin
    let st0: lseq (element_t SHA2_256 M32) 8 = as_seq h0 st in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_256 in
    let b0: multiseq (lanes SHA2_256 M32) (v len) = as_seq_multi h0 b in
    let b0_m32' = Seq.slice b0.(|0|) 0 (Seq.length b0.(|0|) - Seq.length b0.(|0|) % block_length SHA2_256) in
    let st1: lseq (element_t SHA2_256 M32) 8 = as_seq h1 st in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_256 in
    Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_256 len;
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update_nblocks #SHA2_256 (v len) b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #SHA2_256 #M32 (v len) b0 st0 0 }
      Hacl.Spec.SHA2.update_nblocks SHA2_256 (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi' SHA2_256 (v len) b0.(|0|) st0_m32 }
      Lib.Sequence.repeat_blocks_multi (block_length SHA2_256) b0_m32' (Hacl.Spec.SHA2.update SHA2_256) st0_m32;
    (==) {
      FStar.Classical.forall_intro_2 hacl_spec_update_224_256;
      Hacl.Spec.SHA2.EquivScalar.repeat_blocks_multi_extensionality #uint8 #(words_state SHA2_256) (block_length SHA2_256) b0_m32'
        (Hacl.Spec.SHA2.update SHA2_256)
        (Hacl.Spec.SHA2.update SHA2_224)
        st0_m32
    }
      Lib.Sequence.repeat_blocks_multi #uint8 #(words_state SHA2_256) (block_length SHA2_256) b0_m32' (Hacl.Spec.SHA2.update SHA2_224) st0_m32;
    (==) { }
      Lib.Sequence.repeat_blocks_multi #uint8 #(words_state SHA2_224) (block_length SHA2_224) b0_m32' (Hacl.Spec.SHA2.update SHA2_224) (st0_m32 <: words_state SHA2_224);
    (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi' SHA2_224 (v len) b0.(|0|) st0_m32 }
      Hacl.Spec.SHA2.update_nblocks SHA2_224 (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #SHA2_224 #M32 (v len) b0 st0 0 }
      (state_spec_v #SHA2_224 #M32 (SpecVec.update_nblocks #SHA2_224 (v len) b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_256
      (SpecVec.update_nblocks #SHA2_256 (v len) b0 st0)
      (SpecVec.update_nblocks #SHA2_224 #M32 (v len) b0 st0)
  end


val sha224_update_last: update_last_vec_t' SHA2_224 M32

let sha224_update_last totlen len b st =
  let open Lib.Sequence in
  let h0 = ST.get () in
  sha256_update_last totlen len b st;
  let h1 = ST.get () in
  begin
    let st0: lseq (element_t SHA2_256 M32) 8 = as_seq h0 st in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_256 in
    let b0: multiseq (lanes SHA2_256 M32) (v len) = as_seq_multi h0 b in
    let st1: lseq (element_t SHA2_256 M32) 8 = as_seq h1 st in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_256 in
    Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_256 len;
    let hacl_spec_update_224_256 b st: Lemma (ensures
      Hacl.Spec.SHA2.update SHA2_256 b st ==
      Hacl.Spec.SHA2.update SHA2_224 b st)
      [ SMTPat (Hacl.Spec.SHA2.update SHA2_256 b st) ]
    =
      hacl_spec_update_224_256 b st
    in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update_last #SHA2_256 totlen (v len) b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_256 #M32 totlen (v len) b0 st0 0 }
      Hacl.Spec.SHA2.update_last SHA2_256 totlen (v len) b0.(|0|) st0_m32;
    (==) { }
      Hacl.Spec.SHA2.update_last SHA2_224 totlen (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_224 #M32 totlen (v len) b0 st0 0 }
      (state_spec_v (SpecVec.update_last #SHA2_224 #M32 totlen (v len) b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_256
      (SpecVec.update_last #SHA2_224 #M32 totlen (v len) b0 st0)
      (SpecVec.update_last #SHA2_256 #M32 totlen (v len) b0 st0)
  end

#pop-options

[@CInline] let sha224_finish = finish #SHA2_224 #M32

[@CInline] let sha384_init = init #SHA2_384 #M32
[@CInline] let sha384_update = update #SHA2_384 #M32
[@CInline] let sha384_update_nblocks = update_nblocks #SHA2_384 #M32 sha384_update
[@CInline] let sha384_update_last = update_last #SHA2_384 #M32 sha384_update
[@CInline] let sha384_finish = finish #SHA2_384 #M32

let sha512_init = init #SHA2_512 #M32
[@CInline] let sha512_update = update #SHA2_512 #M32
[@CInline] let sha512_update_nblocks = update_nblocks #SHA2_512 #M32 sha512_update
[@CInline] let sha512_update_last = update_last #SHA2_512 #M32 sha512_update
[@CInline] let sha512_finish = finish #SHA2_512 #M32

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

