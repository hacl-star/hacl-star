module Hacl.SHA2.Scalar32.Lemmas

open Lib.IntTypes
open Spec.Agile.Hash
open Hacl.Spec.SHA2.Vec
module SpecVec = Hacl.Spec.SHA2.Vec

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

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

let lemma_spec_update_224_256 b st: Lemma (ensures
  Hacl.Spec.SHA2.update SHA2_256 b st ==
  Hacl.Spec.SHA2.update SHA2_224 b st)
=
  calc (==) {
    Hacl.Spec.SHA2.update SHA2_256 b st;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_256 b st }
    Spec.Agile.Hash.update SHA2_256 st b;
  (==) { Spec.SHA2.Lemmas.update_224_256 st b }
    Spec.Agile.Hash.update SHA2_224 st b;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_224 b st }
    Hacl.Spec.SHA2.update SHA2_224 b st;
  }

let lemma_spec_update_vec_224_256 b0 st0 : Lemma (ensures
  SpecVec.update #SHA2_224 #M32 b0 st0 ==
  SpecVec.update #SHA2_256 #M32 b0 st0)
  =
  let open Lib.Sequence in
  let open Lib.MultiBuffer in
  let st1 = SpecVec.update #SHA2_256 #M32 b0 st0 in
  let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_256 in
  let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_256 in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update #SHA2_256 b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_lemma_l #SHA2_256 #M32 b0 st0 0 }
      Hacl.Spec.SHA2.update SHA2_256 b0.(|0|) st0_m32;
    (==) { lemma_spec_update_224_256 b0.(|0|) st0_m32 }
      Hacl.Spec.SHA2.update SHA2_224 b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_lemma_l #SHA2_224 #M32 b0 st0 0 }
      (state_spec_v #SHA2_224 #M32 (SpecVec.update #SHA2_224 b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_256
      (SpecVec.update #SHA2_256 b0 st0)
      (SpecVec.update #SHA2_224 #M32 b0 st0)

let lemma_spec_update_nblocks_vec_224_256 (len:size_t) b0 st0 : Lemma (ensures (
  Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_256 len;
  SpecVec.update_nblocks #SHA2_224 #M32 (v len) b0 st0 ==
  SpecVec.update_nblocks #SHA2_256 #M32 (v len) b0 st0))
  = let open Lib.IntTypes in
    let open Lib.Sequence in
    let open Lib.MultiBuffer in
    Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_256 len;
    let st1 = SpecVec.update_nblocks #SHA2_256 #M32 (v len) b0 st0 in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_256 in
    let b0_m32' = Seq.slice b0.(|0|) 0 (Seq.length b0.(|0|) - Seq.length b0.(|0|) % block_length SHA2_256) in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_256 in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update_nblocks #SHA2_256 (v len) b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #SHA2_256 #M32 (v len) b0 st0 0 }
      Hacl.Spec.SHA2.update_nblocks SHA2_256 (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi SHA2_256 (v len) b0.(|0|) st0_m32 }
      Lib.Sequence.repeat_blocks_multi (block_length SHA2_256) b0_m32' (Hacl.Spec.SHA2.update SHA2_256) st0_m32;
    (==) {
      FStar.Classical.forall_intro_2 lemma_spec_update_224_256;
      Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality #uint8 #(words_state SHA2_256) (block_length SHA2_256) b0_m32'
        (Hacl.Spec.SHA2.update SHA2_256)
        (Hacl.Spec.SHA2.update SHA2_224)
        st0_m32
    }
      Lib.Sequence.repeat_blocks_multi #uint8 #(words_state SHA2_256) (block_length SHA2_256) b0_m32' (Hacl.Spec.SHA2.update SHA2_224) st0_m32;
    (==) { }
      Lib.Sequence.repeat_blocks_multi #uint8 #(words_state SHA2_224) (block_length SHA2_224) b0_m32' (Hacl.Spec.SHA2.update SHA2_224) (st0_m32 <: words_state SHA2_224);
    (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi SHA2_224 (v len) b0.(|0|) st0_m32 }
      Hacl.Spec.SHA2.update_nblocks SHA2_224 (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #SHA2_224 #M32 (v len) b0 st0 0 }
      (state_spec_v #SHA2_224 #M32 (SpecVec.update_nblocks #SHA2_224 (v len) b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_256
      (SpecVec.update_nblocks #SHA2_256 (v len) b0 st0)
      (SpecVec.update_nblocks #SHA2_224 #M32 (v len) b0 st0)

let lemma_spec_update_last_vec_224_256 totlen (len:size_t{v len <= block_length SHA2_256}) b0 st0 : Lemma (ensures (
  Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_256 len;
  SpecVec.update_last #SHA2_224 #M32 totlen (v len) b0 st0 ==
  SpecVec.update_last #SHA2_256 #M32 totlen (v len) b0 st0))
  = let open Lib.Sequence in
    let open Lib.MultiBuffer in
    let st1 = SpecVec.update_last #SHA2_256 #M32 totlen (v len) b0 st0 in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_256 in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_256 in
    Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_256 len;
    let hacl_spec_update_224_256 b st: Lemma (ensures
      Hacl.Spec.SHA2.update SHA2_256 b st ==
      Hacl.Spec.SHA2.update SHA2_224 b st)
      [ SMTPat (Hacl.Spec.SHA2.update SHA2_256 b st) ]
    =
      lemma_spec_update_224_256 b st
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


let lemma_spec_update_384_512 b st: Lemma (ensures
  Hacl.Spec.SHA2.update SHA2_512 b st ==
  Hacl.Spec.SHA2.update SHA2_384 b st)
=
  calc (==) {
    Hacl.Spec.SHA2.update SHA2_512 b st;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_512 b st }
    Spec.Agile.Hash.update SHA2_512 st b;
  (==) { Spec.SHA2.Lemmas.update_384_512 st b }
    Spec.Agile.Hash.update SHA2_384 st b;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_384 b st }
    Hacl.Spec.SHA2.update SHA2_384 b st;
  }

let lemma_spec_update_vec_384_512 b0 st0 : Lemma (ensures
  SpecVec.update #SHA2_384 #M32 b0 st0 ==
  SpecVec.update #SHA2_512 #M32 b0 st0)
  =
  let open Lib.Sequence in
  let open Lib.MultiBuffer in
  let st1 = SpecVec.update #SHA2_512 #M32 b0 st0 in
  let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_512 in
  let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_512 in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update #SHA2_512 b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_lemma_l #SHA2_512 #M32 b0 st0 0 }
      Hacl.Spec.SHA2.update SHA2_512 b0.(|0|) st0_m32;
    (==) { lemma_spec_update_384_512 b0.(|0|) st0_m32 }
      Hacl.Spec.SHA2.update SHA2_384 b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_lemma_l #SHA2_384 #M32 b0 st0 0 }
      (state_spec_v #SHA2_384 #M32 (SpecVec.update #SHA2_384 b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_512
      (SpecVec.update #SHA2_512 b0 st0)
      (SpecVec.update #SHA2_384 #M32 b0 st0)

let lemma_spec_update_nblocks_vec_384_512 (len:size_t) b0 st0 : Lemma (ensures (
  Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_512 len;
  SpecVec.update_nblocks #SHA2_384 #M32 (v len) b0 st0 ==
  SpecVec.update_nblocks #SHA2_512 #M32 (v len) b0 st0))
  = let open Lib.IntTypes in
    let open Lib.Sequence in
    let open Lib.MultiBuffer in
    Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_512 len;
    let st1 = SpecVec.update_nblocks #SHA2_512 #M32 (v len) b0 st0 in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_512 in
    let b0_m32' = Seq.slice b0.(|0|) 0 (Seq.length b0.(|0|) - Seq.length b0.(|0|) % block_length SHA2_512) in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_512 in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update_nblocks #SHA2_512 (v len) b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #SHA2_512 #M32 (v len) b0 st0 0 }
      Hacl.Spec.SHA2.update_nblocks SHA2_512 (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi SHA2_512 (v len) b0.(|0|) st0_m32 }
      Lib.Sequence.repeat_blocks_multi (block_length SHA2_512) b0_m32' (Hacl.Spec.SHA2.update SHA2_512) st0_m32;
    (==) {
      FStar.Classical.forall_intro_2 lemma_spec_update_384_512;
      Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality #uint8 #(words_state SHA2_512) (block_length SHA2_512) b0_m32'
        (Hacl.Spec.SHA2.update SHA2_512)
        (Hacl.Spec.SHA2.update SHA2_384)
        st0_m32
    }
      Lib.Sequence.repeat_blocks_multi #uint8 #(words_state SHA2_512) (block_length SHA2_512) b0_m32' (Hacl.Spec.SHA2.update SHA2_384) st0_m32;
    (==) { }
      Lib.Sequence.repeat_blocks_multi #uint8 #(words_state SHA2_384) (block_length SHA2_384) b0_m32' (Hacl.Spec.SHA2.update SHA2_384) (st0_m32 <: words_state SHA2_384);
    (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi SHA2_384 (v len) b0.(|0|) st0_m32 }
      Hacl.Spec.SHA2.update_nblocks SHA2_384 (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #SHA2_384 #M32 (v len) b0 st0 0 }
      (state_spec_v #SHA2_384 #M32 (SpecVec.update_nblocks #SHA2_384 (v len) b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_512
      (SpecVec.update_nblocks #SHA2_512 (v len) b0 st0)
      (SpecVec.update_nblocks #SHA2_384 #M32 (v len) b0 st0)

let lemma_spec_update_last_vec_384_512 totlen (len:size_t{v len <= block_length SHA2_512}) b0 st0 : Lemma (ensures (
  Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_512 len;
  SpecVec.update_last #SHA2_384 #M32 totlen (v len) b0 st0 ==
  SpecVec.update_last #SHA2_512 #M32 totlen (v len) b0 st0))
  = let open Lib.Sequence in
    let open Lib.MultiBuffer in
    let st1 = SpecVec.update_last #SHA2_512 #M32 totlen (v len) b0 st0 in
    let st0_m32 = (state_spec_v st0).[0] <: words_state SHA2_512 in
    let st1_m32 = (state_spec_v st1).[0] <: words_state SHA2_512 in
    Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t SHA2_512 len;
    let hacl_spec_update_384_512 b st: Lemma (ensures
      Hacl.Spec.SHA2.update SHA2_512 b st ==
      Hacl.Spec.SHA2.update SHA2_384 b st)
      [ SMTPat (Hacl.Spec.SHA2.update SHA2_512 b st) ]
    =
      lemma_spec_update_384_512 b st
    in
    calc (==) {
      st1_m32;
    (==) {}
      (state_spec_v (SpecVec.update_last #SHA2_512 totlen (v len) b0 st0)).[0];
    (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_512 #M32 totlen (v len) b0 st0 0 }
      Hacl.Spec.SHA2.update_last SHA2_512 totlen (v len) b0.(|0|) st0_m32;
    (==) { }
      Hacl.Spec.SHA2.update_last SHA2_384 totlen (v len) b0.(|0|) st0_m32;
    (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_384 #M32 totlen (v len) b0 st0 0 }
      (state_spec_v (SpecVec.update_last #SHA2_384 #M32 totlen (v len) b0 st0)).[0];
    };
    state_spec_v_extensionality SHA2_512
      (SpecVec.update_last #SHA2_384 #M32 totlen (v len) b0 st0)
      (SpecVec.update_last #SHA2_512 #M32 totlen (v len) b0 st0)
