module Hacl.Hash.SHA2

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module B = LowStar.Buffer

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

open Lib.MultiBuffer
open Lib.NTuple

module Vec = Hacl.Spec.SHA2.Vec

// To prove we are properly defining init
friend Spec.Agile.Hash
// To prove we are properly defining update_last
friend Spec.Hash.Incremental
// To know the definition of init
friend Spec.SHA2

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
let mb_state_32 a = Hacl.Impl.SHA2.Core.state_t a Hacl.Spec.SHA2.Vec.M32

#push-options "--ifuel 1"

inline_for_extraction noextract
let coerce_to_state (a:sha2_alg) (b:mb_state_32 a) : state (| a, () |)
  = Lib.IntVector.reveal_vec_1 (word_t a);
    b

inline_for_extraction noextract
let coerce_to_mb_state (a:sha2_alg) (b:state (| a, () |)) : mb_state_32 a
  = Lib.IntVector.reveal_vec_1 (word_t a);
    b

val state_spec_v_lemma (a:sha2_alg) (st:Vec.state_spec a Vec.M32) : Lemma
  (Lib.IntVector.reveal_vec_1 (word_t a);
   st `Seq.equal` Lib.Sequence.index (Vec.state_spec_v st) 0)

let state_spec_v_lemma a st =
  let open Lib.Sequence in
  let open Lib.IntVector in
  reveal_vec_v_1 st.[0];
  reveal_vec_v_1 st.[1];
  reveal_vec_v_1 st.[2];
  reveal_vec_v_1 st.[3];
  reveal_vec_v_1 st.[4];
  reveal_vec_v_1 st.[5];
  reveal_vec_v_1 st.[6];
  reveal_vec_v_1 st.[7];
  reveal_vec_1 (word_t a);
  eq_intro #(word a) #8 (Vec.state_spec_v st).[0] st

let init_224 st =
  [@inline_let]
  let st: mb_state_32 SHA2_224 = coerce_to_mb_state SHA2_224 st in

  Lib.IntVector.reveal_vec_1 (word_t SHA2_224);
  Hacl.SHA2.Scalar32.init #SHA2_224 st;
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_224 Vec.M32 0;
  state_spec_v_lemma SHA2_224 (Vec.init SHA2_224 Vec.M32)

let init_256 st =
  [@inline_let]
  let st: mb_state_32 SHA2_256 = coerce_to_mb_state SHA2_256 st in

  Lib.IntVector.reveal_vec_1 (word_t SHA2_256);
  Hacl.SHA2.Scalar32.init #SHA2_256 st;
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_256 Vec.M32 0;
  state_spec_v_lemma SHA2_256 (Vec.init SHA2_256 Vec.M32)

let init_384 st =
  [@inline_let]
  let st: mb_state_32 SHA2_384 = coerce_to_mb_state SHA2_384 st in

  Lib.IntVector.reveal_vec_1 (word_t SHA2_384);
  Hacl.SHA2.Scalar32.init #SHA2_384 st;
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_384 Vec.M32 0;
  state_spec_v_lemma SHA2_384 (Vec.init SHA2_384 Vec.M32)

let init_512 st =
  [@inline_let]
  let st: mb_state_32 SHA2_512 = coerce_to_mb_state SHA2_512 st in

  Lib.IntVector.reveal_vec_1 (word_t SHA2_512);
  Hacl.SHA2.Scalar32.init #SHA2_512 st;
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_512 Vec.M32 0;
  state_spec_v_lemma SHA2_512 (Vec.init SHA2_512 Vec.M32)

let alloca_224 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_224 Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_224 Vec.M32 0;
  Lib.IntVector.reveal_vec_1 (word_t SHA2_224);
  state_spec_v_lemma SHA2_224 (Vec.init SHA2_224 Vec.M32);
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  coerce_to_state SHA2_224 st

let alloca_256 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_256 Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_256 Vec.M32 0;
  Lib.IntVector.reveal_vec_1 (word_t SHA2_256);
  state_spec_v_lemma SHA2_256 (Vec.init SHA2_256 Vec.M32);
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  coerce_to_state SHA2_256 st

let alloca_384 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_384 Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_384 Vec.M32 0;
  Lib.IntVector.reveal_vec_1 (word_t SHA2_384);
  state_spec_v_lemma SHA2_384 (Vec.init SHA2_384 Vec.M32);
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  coerce_to_state SHA2_384 st

let alloca_512 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_512 Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  Hacl.Spec.SHA2.Equiv.init_lemma_l SHA2_512 Vec.M32 0;
  Lib.IntVector.reveal_vec_1 (word_t SHA2_512);
  state_spec_v_lemma SHA2_512 (Vec.init SHA2_512 Vec.M32);
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  coerce_to_state SHA2_512 st

inline_for_extraction noextract
val mk_update_multi: a:sha2_alg -> update_multi_st (| a, () |)

let mk_update_multi a st () blocks n_blocks =
  Lib.IntVector.reveal_vec_1 (word_t a);

  [@inline_let]
  let len_blocks = n_blocks `FStar.UInt32.mul` block_len a in
  [@inline_let]
  let blocks_multi = ntup1 #(Lib.Buffer.lbuffer Lib.IntTypes.uint8 len_blocks) #1 blocks in
  let h0 = ST.get () in
  [@inline_let]
  let st' = coerce_to_mb_state a st in
  begin match a with
  | SHA2_224 -> Hacl.SHA2.Scalar32.sha224_update_nblocks len_blocks blocks_multi st'
  | SHA2_256 -> Hacl.SHA2.Scalar32.sha256_update_nblocks len_blocks blocks_multi st'
  | SHA2_384 -> Hacl.SHA2.Scalar32.sha384_update_nblocks len_blocks blocks_multi st'
  | SHA2_512 -> Hacl.SHA2.Scalar32.sha512_update_nblocks len_blocks blocks_multi st'
  end;

  let h1 = ST.get () in

  begin (* ghost *)
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let st0' = as_seq #(| a, () |) h0 st' in
  let st0 = as_seq h0 st in
  let blocks0 = LowStar.Buffer.as_seq h0 blocks in
  let length_blocks = UInt32.v len_blocks in
  assert (Lib.Sequence.length blocks0 = length_blocks);
  let blocks0_multi = as_seq_multi #1 #len_blocks h0 blocks_multi in
  let st0_raw = LowStar.Buffer.as_seq h0 st in

  calc (==) {
    as_seq h1 st;
  (==) { }
    as_seq #(| a, () |) h1 st';
  (==) { }
    Vec.update_nblocks #a #Vec.M32 length_blocks blocks0_multi st0';
  (==) { state_spec_v_lemma a (Vec.update_nblocks #a #Vec.M32 length_blocks blocks0_multi st0') }
    Lib.Sequence.index (Vec.state_spec_v (Vec.update_nblocks #a #Vec.M32 length_blocks blocks0_multi st0')) 0;
  (==) { Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #a #Vec.M32 length_blocks blocks0_multi st0_raw 0 }
    Hacl.Spec.SHA2.update_nblocks a length_blocks blocks0_multi.(|0|)
      (Lib.Sequence.index (Vec.state_spec_v #a #Vec.M32 (as_seq h0 st)) 0);
  (==) { state_spec_v_lemma a (as_seq h0 st) }
    Hacl.Spec.SHA2.update_nblocks a length_blocks blocks0_multi.(|0|) (as_seq h0 st);
  (==) { }
    Hacl.Spec.SHA2.update_nblocks a length_blocks blocks0 st0;
  (==) { Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi a length_blocks blocks0 st0 } (
    let b = blocks0 in
    let open Lib.Sequence in
    let bl = block_length a in
    repeat_blocks_multi #Lib.IntTypes.uint8 #(words_state a) bl
      (Seq.slice b 0 (Seq.length b - Seq.length b % bl)) (Hacl.Spec.SHA2.update a) st0);
  (==) { }
    Lib.Sequence.repeat_blocks_multi #Lib.IntTypes.uint8 #(words_state a)
      (block_length a) blocks0 (Hacl.Spec.SHA2.update a) st0;
  (==) {
    FStar.Classical.forall_intro_2 (Hacl.Spec.SHA2.EquivScalar.update_lemma a);
    Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality
      #Lib.IntTypes.uint8 #(words_state a)
      (block_length a) blocks0 (Hacl.Spec.SHA2.update a)
      (Lib.UpdateMulti.Lemmas.repeat_f (block_length a) (Spec.Agile.Hash.update a))
      st0
  }
    Lib.Sequence.repeat_blocks_multi #Lib.IntTypes.uint8 #(words_state a)
      (block_length a) blocks0 (Lib.UpdateMulti.Lemmas.repeat_f (block_length a) (Spec.Agile.Hash.update a)) st0;
  (==) {
    Lib.UpdateMulti.Lemmas.update_multi_is_repeat_blocks_multi #(words_state a)
      (block_length a) (Spec.Agile.Hash.update a) st0 blocks0
  }
    Lib.UpdateMulti.mk_update_multi #(words_state a) (block_length a) (Spec.Agile.Hash.update a) st0 blocks0;
  (==) { }
    Spec.Agile.Hash.update_multi a st0 () blocks0;
  }
  end

let update_multi_224 =
  mk_update_multi SHA2_224
let update_multi_256 =
  mk_update_multi SHA2_256
let update_multi_384 =
  mk_update_multi SHA2_384
let update_multi_512 =
  mk_update_multi SHA2_512

let pad_224 = Hacl.Hash.PadFinish.pad SHA2_224
let pad_256 = Hacl.Hash.PadFinish.pad SHA2_256
let pad_384 = Hacl.Hash.PadFinish.pad SHA2_384
let pad_512 = Hacl.Hash.PadFinish.pad SHA2_512

#push-options "--z3rlimit 300"

let update_last_224 st prev_len input input_len =
  let h0 = ST.get () in
  [@inline_let]
  let st' = coerce_to_mb_state SHA2_224 st in
  [@inline_let]
  let input' = ntup1 #(Lib.Buffer.lbuffer Lib.IntTypes.uint8 input_len) #1 input in
  Lib.IntVector.reveal_vec_1 (word_t SHA2_224);
  [@inline_let]
  let totlen = prev_len `Hacl.Hash.MD.len_add32 SHA2_224` input_len in
  Hacl.SHA2.Scalar32.sha224_update_last totlen input_len input' st';
  let h1 = ST.get () in
  begin (* ghost *)
    let input0_raw = B.as_seq h0 input in
    let input0 = as_seq_multi h0 input' in

    let st0 = as_seq h0 st in
    let st0' = as_seq #(| SHA2_224, () |) h0 st' in
    let vlen = Lib.IntTypes.v input_len in
    let vprev_len = prev_len_v prev_len in
    let vtotlen = Lib.IntTypes.v totlen in
    let pad_s = Spec.Hash.MD.pad SHA2_224 vtotlen in
    let blocks1 = Seq.append input0 pad_s in
    let blocks1_raw = Seq.append input0_raw pad_s in

    calc (==) {
        as_seq h1 st;
      (==) { }
        Vec.update_last #SHA2_224 #Vec.M32 totlen vlen input0 st0';
      (==) { state_spec_v_lemma SHA2_224 (Vec.update_last totlen vlen input0 st0') }
        Lib.Sequence.index (Vec.state_spec_v #SHA2_224 #Vec.M32 (Vec.update_last totlen vlen input0 st0')) 0;
      (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_224 #Vec.M32 totlen vlen input0 st0' 0 }
        Hacl.Spec.SHA2.update_last SHA2_224 totlen vlen input0.(|0|)
          (Lib.Sequence.index (Vec.state_spec_v #SHA2_224 #Vec.M32 st0') 0);
      (==) { state_spec_v_lemma SHA2_224 st0' }
        Hacl.Spec.SHA2.update_last SHA2_224 totlen vlen input0.(|0|) st0';
      (==) { ntup1_lemma #_ #1 input0 }
        Hacl.Spec.SHA2.update_last SHA2_224 totlen vlen input0 st0';
      (==) {
        Hacl.Spec.SHA2.EquivScalar.update_last_is_repeat_blocks_multi SHA2_224 vtotlen vlen input0 st0'
      }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_224) blocks1 (Hacl.Spec.SHA2.update SHA2_224) st0';
      (==) { assert (st0 `Seq.equal` st0');
             ntup1_lemma #_ #1 input0; assert (blocks1 `Seq.equal` blocks1_raw) }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_224) blocks1_raw (Hacl.Spec.SHA2.update SHA2_224) st0;
      (==) { Classical.forall_intro_2 (Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_224);
             Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality (block_length SHA2_224)
               blocks1_raw
               (Hacl.Spec.SHA2.update SHA2_224)
               (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_224) (Spec.Agile.Hash.update SHA2_224))
               st0 }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_224) blocks1_raw
          (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_224) (Spec.Agile.Hash.update SHA2_224))
          st0;
      (==) {
        Lib.UpdateMulti.Lemmas.update_multi_is_repeat_blocks_multi (block_length SHA2_224) (Spec.Agile.Hash.update SHA2_224) st0 blocks1_raw }
        Lib.UpdateMulti.mk_update_multi (block_length SHA2_224) (Spec.Agile.Hash.update SHA2_224) st0 blocks1_raw;
      (==) { }
        Spec.Hash.Incremental.update_last SHA2_224 st0 (prev_len_v prev_len) input0_raw;
    }
  end

let update_last_256 st prev_len input input_len =
  let h0 = ST.get () in
  [@inline_let]
  let st' = coerce_to_mb_state SHA2_256 st in
  [@inline_let]
  let input' = ntup1 #(Lib.Buffer.lbuffer Lib.IntTypes.uint8 input_len) #1 input in
  Lib.IntVector.reveal_vec_1 (word_t SHA2_256);
  [@inline_let]
  let totlen = prev_len `Hacl.Hash.MD.len_add32 SHA2_256` input_len in
  Hacl.SHA2.Scalar32.sha256_update_last totlen input_len input' st';
  let h1 = ST.get () in
  begin (* ghost *)
    let input0_raw = B.as_seq h0 input in
    let input0 = as_seq_multi h0 input' in

    let st0 = as_seq h0 st in
    let st0' = as_seq #(| SHA2_256, () |) h0 st' in
    let vlen = Lib.IntTypes.v input_len in
    let vprev_len = prev_len_v prev_len in
    let vtotlen = Lib.IntTypes.v totlen in
    let pad_s = Spec.Hash.MD.pad SHA2_256 vtotlen in
    let blocks1 = Seq.append input0 pad_s in
    let blocks1_raw = Seq.append input0_raw pad_s in

    calc (==) {
        as_seq h1 st;
      (==) { }
        Vec.update_last #SHA2_256 #Vec.M32 totlen vlen input0 st0';
      (==) { state_spec_v_lemma SHA2_256 (Vec.update_last totlen vlen input0 st0') }
        Lib.Sequence.index (Vec.state_spec_v #SHA2_256 #Vec.M32 (Vec.update_last totlen vlen input0 st0')) 0;
      (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_256 #Vec.M32 totlen vlen input0 st0' 0 }
        Hacl.Spec.SHA2.update_last SHA2_256 totlen vlen input0.(|0|)
          (Lib.Sequence.index (Vec.state_spec_v #SHA2_256 #Vec.M32 st0') 0);
      (==) { state_spec_v_lemma SHA2_256 st0' }
        Hacl.Spec.SHA2.update_last SHA2_256 totlen vlen input0.(|0|) st0';
      (==) { ntup1_lemma #_ #1 input0 }
        Hacl.Spec.SHA2.update_last SHA2_256 totlen vlen input0 st0';
      (==) {
        Hacl.Spec.SHA2.EquivScalar.update_last_is_repeat_blocks_multi SHA2_256 vtotlen vlen input0 st0'
      }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_256) blocks1 (Hacl.Spec.SHA2.update SHA2_256) st0';
      (==) { assert (st0 `Seq.equal` st0');
             ntup1_lemma #_ #1 input0; assert (blocks1 `Seq.equal` blocks1_raw) }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_256) blocks1_raw (Hacl.Spec.SHA2.update SHA2_256) st0;
      (==) { Classical.forall_intro_2 (Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_256);
             Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality (block_length SHA2_256)
               blocks1_raw
               (Hacl.Spec.SHA2.update SHA2_256)
               (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_256) (Spec.Agile.Hash.update SHA2_256))
               st0 }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_256) blocks1_raw
          (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_256) (Spec.Agile.Hash.update SHA2_256))
          st0;
      (==) {
        Lib.UpdateMulti.Lemmas.update_multi_is_repeat_blocks_multi (block_length SHA2_256) (Spec.Agile.Hash.update SHA2_256) st0 blocks1_raw }
        Lib.UpdateMulti.mk_update_multi (block_length SHA2_256) (Spec.Agile.Hash.update SHA2_256) st0 blocks1_raw;
      (==) { }
        Spec.Hash.Incremental.update_last SHA2_256 st0 (prev_len_v prev_len) input0_raw;
    }
  end

let update_last_384 st prev_len input input_len =
  let h0 = ST.get () in
  [@inline_let]
  let st' = coerce_to_mb_state SHA2_384 st in
  [@inline_let]
  let input' = ntup1 #(Lib.Buffer.lbuffer Lib.IntTypes.uint8 input_len) #1 input in
  Lib.IntVector.reveal_vec_1 (word_t SHA2_384);
  [@inline_let]
  let totlen = prev_len `Hacl.Hash.MD.len_add32 SHA2_384` input_len in
  Hacl.SHA2.Scalar32.sha384_update_last totlen input_len input' st';
  let h1 = ST.get () in
  begin (* ghost *)
    let input0_raw = B.as_seq h0 input in
    let input0 = as_seq_multi h0 input' in

    let st0 = as_seq h0 st in
    let st0' = as_seq #(| SHA2_384, () |) h0 st' in
    let vlen = Lib.IntTypes.v input_len in
    let vprev_len = prev_len_v prev_len in
    let vtotlen = Lib.IntTypes.v totlen in
    let pad_s = Spec.Hash.MD.pad SHA2_384 vtotlen in
    let blocks1 = Seq.append input0 pad_s in
    let blocks1_raw = Seq.append input0_raw pad_s in

    calc (==) {
        as_seq h1 st;
      (==) { }
        Vec.update_last #SHA2_384 #Vec.M32 totlen vlen input0 st0';
      (==) { state_spec_v_lemma SHA2_384 (Vec.update_last totlen vlen input0 st0') }
        Lib.Sequence.index (Vec.state_spec_v #SHA2_384 #Vec.M32 (Vec.update_last totlen vlen input0 st0')) 0;
      (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_384 #Vec.M32 totlen vlen input0 st0' 0 }
        Hacl.Spec.SHA2.update_last SHA2_384 totlen vlen input0.(|0|)
          (Lib.Sequence.index (Vec.state_spec_v #SHA2_384 #Vec.M32 st0') 0);
      (==) { state_spec_v_lemma SHA2_384 st0' }
        Hacl.Spec.SHA2.update_last SHA2_384 totlen vlen input0.(|0|) st0';
      (==) { ntup1_lemma #_ #1 input0 }
        Hacl.Spec.SHA2.update_last SHA2_384 totlen vlen input0 st0';
      (==) {
        Hacl.Spec.SHA2.EquivScalar.update_last_is_repeat_blocks_multi SHA2_384 vtotlen vlen input0 st0'
      }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_384) blocks1 (Hacl.Spec.SHA2.update SHA2_384) st0';
      (==) { assert (st0 `Seq.equal` st0');
             ntup1_lemma #_ #1 input0; assert (blocks1 `Seq.equal` blocks1_raw) }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_384) blocks1_raw (Hacl.Spec.SHA2.update SHA2_384) st0;
      (==) { Classical.forall_intro_2 (Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_384);
             Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality (block_length SHA2_384)
               blocks1_raw
               (Hacl.Spec.SHA2.update SHA2_384)
               (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_384) (Spec.Agile.Hash.update SHA2_384))
               st0 }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_384) blocks1_raw
          (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_384) (Spec.Agile.Hash.update SHA2_384))
          st0;
      (==) {
        Lib.UpdateMulti.Lemmas.update_multi_is_repeat_blocks_multi (block_length SHA2_384) (Spec.Agile.Hash.update SHA2_384) st0 blocks1_raw }
        Lib.UpdateMulti.mk_update_multi (block_length SHA2_384) (Spec.Agile.Hash.update SHA2_384) st0 blocks1_raw;
      (==) { }
        Spec.Hash.Incremental.update_last SHA2_384 st0 (prev_len_v prev_len) input0_raw;
    }
  end

let update_last_512  st prev_len input input_len =
  let h0 = ST.get () in
  [@inline_let]
  let st' = coerce_to_mb_state SHA2_512 st in
  [@inline_let]
  let input' = ntup1 #(Lib.Buffer.lbuffer Lib.IntTypes.uint8 input_len) #1 input in
  Lib.IntVector.reveal_vec_1 (word_t SHA2_512);
  [@inline_let]
  let totlen = prev_len `Hacl.Hash.MD.len_add32 SHA2_512` input_len in
  Hacl.SHA2.Scalar32.sha512_update_last totlen input_len input' st';
  let h1 = ST.get () in
  begin (* ghost *)
    let input0_raw = B.as_seq h0 input in
    let input0 = as_seq_multi h0 input' in

    let st0 = as_seq h0 st in
    let st0' = as_seq #(| SHA2_512, () |) h0 st' in
    let vlen = Lib.IntTypes.v input_len in
    let vprev_len = prev_len_v prev_len in
    let vtotlen = Lib.IntTypes.v totlen in
    let pad_s = Spec.Hash.MD.pad SHA2_512 vtotlen in
    let blocks1 = Seq.append input0 pad_s in
    let blocks1_raw = Seq.append input0_raw pad_s in

    calc (==) {
        as_seq h1 st;
      (==) { }
        Vec.update_last #SHA2_512 #Vec.M32 totlen vlen input0 st0';
      (==) { state_spec_v_lemma SHA2_512 (Vec.update_last totlen vlen input0 st0') }
        Lib.Sequence.index (Vec.state_spec_v #SHA2_512 #Vec.M32 (Vec.update_last totlen vlen input0 st0')) 0;
      (==) { Hacl.Spec.SHA2.Equiv.update_last_lemma_l #SHA2_512 #Vec.M32 totlen vlen input0 st0' 0 }
        Hacl.Spec.SHA2.update_last SHA2_512 totlen vlen input0.(|0|)
          (Lib.Sequence.index (Vec.state_spec_v #SHA2_512 #Vec.M32 st0') 0);
      (==) { state_spec_v_lemma SHA2_512 st0' }
        Hacl.Spec.SHA2.update_last SHA2_512 totlen vlen input0.(|0|) st0';
      (==) { ntup1_lemma #_ #1 input0 }
        Hacl.Spec.SHA2.update_last SHA2_512 totlen vlen input0 st0';
      (==) {
        Hacl.Spec.SHA2.EquivScalar.update_last_is_repeat_blocks_multi SHA2_512 vtotlen vlen input0 st0'
      }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_512) blocks1 (Hacl.Spec.SHA2.update SHA2_512) st0';
      (==) { assert (st0 `Seq.equal` st0');
             ntup1_lemma #_ #1 input0; assert (blocks1 `Seq.equal` blocks1_raw) }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_512) blocks1_raw (Hacl.Spec.SHA2.update SHA2_512) st0;
      (==) { Classical.forall_intro_2 (Hacl.Spec.SHA2.EquivScalar.update_lemma SHA2_512);
             Lib.Sequence.Lemmas.repeat_blocks_multi_extensionality (block_length SHA2_512)
               blocks1_raw
               (Hacl.Spec.SHA2.update SHA2_512)
               (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_512) (Spec.Agile.Hash.update SHA2_512))
               st0 }
        Lib.Sequence.repeat_blocks_multi (block_length SHA2_512) blocks1_raw
          (Lib.UpdateMulti.Lemmas.repeat_f (block_length SHA2_512) (Spec.Agile.Hash.update SHA2_512))
          st0;
      (==) {
        Lib.UpdateMulti.Lemmas.update_multi_is_repeat_blocks_multi (block_length SHA2_512) (Spec.Agile.Hash.update SHA2_512) st0 blocks1_raw }
        Lib.UpdateMulti.mk_update_multi (block_length SHA2_512) (Spec.Agile.Hash.update SHA2_512) st0 blocks1_raw;
      (==) { }
        Spec.Hash.Incremental.update_last SHA2_512 st0 (prev_len_v prev_len) input0_raw;
    }
  end

let finish_224 = Hacl.Hash.PadFinish.finish (|SHA2_224, ()|)
let finish_256 = Hacl.Hash.PadFinish.finish (|SHA2_256, ()|)
let finish_384 = Hacl.Hash.PadFinish.finish (|SHA2_384, ()|)
let finish_512 = Hacl.Hash.PadFinish.finish (|SHA2_512, ()|)

let hash_224 input input_len dst =
  Hacl.Streaming.SHA2.sha224 input input_len dst
let hash_256 input input_len dst =
  Hacl.Streaming.SHA2.sha256 input input_len dst
let hash_384 input input_len dst =
  Hacl.Streaming.SHA2.sha384 input input_len dst
let hash_512 input input_len dst =
  Hacl.Streaming.SHA2.sha512 input input_len dst
