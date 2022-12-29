module Hacl.Hash.SHA2

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

open Lib.MultiBuffer
open Lib.NTuple

include Hacl.Hash.Core.SHA2

// To prove we are properly defining init
friend Spec.Agile.Hash
// To prove we are properly defining update_last
friend Spec.Hash.Incremental
// To know the definition of init
friend Spec.SHA2

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let mb_init_is_init (#a: sha2_alg) (h: HS.mem) (st: state (| a, () |) ): Lemma
  (requires (LowStar.Buffer.as_seq h st == Hacl.Spec.SHA2.Vec.(init a M32)))
  (ensures (as_seq h st == Spec.Agile.Hash.init a))
=
  let st1 = as_seq h st in
  let st1_raw = LowStar.Buffer.as_seq h st in
  let spec = Spec.Agile.Hash.init a in
  let spec_vec = Hacl.Spec.SHA2.Vec.(init a M32) in
  assert (st1_raw `Seq.equal` spec_vec);
  let t = Spec.Hash.Definitions.word_t a in
  let h0 = Hacl.Spec.SHA2.h0 a in
  let lemma_i (i: nat { i < 8 }): Lemma
    (Seq.index st1 i == Seq.index spec i)
  =
    calc (== ) {
      Seq.index st1 i;
    (==) { }
      Seq.index (Lib.IntVector.vec_v #t #1 (Seq.index spec_vec i)) 0;
    (==) { (* otherwise the pattern on createi doesn't trigger *) }
      Seq.index (Lib.IntVector.vec_v #t #1 (Lib.Sequence.index spec_vec i)) 0;
    (==) { }
      Seq.index (Lib.IntVector.vec_v #t #1 Hacl.Spec.SHA2.Vec.(load_element a M32
        (Seq.index h0 i))) 0;
    (==) { }
      Seq.index (Lib.IntVector.vec_v #t #1 Lib.IntVector.(
        vec_load (Seq.index h0 i) 1)) 0;
    (==) { }
      Seq.index h0 i;
    };
    ()
  in
  FStar.Classical.forall_intro lemma_i;
  assert (st1 `Seq.equal` spec)

let init_224 st =
  Hacl.SHA2.Scalar32.init #SHA2_224 st;
  let h1 = ST.get () in
  mb_init_is_init h1 st

let init_256 st =
  Hacl.SHA2.Scalar32.init #SHA2_256 st;
  let h1 = ST.get () in
  mb_init_is_init h1 st

let init_384 st =
  Hacl.SHA2.Scalar32.init #SHA2_384 st;
  let h1 = ST.get () in
  mb_init_is_init h1 st

let init_512 st =
  Hacl.SHA2.Scalar32.init #SHA2_512 st;
  let h1 = ST.get () in
  mb_init_is_init h1 st

let alloca_224 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_224 Hacl.Spec.SHA2.Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  mb_init_is_init #SHA2_224 h1 st;
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  st

let alloca_256 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_256 Hacl.Spec.SHA2.Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  mb_init_is_init #SHA2_256 h1 st;
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  st

let alloca_384 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_384 Hacl.Spec.SHA2.Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  mb_init_is_init #SHA2_384 h1 st;
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  st

let alloca_512 () =
  let h0 = ST.get () in
  let st = Hacl.Impl.SHA2.Generic.alloc SHA2_512 Hacl.Spec.SHA2.Vec.M32 in
  Hacl.Impl.SHA2.Generic.init st;
  let h1 = ST.get () in
  mb_init_is_init #SHA2_512 h1 st;
  LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
  st

let update_multi_224 st () blocks n_blocks =
  let blocks1 = ntup1 blocks in
  Hacl.SHA2.Scalar32.sha224_update_nblocks (n_blocks `FStar.UInt32.mul` block_len SHA2_224) blocks1 st;
  admit ()

let update_multi_256 =
  Hacl.Hash.MD.mk_update_multi SHA2_256 update_256
let update_multi_384 =
  Hacl.Hash.MD.mk_update_multi SHA2_384 update_384
let update_multi_512 =
  Hacl.Hash.MD.mk_update_multi SHA2_512 update_512

let update_last_224 =
  Hacl.Hash.MD.mk_update_last SHA2_224 update_multi_224 pad_224
let update_last_256 =
  Hacl.Hash.MD.mk_update_last SHA2_256 update_multi_256 pad_256
let update_last_384 =
  Hacl.Hash.MD.mk_update_last SHA2_384 update_multi_384 pad_384
let update_last_512 =
  Hacl.Hash.MD.mk_update_last SHA2_512 update_multi_512 pad_512

let hash_224 input input_len dst =
  Hacl.Streaming.SHA2.sha224 input input_len dst
let hash_256 input input_len dst =
  Hacl.Streaming.SHA2.sha256 input input_len dst
let hash_384 input input_len dst =
  Hacl.Streaming.SHA2.sha384 input input_len dst
let hash_512 input input_len dst =
  Hacl.Streaming.SHA2.sha512 input input_len dst
