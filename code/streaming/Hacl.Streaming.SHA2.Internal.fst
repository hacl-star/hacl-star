module Hacl.Streaming.SHA2.Internal

open Spec.Hash.Definitions

open FStar.HyperStack.ST

inline_for_extraction noextract
let update_nblocks_vec_t' (a:sha2_alg) (m:Hacl.Spec.SHA2.Vec.(m:m_spec{is_supported a m})) =
  let open Lib.IntTypes in
  let open Lib.MultiBuffer in
  let open Lib.Buffer in
  let open Hacl.Spec.SHA2.Vec in
  let open Hacl.Impl.SHA2.Core in
    len:size_t
  -> b:multibuf (lanes a m) len
  -> st:state_t a m ->
  Stack unit
  (requires fun h0 -> live_multi h0 b /\ live h0 st /\ disjoint_multi b st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
   (lemma_len_lt_max_a_fits_size_t a len;
    as_seq h1 st == update_nblocks #a #m (v len) (as_seq_multi h0 b) (as_seq h0 st)))

// TODO: move these into suitable files
let update_nblocks_224: update_nblocks_vec_t' SHA2_224 Hacl.Spec.SHA2.Vec.M32 =
  Hacl.Impl.SHA2.Generic.update_nblocks #SHA2_224 #Hacl.Spec.SHA2.Vec.M32
    (Hacl.Impl.SHA2.Generic.update #SHA2_224 #Hacl.Spec.SHA2.Vec.M32)
let update_nblocks_256: update_nblocks_vec_t' SHA2_256 Hacl.Spec.SHA2.Vec.M32 =
  Hacl.Impl.SHA2.Generic.update_nblocks #SHA2_256 #Hacl.Spec.SHA2.Vec.M32
    (Hacl.Impl.SHA2.Generic.update #SHA2_256 #Hacl.Spec.SHA2.Vec.M32)
let update_nblocks_384: update_nblocks_vec_t' SHA2_384 Hacl.Spec.SHA2.Vec.M32 =
  Hacl.Impl.SHA2.Generic.update_nblocks #SHA2_384 #Hacl.Spec.SHA2.Vec.M32
    (Hacl.Impl.SHA2.Generic.update #SHA2_384 #Hacl.Spec.SHA2.Vec.M32)
let update_nblocks_512: update_nblocks_vec_t' SHA2_512 Hacl.Spec.SHA2.Vec.M32 =
  Hacl.Impl.SHA2.Generic.update_nblocks #SHA2_512 #Hacl.Spec.SHA2.Vec.M32
    (Hacl.Impl.SHA2.Generic.update #SHA2_512 #Hacl.Spec.SHA2.Vec.M32)
