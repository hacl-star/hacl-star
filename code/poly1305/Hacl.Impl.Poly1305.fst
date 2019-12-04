module Hacl.Impl.Poly1305

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module S = Spec.Poly1305
module Vec = Hacl.Spec.Poly1305.Vec
module Equiv = Hacl.Spec.Poly1305.Equiv
module F32xN = Hacl.Impl.Poly1305.Field32xN

friend Lib.LoopCombinators


let _: squash (inversion field_spec) = allow_inversion field_spec


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq' --record_options"

inline_for_extraction noextract
let get_acc #s (ctx:poly1305_ctx s) : Stack (felem s)
  (requires fun h -> live h ctx)
  (ensures  fun h0 acc h1 -> h0 == h1 /\ live h1 acc /\ acc == gsub ctx 0ul (nlimb s))
  = sub ctx 0ul (nlimb s)


inline_for_extraction noextract
let get_precomp_r #s (ctx:poly1305_ctx s) : Stack (precomp_r s)
  (requires fun h -> live h ctx)
  (ensures  fun h0 pre h1 -> h0 == h1 /\ live h1 pre /\ pre == gsub ctx (nlimb s) (precomplen s))
  = sub ctx (nlimb s) (precomplen s)


unfold
let op_String_Access #a #len = LSeq.index #a #len

let as_get_acc #s h ctx = (feval h (gsub ctx 0ul (nlimb s))).[0]

let as_get_r #s h ctx = (feval h (gsub ctx (nlimb s) (nlimb s))).[0]

let state_inv_t #s h ctx =
  felem_fits h (gsub ctx 0ul (nlimb s)) (2, 2, 2, 2, 2) /\
  F32xN.load_precompute_r_post #(width s) h (gsub ctx (nlimb s) (precomplen s))


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --record_options"
let reveal_ctx_inv #s ctx h0 h1 =
  let acc_b = gsub ctx 0ul (nlimb s) in
  let r_b = gsub ctx (nlimb s) (nlimb s) in
  let precom_b = gsub ctx (nlimb s) (precomplen s) in
  as_seq_gsub h0 ctx 0ul (nlimb s);
  as_seq_gsub h1 ctx 0ul (nlimb s);
  as_seq_gsub h0 ctx (nlimb s) (nlimb s);
  as_seq_gsub h1 ctx (nlimb s) (nlimb s);
  as_seq_gsub h0 ctx (nlimb s) (precomplen s);
  as_seq_gsub h1 ctx (nlimb s) (precomplen s);
  assert (as_seq h0 acc_b == as_seq h1 acc_b);
  assert (as_seq h0 r_b == as_seq h1 r_b);
  assert (as_seq h0 precom_b == as_seq h1 precom_b)


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq' --record_options"

inline_for_extraction noextract
val poly1305_encode_block:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint b f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    (feval h1 f).[0] == S.encode 16 (as_seq h0 b))

let poly1305_encode_block #s f b =
  load_felem_le f b;
  set_bit128 f


inline_for_extraction noextract
val poly1305_encode_blocks:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 (blocklen s) ->
  Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint b f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    feval h1 f == Vec.load_blocks #(width s) (as_seq h0 b))

let poly1305_encode_blocks #s f b =
  load_felems_le f b;
  set_bit128 f


inline_for_extraction noextract
val poly1305_encode_last:
    #s:field_spec
  -> f:felem s
  -> len:size_t{v len < 16}
  -> b:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint b f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    (feval h1 f).[0] == S.encode (v len) (as_seq h0 b))

let poly1305_encode_last #s f len b =
  push_frame();
  let tmp = create 16ul (u8 0) in
  update_sub tmp 0ul len b;
  let h0 = ST.get () in
  Hacl.Impl.Poly1305.Lemmas.nat_from_bytes_le_eq_lemma (v len) (as_seq h0 b);
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) == BSeq.nat_from_bytes_le (as_seq h0 tmp));
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) < pow2 (v len * 8));

  load_felem_le f tmp;
  let h1 = ST.get () in
  lemma_feval_is_fas_nat h1 f;
  set_bit f (len *! 8ul);
  pop_frame()


inline_for_extraction noextract
val poly1305_encode_r:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h b /\ live h p /\ disjoint b p)
  (ensures  fun h0 _ h1 ->
    modifies (loc p) h0 h1 /\
    F32xN.load_precompute_r_post #(width s) h1 p /\
    (feval h1 (gsub p 0ul 5ul)).[0] == S.poly1305_encode_r (as_seq h0 b))

let poly1305_encode_r #s p b =
  let lo = uint_from_bytes_le (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le (sub b 8ul 8ul) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  load_precompute_r p lo hi

[@ Meta.Attribute.specialize ]
let poly1305_init #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let kr = sub key 0ul 16ul in
  set_zero acc;
  poly1305_encode_r #s pre kr


inline_for_extraction noextract
val update1:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 16ul
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h p /\ live h b /\ live h acc /\
    disjoint p acc /\ disjoint b acc /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.fmul_precomp_r_pre #(width s) h p)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    (feval h1 acc).[0] == S.poly1305_update1
      (feval h0 (gsub p 0ul 5ul)).[0] 16 (as_seq h0 b) (feval h0 acc).[0])

let update1 #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_block e b;
  fadd_mul_r acc e pre;
  pop_frame ()


let poly1305_update1 #s ctx text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  update1 pre text acc


inline_for_extraction noextract
val poly1305_update_last:
    #s:field_spec
  -> p:precomp_r s
  -> len:size_t{v len < 16}
  -> b:lbuffer uint8 len
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h p /\ live h b /\ live h acc /\
    disjoint p acc /\ disjoint b acc /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.fmul_precomp_r_pre #(width s) h p)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    (feval h1 acc).[0] == S.poly1305_update1
      (feval h0 (gsub p 0ul 5ul)).[0] (v len) (as_seq h0 b) (feval h0 acc).[0])

#push-options "--z3rlimit 200"
let poly1305_update_last #s pre len b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_last e len b;
  fadd_mul_r acc e pre;
  pop_frame ()
#pop-options

inline_for_extraction noextract
val poly1305_update_nblocks:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 (blocklen s)
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h p /\ live h b /\ live h acc /\
    disjoint acc p /\ disjoint acc b /\
    felem_fits h acc (3, 3, 3, 3, 3) /\
    F32xN.load_precompute_r_post #(width s) h p)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (3, 3, 3, 3, 3) /\
    feval h1 acc ==
      Vec.poly1305_update_nblocks #(width s) (feval h0 (gsub p 10ul 5ul)) (as_seq h0 b) (feval h0 acc))

let poly1305_update_nblocks #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_blocks e b;
  fmul_rn acc acc pre;
  fadd acc acc e;
  pop_frame ()


inline_for_extraction noextract
val poly1305_update1_f:
    #s:field_spec
  -> p:precomp_r s
  -> nb:size_t
  -> len:size_t{v nb == v len / 16}
  -> text:lbuffer uint8 len
  -> i:size_t{v i < v nb}
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h p /\ live h text /\ live h acc /\
    disjoint acc p /\ disjoint acc text /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.fmul_precomp_r_pre #(width s) h p)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    (feval h1 acc).[0] ==
    LSeq.repeat_blocks_f #uint8 #S.felem 16
      (as_seq h0 text) (S.poly1305_update1 (feval h0 (gsub p 0ul 5ul)).[0] 16) (v nb) (v i) (feval h0 acc).[0])

let poly1305_update1_f #s pre nb len text i acc=
  assert ((v i + 1) * 16 <= v nb * 16);
  let block = sub #_ #_ #len text (i *! 16ul) 16ul in
  update1 #s pre block acc


#push-options "--max_fuel 1"
inline_for_extraction noextract
val poly1305_update_scalar:
    #s:field_spec
  -> len:size_t
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h text /\ live h acc /\ live h pre /\
    disjoint acc text /\ disjoint acc pre /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.fmul_precomp_r_pre #(width s) h pre)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    (feval h1 acc).[0] ==
    S.poly1305_update (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])

let poly1305_update_scalar #s len text pre acc =
  let nb = len /. 16ul in
  let rem = len %. 16ul in
  let h0 = ST.get () in
  LSeq.lemma_repeat_blocks #uint8 #S.felem 16 (as_seq h0 text)
  (S.poly1305_update1 (feval h0 (gsub pre 0ul 5ul)).[0] 16)
  (S.poly1305_update_last (feval h0 (gsub pre 0ul 5ul)).[0])
  (feval h0 acc).[0];

  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f 16 (as_seq h0 text)
      (S.poly1305_update1 (feval h0 (gsub pre 0ul 5ul)).[0] 16) (v nb) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies1 acc h0 h /\
    live h pre /\ live h text /\ live h acc /\
    disjoint acc pre /\ disjoint acc text /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.fmul_precomp_r_pre #(width s) h pre /\
    (feval h acc).[0] == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc).[0] in

  Lib.Loops.for (size 0) nb inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc).[0] (v i);
      poly1305_update1_f #s pre nb len text i acc);

  let h1 = ST.get () in
  assert ((feval h1 acc).[0] == Lib.LoopCombinators.repeati (v nb) (spec_fh h0) (feval h0 acc).[0]);

  if rem >. 0ul then (
    let last = sub text (nb *! 16ul) rem in
    as_seq_gsub h1 text (nb *! 16ul) rem;
    assert (disjoint acc last);
    poly1305_update_last #s pre rem last acc)
#pop-options


inline_for_extraction noextract
val poly1305_update_multi_f:
    #s:field_spec
  -> p:precomp_r s
  -> bs:size_t{v bs == width s * S.size_block}
  -> nb:size_t
  -> len:size_t{v nb == v len / v bs /\ v len % v bs == 0}
  -> text:lbuffer uint8 len
  -> i:size_t{v i < v nb}
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h p /\ live h text /\ live h acc /\
    disjoint acc p /\ disjoint acc text /\
    felem_fits h acc (3, 3, 3, 3, 3) /\
    F32xN.load_precompute_r_post #(width s) h p)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (3, 3, 3, 3, 3) /\
    F32xN.load_precompute_r_post #(width s) h1 p /\
    feval h1 acc ==
    LSeq.repeat_blocks_f #uint8 #(Vec.elem (width s))
      (v bs) (as_seq h0 text) (Vec.poly1305_update_nblocks #(width s) (feval h0 (gsub p 10ul 5ul))) (v nb) (v i) (feval h0 acc))

let poly1305_update_multi_f #s pre bs nb len text i acc=
  assert ((v i + 1) * v bs <= v nb * v bs);
  let block = sub #_ #_ #len text (i *! bs) bs in
  let h1 = ST.get () in
  as_seq_gsub h1 text (i *! bs) bs;
  poly1305_update_nblocks #s pre block acc


#push-options "--max_fuel 1"
inline_for_extraction noextract
val poly1305_update_multi_loop:
    #s:field_spec
  -> bs:size_t{v bs == width s * S.size_block}
  -> len:size_t{v len % v (blocklen s) == 0}
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h pre /\ live h acc /\ live h text /\
    disjoint acc text /\ disjoint acc pre /\
    felem_fits h acc (3, 3, 3, 3, 3) /\
    F32xN.load_precompute_r_post #(width s) h pre)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (3, 3, 3, 3, 3) /\
    F32xN.load_precompute_r_post #(width s) h1 pre /\
    feval h1 acc == LSeq.repeat_blocks_multi #uint8 #(Vec.elem (width s)) (v bs) (as_seq h0 text)
      (Vec.poly1305_update_nblocks (feval h0 (gsub pre 10ul 5ul))) (feval h0 acc))

let poly1305_update_multi_loop #s bs len text pre acc =
  let nb = len /. bs in

  let h0 = ST.get () in
  LSeq.lemma_repeat_blocks_multi #uint8 #(Vec.elem (width s)) (v bs) (as_seq h0 text)
    (Vec.poly1305_update_nblocks #(width s) (feval h0 (gsub pre 10ul 5ul))) (feval h0 acc);
  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f (v bs) (as_seq h0 text)
      (Vec.poly1305_update_nblocks #(width s) (feval h0 (gsub pre 10ul 5ul))) (v nb) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies1 acc h0 h /\
    live h pre /\ live h text /\ live h acc /\
    disjoint acc pre /\ disjoint acc text /\
    felem_fits h acc (3, 3, 3, 3, 3) /\
    F32xN.load_precompute_r_post #(width s) h pre /\
    feval h acc == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc) in

  Lib.Loops.for (size 0) nb inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc) (v i);
      poly1305_update_multi_f #s pre bs nb len text i acc)
#pop-options


#push-options "--z3rlimit 350"
inline_for_extraction noextract
val poly1305_update_multi:
    #s:field_spec
  -> len:size_t{0 < v len /\ v len % v (blocklen s) == 0}
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h pre /\ live h acc /\ live h text /\
    disjoint acc text /\ disjoint acc pre /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.load_precompute_r_post #(width s) h pre)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    (feval h1 acc).[0] ==
    Vec.poly1305_update_multi #(width s) (as_seq h0 text)
      (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])

let poly1305_update_multi #s len text pre acc =
  let h0 = ST.get () in
  assert_norm (v 10ul + v 5ul <= v 20ul);
  assert (feval h0 (gsub pre 10ul 5ul) == Vec.compute_rw #(width s) ((feval h0 (gsub pre 0ul 5ul)).[0]));

  let bs = blocklen s in
  //assert (v bs == width s * S.size_block);
  let text0 = sub text 0ul bs in
  load_acc #s acc text0;

  let len1 = len -! bs in
  let text1 = sub text bs len1 in
  poly1305_update_multi_loop #s bs len1 text1 pre acc;
  fmul_rn_normalize acc pre
#pop-options


inline_for_extraction noextract
val poly1305_update_vec:
    #s:field_spec
  -> len:size_t
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h text /\ live h acc /\ live h pre /\
    disjoint acc text /\ disjoint acc pre /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    F32xN.load_precompute_r_post #(width s) h pre)
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    (feval h1 acc).[0] ==
      Vec.poly1305_update_vec #(width s) (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])

let poly1305_update_vec #s len text pre acc =
  let sz_block = blocklen s in
  FStar.Math.Lemmas.multiply_fractions (v len) (v sz_block);
  let len0 = (len /. sz_block) *! sz_block in
  let t0 = sub text 0ul len0 in
  FStar.Math.Lemmas.multiple_modulo_lemma (v (len /. sz_block)) (v (blocklen s));
  if len0 >. 0ul then poly1305_update_multi len0 t0 pre acc;

  let len1 = len -! len0 in
  let t1 = sub text len0 len1 in
  poly1305_update_scalar #s len1 t1 pre acc


inline_for_extraction noextract
val poly1305_update32: poly1305_update_st M32
let poly1305_update32 ctx len text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  poly1305_update_scalar #M32 len text pre acc


inline_for_extraction noextract
val poly1305_update_128_256: #s:field_spec { s = M128 || s = M256 } -> poly1305_update_st s
let poly1305_update_128_256 #s ctx len text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  let h0 = ST.get () in
  poly1305_update_vec #s len text pre acc;
  let h1 = ST.get () in
  Equiv.poly1305_update_vec_lemma #(width s) (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0]


inline_for_extraction noextract
[@ Meta.Attribute.specialize ]
let poly1305_update #s =
  match s with
  | M32 -> poly1305_update32
  | _ -> poly1305_update_128_256 #s

#set-options "--z3rlimit 150"

[@ Meta.Attribute.specialize ]
let poly1305_finish #s tag key ctx =
  let acc = get_acc ctx in
  let ks = sub key 16ul 16ul in

  let h0 = ST.get () in
  reduce_felem acc;
  let h1 = ST.get () in
  assert ((fas_nat h1 acc).[0] == (feval h0 acc).[0]);
  let (f10, f11) = uints64_from_felem_le acc in
  assert (v f11 * pow2 64 + v f10 == (fas_nat h1 acc).[0] % pow2 128);
  let (f20, f21) = uints64_from_bytes_le ks in
  assert (v f21 * pow2 64 + v f20 == BSeq.nat_from_bytes_le (as_seq h0 ks));
  let (f30, f31) = mod_add128 (f10, f11) (f20, f21) in
  assert (v f31 * pow2 64 + v f30 ==
    ((fas_nat h1 acc).[0] % pow2 128 + BSeq.nat_from_bytes_le (as_seq h0 ks)) % pow2 128);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (fas_nat h1 acc).[0] (BSeq.nat_from_bytes_le (as_seq h0 ks)) (pow2 128);
  uints64_to_bytes_le tag f30 f31

noextract
[@ Meta.Attribute.specialize ]
let poly1305_mac #s tag len text key =
  push_frame ();
  let ctx = create (nlimb s +! precomplen s) (limb_zero s) in
  poly1305_init #s ctx key;
  poly1305_update #s ctx len text;
  poly1305_finish #s tag key ctx;
  pop_frame ()
