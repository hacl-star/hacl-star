module Hacl.Impl.Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Fields
module S = Hacl.Spec.Poly1305.Vec
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence
module F32xN = Hacl.Impl.Poly1305.Field32xN

friend Lib.LoopCombinators

#reset-options "--z3rlimit 50 --max_fuel 2 --using_facts_from '* -FStar.Seq'"

unfold
let op_String_Access #a #len = LSeq.index #a #len

let get_acc_ #s (ctx:poly1305_ctx s) = gsub ctx 0ul (nlimb s)
let get_precomp_r_ #s (ctx:poly1305_ctx s) = gsub ctx (nlimb s) (precomplen s)
let get_r_ #s (ctx:poly1305_ctx s) = gsub ctx (nlimb s) (nlimb s)

inline_for_extraction
let get_acc #s (ctx:poly1305_ctx s) = sub ctx 0ul (nlimb s)

inline_for_extraction
let get_precomp_r #s (ctx:poly1305_ctx s) = sub ctx (nlimb s) (precomplen s)

let as_get_acc #s h ctx = feval h (gsub ctx 0ul (nlimb s))
let as_get_r #s h ctx = feval h (gsub ctx (nlimb s) (nlimb s))
let state_inv_t #s h ctx =
  F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h (get_acc_ ctx)) /\
  F32xN.load_precompute_r_post #(width s) h (get_precomp_r_ ctx)

inline_for_extraction
val poly1305_encode_block:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h ->
      live h b /\ live h f /\ disjoint b f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      feval h1 f == LSeq.map (S.pfadd (pow2 128))
        (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b))))
let poly1305_encode_block #s f b =
  load_felem_le f b;
  set_bit128 f

inline_for_extraction
val poly1305_encode_blocks:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 (blocklen s)
  -> Stack unit
    (requires fun h ->
      live h b /\ live h f /\ disjoint b f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      feval h1 f == LSeq.map (S.pfadd (pow2 128))
        (S.load_elem #(width s) (as_seq h0 b)))
let poly1305_encode_blocks #s f b =
  load_felems_le f b;
  set_bit128 f

inline_for_extraction
val poly1305_encode_last:
    #s:field_spec
  -> f:felem s
  -> len:size_t{v len < 16}
  -> b:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h b /\ live h f /\ disjoint b f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
     (Math.Lemmas.pow2_le_compat 128 (8 * v len);
      assert_norm (pow2 128 < S.prime);
      feval h1 f == LSeq.map (S.pfadd (pow2 (8 * v len)))
        (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)))))
let poly1305_encode_last #s f len b =
  Math.Lemmas.pow2_le_compat 128 (v len * 8);
  assert_norm (pow2 128 < S.prime);
  push_frame();
  let tmp = create 16ul (u8 0) in
  copy (sub tmp 0ul len) (sub b 0ul len);
  let h0 = ST.get () in
  assume (BSeq.nat_from_bytes_le (as_seq h0 b) == BSeq.nat_from_bytes_le (as_seq h0 tmp));
  load_felem_le f tmp;
  let h1 = ST.get () in
  lemma_feval_is_fas_nat h1 f;
  assert (forall (i:nat). i < width s ==> (feval h1 f).[i] == (fas_nat h1 f).[i]);
  assert (feval h1 f == LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)));
  LSeq.eq_intro
    (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)))
    (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)));
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) < pow2 (v len * 8));
  assert (F32xN.felem_less #(width s) h1 f (pow2 (v len * 8)));
  set_bit f (len *! 8ul);
  pop_frame();
  admit ()

inline_for_extraction
val poly1305_encode_r:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h ->
      live h b /\ live h p /\ disjoint b p)
    (ensures  fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
      F32xN.load_precompute_r_post #(width s) h1 p /\
      feval h1 (gsub p 0ul 5ul) == S.encode_r (as_seq h0 b))
let poly1305_encode_r #s p b =
  let h0 = ST.get () in
  let lo = uint_from_bytes_le (sub b 0ul 8ul) in
  uintv_extensionality lo (BSeq.uint_from_bytes_le (LSeq.sub (as_seq h0 b) 0 8));
  let hi = uint_from_bytes_le (sub b 8ul 8ul) in
  uintv_extensionality hi (BSeq.uint_from_bytes_le (LSeq.sub (as_seq h0 b) 8 8));
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  load_precompute_r p lo hi;
  let h1 = ST.get () in
  LSeq.eq_intro (feval h1 (gsub p 0ul 5ul)) (S.encode_r (as_seq h0 b))

inline_for_extraction
val poly1305_init_:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h key /\ disjoint ctx key)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #s h1 ctx /\
      (as_get_acc h1 ctx, as_get_r h1 ctx) == S.poly1305_init (as_seq h0 key))
let poly1305_init_ #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let kr = sub key 0ul 16ul in
  let h0 = ST.get () in
  set_zero acc;
  let h1 = ST.get () in
  LSeq.eq_intro (feval h1 acc) (fst (S.poly1305_init (as_seq h0 key)));
  poly1305_encode_r #s pre kr;
  admit ()

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_init_32 (ctx:poly1305_ctx M32) (k:lbuffer uint8 32ul) = poly1305_init_ #M32 ctx k
[@CInline]
let poly1305_init_128 (ctx:poly1305_ctx M128) (k:lbuffer uint8 32ul) = poly1305_init_ #M128 ctx k
[@CInline]
let poly1305_init_256  (ctx:poly1305_ctx M256) (k:lbuffer uint8 32ul) = poly1305_init_ #M256 ctx k

let poly1305_init #s ctx key =
  match s with
  | M32  -> poly1305_init_32 ctx key
  | M128 -> poly1305_init_128 ctx key
  | M256 -> poly1305_init_256 ctx key
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val update1:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 16ul
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h p /\ live h b /\ live h acc /\
      disjoint p acc /\ disjoint b acc /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
      F32xN.fmul_precomp_r_pre #(width s) h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      feval h1 acc == S.update1 #(width s)
        (feval h0 (gsub p 0ul 5ul)) 16 (as_seq h0 b) (feval h0 acc))
let update1 #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_block e b;
  fadd_mul_r acc e pre;
  pop_frame ()

inline_for_extraction
val update1_last:
    #s:field_spec
  -> p:precomp_r s
  -> len:size_t{v len < 16}
  -> b:lbuffer uint8 len
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h p /\ live h b /\ live h acc /\
      disjoint p acc /\ disjoint b acc /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
      F32xN.fmul_precomp_r_pre #(width s) h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      feval h1 acc == S.update1 #(width s)
        (feval h0 (gsub p 0ul 5ul)) (v len) (as_seq h0 b) (feval h0 acc))
let update1_last #s pre len b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_last e len b;
  fadd_mul_r acc e pre;
  pop_frame ()

inline_for_extraction
val updaten:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 (blocklen s)
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h p /\ live h b /\ live h acc /\
      disjoint acc p /\ disjoint acc b /\
      felem_fits h acc (2, 3, 2, 2, 2) /\
      F32xN.load_precompute_r_post #(width s) h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      felem_fits h1 acc (2, 3, 2, 2, 2) /\
      feval h1 acc ==
        S.updaten #(width s) (feval h0 (gsub p 10ul 5ul)) (as_seq h0 b) (feval h0 acc))
let updaten #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_blocks e b;
  fmul_rn acc acc pre;
  fadd acc acc e;
  pop_frame ()

inline_for_extraction noextract
val poly1305_update_multi_f:
    #s:field_spec
  -> p:precomp_r s
  -> bs:size_t{v bs == v (blocklen s)}
  -> nb:size_t
  -> len:size_t{v nb == v len / v bs /\ v len % v bs == 0}
  -> text:lbuffer uint8 len
  -> i:size_t{v i < v nb}
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h p /\ live h text /\ live h acc /\
      disjoint acc p /\ disjoint acc text /\
      felem_fits h acc (2, 3, 2, 2, 2) /\
      F32xN.load_precompute_r_post #(width s) h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      felem_fits h1 acc (2, 3, 2, 2, 2) /\
      F32xN.load_precompute_r_post #(width s) h1 p /\
      feval h1 acc ==
      LSeq.repeat_blocks_f #uint8 #(S.elem (width s))
	(v bs) (as_seq h0 text) (S.updaten #(width s) (feval h0 (gsub p 10ul 5ul))) (v nb) (v i) (feval h0 acc))

let poly1305_update_multi_f #s pre bs nb len text i acc=
  assert ((v i + 1) * v bs <= v nb * v bs);
  let block = sub #_ #_ #len text (i *! bs) bs in
  let h1 = ST.get () in
  as_seq_gsub h1 text (i *! bs) bs;
  updaten #s pre block acc

inline_for_extraction
val poly1305_update_multi:
    #s:field_spec
  -> len:size_t{v len % v (blocklen s) == 0}
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h pre /\ live h acc /\ live h text /\
      disjoint acc text /\ disjoint acc pre /\
      felem_fits h acc (2, 3, 2, 2, 2) /\
      F32xN.load_precompute_r_post #(width s) h pre)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      (feval h1 acc).[0] ==
      (S.poly_update_multi #(width s) (as_seq h0 text)
        (feval h0 acc) (feval h0 (gsub pre 0ul 5ul))).[0])
let poly1305_update_multi #s len text pre acc =
  let bs = blocklen s in
  let nb = len /. bs in

  let h0 = ST.get () in
  LSeq.lemma_repeat_blocks_multi #uint8 #(S.elem (width s)) (v bs) (as_seq h0 text)
    (S.updaten #(width s) (feval h0 (gsub pre 10ul 5ul))) (feval h0 acc);
  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f (v bs) (as_seq h0 text)
      (S.updaten #(width s) (feval h0 (gsub pre 10ul 5ul))) (v nb) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies1 acc h0 h /\
    live h pre /\ live h text /\ live h acc /\
    disjoint acc pre /\ disjoint acc text /\
    felem_fits h acc (2, 3, 2, 2, 2) /\
    F32xN.load_precompute_r_post #(width s) h pre /\
    feval h acc == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc) in

  Lib.Loops.for (size 0) nb inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc) (v i);
      poly1305_update_multi_f #s pre bs nb len text i acc);
  fmul_rn_normalize acc pre

inline_for_extraction noextract
val poly1305_update1_f:
    #s:field_spec
  -> p:precomp_r s
  -> nb:size_t
  -> len:size_t{v nb == v len / 16}
  -> text:lbuffer uint8 len
  -> i:size_t{v i < v nb}
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h p /\ live h text /\ live h acc /\
      disjoint acc p /\ disjoint acc text /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
      F32xN.fmul_precomp_r_pre #(width s) h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      feval h1 acc ==
      LSeq.repeat_blocks_f #uint8 #(S.elem (width s)) 16
	(as_seq h0 text) (S.update1 #(width s) (feval h0 (gsub p 0ul 5ul)) 16) (v nb) (v i) (feval h0 acc))
let poly1305_update1_f #s pre nb len text i acc=
  assert ((v i + 1) * 16 <= v nb * 16);
  let block = sub #_ #_ #len text (i *! 16ul) 16ul in
  update1 #s pre block acc

inline_for_extraction noextract
val poly1305_update1_rem:
    #s:field_spec
  -> p:precomp_r s
  -> rem:size_t{v rem < 16}
  -> text:lbuffer uint8 rem
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h p /\ live h text /\ live h acc /\
      disjoint acc p /\ disjoint acc text /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
      F32xN.fmul_precomp_r_pre #(width s) h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      feval h1 acc == S.poly_update1_rem #(width s)
	(feval h0 (gsub p 0ul 5ul)) (v rem) (as_seq h0 text) (feval h0 acc))
let poly1305_update1_rem #s pre rem b acc =
  if (rem >. 0ul) then update1_last #s pre rem b acc

inline_for_extraction
val poly1305_update1:
    #s:field_spec
  -> len:size_t
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h text /\ live h acc /\ live h pre /\
      disjoint acc text /\ disjoint acc pre /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
      F32xN.fmul_precomp_r_pre #(width s) h pre)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      feval h1 acc ==
      S.poly_update1 #(width s) (as_seq h0 text) (feval h0 acc) (feval h0 (gsub pre 0ul 5ul)))
let poly1305_update1 #s len text pre acc =
  let nb = len /. 16ul in
  let rem = len %. 16ul in
  let h0 = ST.get () in
  LSeq.lemma_repeat_blocks #uint8 #(S.elem (width s)) 16 (as_seq h0 text)
  (S.update1 #(width s) (feval h0 (gsub pre 0ul 5ul)) 16)
  (S.poly_update1_rem #(width s) (feval h0 (gsub pre 0ul 5ul)))
  (feval h0 acc);

  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f 16 (as_seq h0 text)
      (S.update1 #(width s) (feval h0 (gsub pre 0ul 5ul)) 16) (v nb) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies1 acc h0 h /\
    live h pre /\ live h text /\ live h acc /\
    disjoint acc pre /\ disjoint acc text /\
    F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
    F32xN.fmul_precomp_r_pre #(width s) h pre /\
    feval h acc == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc) in

  Lib.Loops.for (size 0) nb inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc) (v i);
      poly1305_update1_f #s pre nb len text i acc);

  let h1 = ST.get () in
  assert (feval h1 acc == Lib.LoopCombinators.repeati (v nb) (spec_fh h0) (feval h0 acc));
  let b = sub text (nb *! 16ul) rem in
  as_seq_gsub h1 text (nb *! 16ul) rem;
  assert (as_seq h1 b == LSeq.sub (as_seq h1 text) (v nb * 16) (v rem));
  assert (disjoint b acc);
  poly1305_update1_rem #s pre rem b acc

#set-options "--z3rlimit 150 --max_fuel 1"

inline_for_extraction
val poly1305_update_:
    #s:field_spec
  -> len:size_t
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h text /\ live h acc /\ live h pre /\
      disjoint acc text /\ disjoint acc pre /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
      F32xN.load_precompute_r_post #(width s) h pre)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc))
let poly1305_update_ #s len text pre acc =
  let sz_block = blocklen s in
  let len0 = (len /. sz_block) *! sz_block in
  let t0 = sub text 0ul len0 in
  let h0 = ST.get () in
  as_seq_gsub h0 text 0ul len0;
  assert (felem_fits h0 acc (2, 3, 2, 2, 2));
  assert (disjoint acc t0);
  FStar.Math.Lemmas.multiple_modulo_lemma (v (len /. sz_block)) (v (blocklen s));
  poly1305_update_multi len0 t0 pre acc;

  let len = len -. len0 in
  let text = sub text len0 len in
  poly1305_update1 #s len text pre acc

inline_for_extraction
val poly1305_update1_:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h text /\ live h ctx /\ disjoint ctx text /\
      state_inv_t #s h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #s h1 ctx /\
      as_get_acc h1 ctx == S.poly_update1 #(width s) (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
let poly1305_update1_ #s ctx len text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  poly1305_update1 #s len text pre acc

inline_for_extraction
val poly1305_update__:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h text /\ live h ctx /\ disjoint ctx text /\
      state_inv_t #s h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #s h1 ctx)
let poly1305_update__ #s ctx len text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  poly1305_update_ #s len text pre acc

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_update_32 (ctx:poly1305_ctx M32) (len:size_t) (text:lbuffer uint8 len) = poly1305_update1_ #M32 ctx len text
[@CInline]
let poly1305_update_128 (ctx:poly1305_ctx M128) (len:size_t) (text:lbuffer uint8 len) = poly1305_update__ #M128 ctx len text
[@CInline]
let poly1305_update_256 (ctx:poly1305_ctx M256) (len:size_t) (text:lbuffer uint8 len) = poly1305_update__ #M256 ctx len text

let poly1305_update #s ctx len text = admit();
  match s with
  | M32 -> poly1305_update_32 ctx len text
  | M128 -> poly1305_update_128 ctx len text
  | M256 -> poly1305_update_256 ctx len text
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val poly1305_finish_:
    #s:field_spec
  -> tag:lbuffer uint8 16ul
  -> key:lbuffer uint8 32ul
  -> ctx:poly1305_ctx s
  -> Stack unit
    (requires fun h ->
      live h tag /\ live h key /\ live h ctx /\
      disjoint tag key /\ disjoint tag ctx /\ disjoint key ctx /\
      state_inv_t #s h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc tag |+| loc ctx) h0 h1 /\
      as_seq h1 tag == S.finish #(width s) (as_seq h0 key) (as_get_acc h0 ctx))
let poly1305_finish_ #s tag key ctx =
  let acc = get_acc ctx in
  let ks = sub key 16ul 16ul in

  let h0 = ST.get () in
  reduce_felem acc;
  let h1 = ST.get () in
  assert ((fas_nat h1 acc).[0] == (feval h0 acc).[0]);
  let (f10, f11) = felem_to_limbs acc in
  assert ((limb_v f11).[0] * pow2 64 + (limb_v f10).[0] == (fas_nat h1 acc).[0] % pow2 128);
  let (f20, f21) = bytes_to_limbs #s ks in
  assert ((limb_v f21).[0] * pow2 64 + (limb_v f20).[0] == BSeq.nat_from_bytes_le (as_seq h0 ks));
  let (f30, f31) = mod_add128 (f10, f11) (f20, f21) in
  assert ((limb_v f31).[0] * pow2 64 + (limb_v f30).[0] ==
    ((fas_nat h1 acc).[0] % pow2 128 + BSeq.nat_from_bytes_le (as_seq h0 ks)) % pow2 128);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (fas_nat h1 acc).[0] (BSeq.nat_from_bytes_le (as_seq h0 ks)) (pow2 128);
  store_felem_le tag f30 f31

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_finish_32 (tag:lbuffer uint8 16ul) (key:lbuffer uint8 32ul) (ctx:poly1305_ctx M32) = poly1305_finish_ #M32 tag key ctx
[@CInline]
let poly1305_finish_128 (tag:lbuffer uint8 16ul) (key:lbuffer uint8 32ul) (ctx:poly1305_ctx M128) = poly1305_finish_ #M128 tag key ctx
[@CInline]
let poly1305_finish_256 (tag:lbuffer uint8 16ul) (key:lbuffer uint8 32ul) (ctx:poly1305_ctx M256) = poly1305_finish_ #M256 tag key ctx

let poly1305_finish #s tag key ctx =
   match s with
   | M32 -> poly1305_finish_32 tag key ctx
   | M128 -> poly1305_finish_128 tag key ctx
   | M256 -> poly1305_finish_256 tag key ctx
(* WRAPPER to Prevent Inlining *)

let poly1305_mac #s tag len text key =
  push_frame ();
  let ctx = create (nlimb s +. precomplen s) (limb_zero s) in
  poly1305_init ctx key;
  poly1305_update ctx len text;
  poly1305_finish #s tag key ctx;
  pop_frame ()
