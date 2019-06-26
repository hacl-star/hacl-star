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

let _: squash (inversion field_spec) = allow_inversion field_spec

#reset-options "--z3rlimit 50 --max_fuel 0 --using_facts_from '* -FStar.Seq'"

unfold
let op_String_Access #a #len = LSeq.index #a #len

inline_for_extraction noextract
let get_acc #s (ctx:poly1305_ctx s) = sub ctx 0ul (nlimb s)

inline_for_extraction noextract
let get_precomp_r #s (ctx:poly1305_ctx s) = sub ctx (nlimb s) (precomplen s)

let as_get_acc #s h ctx = (feval h (gsub ctx 0ul (nlimb s))).[0]
let as_get_r #s h ctx = (feval h (gsub ctx (nlimb s) (nlimb s))).[0]
let state_inv_t #s h ctx =
  F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h (gsub ctx 0ul (nlimb s))) /\
  F32xN.load_precompute_r_post #(width s) h (gsub ctx (nlimb s) (precomplen s))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

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

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_pow2_128: n:nat ->
  Lemma
  (requires n <= 128)
  (ensures pow2 n < S.prime)
  [SMTPat (pow2 n)]
let lemma_pow2_128 n =
  Math.Lemmas.pow2_le_compat 128 n;
  assert (pow2 n <= pow2 128);
  assert_norm (pow2 128 < S.prime)

val lemma_felem_fits_init_post:
    #s:field_spec
  -> h:mem
  -> f:felem s
  -> Lemma
    (requires felem_fits h f (0, 0, 0, 0, 0))
    (ensures F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h f))
let lemma_felem_fits_init_post #s h f = ()

val lemma_felem_fits_update_pre:
    #s:field_spec
  -> h:mem
  -> f:felem s
  -> Lemma
    (requires F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h f))
    (ensures felem_fits h f (2, 3, 2, 2, 2))
let lemma_felem_fits_update_pre #s h f = ()

inline_for_extraction noextract
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

inline_for_extraction noextract
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

#restart-solver
#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--z3rlimit 200"
inline_for_extraction noextract
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
      feval h1 f == LSeq.map (S.pfadd (pow2 (8 * v len)))
        (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b))))
let poly1305_encode_last #s f len b =
  push_frame();
  let tmp = create 16ul (u8 0) in
  update_sub tmp 0ul len b;
  let h0 = ST.get () in
  Hacl.Impl.Poly1305.Lemmas.nat_from_bytes_le_eq_lemma (v len) (as_seq h0 b);
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) == BSeq.nat_from_bytes_le (as_seq h0 tmp));
  assert (live h0 f);
  load_felem_le f tmp;
  let h1 = ST.get () in
  lemma_feval_is_fas_nat h1 f;
  assert (forall (i:nat). {:pattern (i < width s) } i < width s ==> (feval h1 f).[i] == (fas_nat h1 f).[i]);
  assert (feval h1 f == LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)));
  LSeq.eq_intro
    (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)))
    (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)));
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) < pow2 (v len * 8));
  assert (F32xN.felem_less #(width s) h1 f (pow2 (v len * 8)));
  set_bit f (len *! 8ul);
  pop_frame()
#pop-options

inline_for_extraction noextract
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
      (feval h1 (gsub p 0ul 5ul)).[0] == S.encode_r (as_seq h0 b))
let poly1305_encode_r #s p b =
  let lo = uint_from_bytes_le (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le (sub b 8ul 8ul) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  load_precompute_r p lo hi

inline_for_extraction noextract
let poly1305_init #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let kr = sub key 0ul 16ul in
  let h0 = ST.get () in
  set_zero acc;
  let h1 = ST.get () in
  lemma_felem_fits_init_post h1 acc;
  poly1305_encode_r #s pre kr

inline_for_extraction noextract
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
      (feval h1 acc).[0] == S.update1
        (feval h0 (gsub p 0ul 5ul)).[0] 16 (as_seq h0 b) (feval h0 acc).[0])
let update1 #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_block e b;
  fadd_mul_r acc e pre;
  pop_frame ()

inline_for_extraction noextract
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
      (feval h1 acc).[0] == S.update1
        (feval h0 (gsub p 0ul 5ul)).[0] (v len) (as_seq h0 b) (feval h0 acc).[0])
let update1_last #s pre len b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_last e len b;
  fadd_mul_r acc e pre;
  pop_frame ()

inline_for_extraction noextract
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
  -> bs:size_t{v bs == width s * S.size_block}
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

#push-options "--max_fuel 1"
inline_for_extraction noextract
val poly1305_update_multi_loop:
    #s:field_spec
  -> bs:size_t{v bs == width s * S.size_block}
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
     (let acc1 = LSeq.repeat_blocks_multi #uint8 #(S.elem (width s)) (v bs) (as_seq h0 text)
       (S.updaten (feval h0 (gsub pre 10ul 5ul))) (feval h0 acc) in
     (feval h1 acc).[0] == S.normalize_n #(width s) acc1 (feval h0 (gsub pre 0ul 5ul)).[0]))
let poly1305_update_multi_loop #s bs len text pre acc =
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
#pop-options

#push-options "--z3rlimit 350"
inline_for_extraction noextract
val poly1305_update_multi:
    #s:field_spec
  -> len:size_t{0 < v len /\ v len % v (blocklen s) == 0}
  -> text:lbuffer uint8 len
  -> pre:precomp_r s
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h pre /\ live h acc /\ live h text /\
      disjoint acc text /\ disjoint acc pre /\
      felem_fits h acc (1, 2, 1, 1, 1) /\
      F32xN.load_precompute_r_post #(width s) h pre)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      (feval h1 acc).[0] ==
      S.poly_update_multi #(width s) (as_seq h0 text)
        (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])
let poly1305_update_multi #s len text pre acc =
  let bs = blocklen s in
  assert (v bs == width s * S.size_block);
  let h0 = ST.get () in
  let text0 = sub text 0ul bs in
  let h1 = ST.get () in
  assert (as_seq h1 text0 == FStar.Seq.slice (as_seq h0 text) 0 (v bs));
  FStar.Seq.Base.lemma_len_slice (as_seq h0 text) 0 (v bs);
  load_acc #s acc text0;
  let len1 = len -! bs in
  let text1 = sub text bs len1 in
  let h2 = ST.get () in
  assert (as_seq h2 text1 == FStar.Seq.slice (as_seq h0 text) (v bs) (v len));
  FStar.Seq.Base.lemma_len_slice (as_seq h0 text) (v bs) (v len);
  assert (feval h0 (gsub pre 10ul 5ul) == S.compute_rw ((feval h0 (gsub pre 0ul 5ul)).[0]));
  poly1305_update_multi_loop #s bs len1 text1 pre acc
#pop-options

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
      (feval h1 acc).[0] ==
      LSeq.repeat_blocks_f #uint8 #(S.pfelem) 16
	(as_seq h0 text) (S.update1 (feval h0 (gsub p 0ul 5ul)).[0] 16) (v nb) (v i) (feval h0 acc).[0])
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
      (feval h1 acc).[0] == S.poly_update1_rem
	(feval h0 (gsub p 0ul 5ul)).[0] (v rem) (as_seq h0 text) (feval h0 acc).[0])
let poly1305_update1_rem #s pre rem b acc =
  if (rem >. 0ul) then update1_last #s pre rem b acc

#push-options "--max_fuel 1"
inline_for_extraction noextract
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
      (feval h1 acc).[0] ==
      S.poly_update1 (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])
let poly1305_update1 #s len text pre acc =
  let nb = len /. 16ul in
  let rem = len %. 16ul in
  let h0 = ST.get () in
  LSeq.lemma_repeat_blocks #uint8 #S.pfelem 16 (as_seq h0 text)
  (S.update1 (feval h0 (gsub pre 0ul 5ul)).[0] 16)
  (S.poly_update1_rem (feval h0 (gsub pre 0ul 5ul)).[0])
  (feval h0 acc).[0];

  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f 16 (as_seq h0 text)
      (S.update1 (feval h0 (gsub pre 0ul 5ul)).[0] 16) (v nb) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies1 acc h0 h /\
    live h pre /\ live h text /\ live h acc /\
    disjoint acc pre /\ disjoint acc text /\
    F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc) /\
    F32xN.fmul_precomp_r_pre #(width s) h pre /\
    (feval h acc).[0] == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc).[0] in

  Lib.Loops.for (size 0) nb inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc).[0] (v i);
      poly1305_update1_f #s pre nb len text i acc);

  let h1 = ST.get () in
  assert ((feval h1 acc).[0] == Lib.LoopCombinators.repeati (v nb) (spec_fh h0) (feval h0 acc).[0]);
  let b = sub text (nb *! 16ul) rem in
  as_seq_gsub h1 text (nb *! 16ul) rem;
  assert (as_seq h1 b == LSeq.sub (as_seq h1 text) (v nb * 16) (v rem));
  assert (disjoint b acc);
  poly1305_update1_rem #s pre rem b acc
#pop-options

inline_for_extraction noextract
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
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 acc) /\
      (feval h1 acc).[0] ==
      S.poly #(width s) (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])

let poly1305_update_ #s len text pre acc =
  let sz_block = blocklen s in
  assert (v sz_block == width s * S.size_block);
  let len0 = (len /. sz_block) *! sz_block in
  let t0 = sub text 0ul len0 in
  let h0 = ST.get () in
  assert (as_seq h0 t0 == FStar.Seq.slice (as_seq h0 text) 0 (v len0));
  FStar.Math.Lemmas.multiple_modulo_lemma (v (len /. sz_block)) (v (blocklen s));
  if len0 >. 0ul then poly1305_update_multi len0 t0 pre acc;

  let len1 = len -! len0 in
  let t1 = sub text len0 len1 in
  let h1 = ST.get () in
  assert (as_seq h1 t1 == FStar.Seq.slice (as_seq h0 text) (v len0) (v len));
  poly1305_update1 #s len1 t1 pre acc

inline_for_extraction noextract
val poly1305_update32: poly1305_update_st M32
let poly1305_update32 ctx len text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  poly1305_update1 #M32 len text pre acc

inline_for_extraction noextract
val poly1305_update_128_256: #s:field_spec { s = M128 || s = M256 } -> poly1305_update_st s
let poly1305_update_128_256 #s ctx len text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  poly1305_update_ #s len text pre acc

inline_for_extraction noextract
let poly1305_update #s =
  match s with
  | M32 -> poly1305_update32
  | _ -> poly1305_update_128_256 #s

inline_for_extraction noextract
let poly1305_finish #s tag key ctx =
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

#set-options "--z3rlimit 150"

inline_for_extraction noextract
let mk_poly1305_mac #s poly1305_init poly1305_update poly1305_finish tag len text key =
  push_frame ();
  let ctx = create (nlimb s +. precomplen s) (limb_zero s) in
  poly1305_init ctx key;
  poly1305_update ctx len text;
  poly1305_finish tag key ctx;
  pop_frame ()
