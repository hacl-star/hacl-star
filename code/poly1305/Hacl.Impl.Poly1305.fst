module Hacl.Impl.Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Fields
module F32xN = Hacl.Impl.Poly1305.Field32xN

module Scalar = Spec.Poly1305
module Vec = Hacl.Spec.Poly1305.Vec

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

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
  (ensures pow2 n < Scalar.prime)
  [SMTPat (pow2 n)]
let lemma_pow2_128 n =
  Math.Lemmas.pow2_le_compat 128 n;
  assert (pow2 n <= pow2 128);
  assert_norm (pow2 128 < Scalar.prime)

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
      (feval h1 f).[0] == pow2 128 + BSeq.nat_from_bytes_le (as_seq h0 b))
let poly1305_encode_block #s f b =
  load_felem_le f b;
  let h0 = ST.get () in
  set_bit128 f;
  let h1 = ST.get () in
  assert ((feval h1 f).[0] == Scalar.fadd (pow2 128) (BSeq.nat_from_bytes_le (as_seq h0 b)));
  assert_norm (pow2 128 + pow2 128 < Scalar.prime);
  FStar.Math.Lemmas.modulo_lemma (pow2 128 + BSeq.nat_from_bytes_le (as_seq h0 b)) Scalar.prime

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
      feval h1 f == Vec.load_blocks #(width s) (as_seq h0 b))
let poly1305_encode_blocks #s f b =
  load_felems_le f b;
  set_bit128 f

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
      (feval h1 f).[0] == pow2 (8 * v len) + BSeq.nat_from_bytes_le (as_seq h0 b))
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
  //assert (forall (i:nat). i < width s ==> (feval h1 f).[i] == (fas_nat h1 f).[i]);
  //assert (feval h1 f == LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)));
  //LSeq.eq_intro
    //(LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)))
    //(LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)));

  //assert (F32xN.felem_less #(width s) h1 f (pow2 (v len * 8)));
  set_bit f (len *! 8ul);
  let h2 = ST.get () in
  assert ((feval h2 f).[0] == Scalar.fadd (pow2 (v len * 8)) (BSeq.nat_from_bytes_le (as_seq h0 b)));
  Math.Lemmas.pow2_lt_compat 128 (8 * v len);
  assert_norm (pow2 128 + pow2 128 < Scalar.prime);
  FStar.Math.Lemmas.modulo_lemma (pow2 (8 * v len) + BSeq.nat_from_bytes_le (as_seq h0 b)) Scalar.prime;
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
      (feval h1 (gsub p 0ul 5ul)).[0] == Scalar.poly1305_encode_r (as_seq h0 b))
let poly1305_encode_r #s p b =
  let lo = uint_from_bytes_le (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le (sub b 8ul 8ul) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  load_precompute_r p lo hi

inline_for_extraction noextract
val poly1305_init_: #s:field_spec -> poly1305_init_st s
let poly1305_init_ #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let kr = sub key 0ul 16ul in
  let h0 = ST.get () in
  set_zero acc;
  let h1 = ST.get () in
  lemma_felem_fits_init_post h1 acc;
  poly1305_encode_r #s pre kr

[@CInline]
let poly1305_init_32 : poly1305_init_st M32 = poly1305_init_ #M32
[@CInline]
let poly1305_init_128 : poly1305_init_st M128 = poly1305_init_ #M128
[@CInline]
let poly1305_init_256 : poly1305_init_st M256 = poly1305_init_ #M256

let poly1305_init #s ctx key =
  match s with
  | M32 -> poly1305_init_32 ctx key
  | M128 -> poly1305_init_128 ctx key
  | M256 -> poly1305_init_256 ctx key

inline_for_extraction noextract
let update1_st (s:field_spec) =
    p:precomp_r s
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
      (feval h1 acc).[0] == Scalar.poly1305_update1
        (feval h0 (gsub p 0ul 5ul)).[0] 16 (as_seq h0 b) (feval h0 acc).[0])

inline_for_extraction noextract
val update1_: #s:field_spec -> update1_st s
let update1_ #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_block e b;
  fadd_mul_r acc e pre;
  pop_frame ()

[@CInline]
let poly1305_update1_32 : update1_st M32 = update1_
[@CInline]
let poly1305_update1_128 : update1_st M128 = update1_
[@CInline]
let poly1305_update1_256 : update1_st M256 = update1_

inline_for_extraction noextract
val update1: (#s:field_spec) -> update1_st s
let update1 #s =
  match s with
  | M32 -> poly1305_update1_32
  | M128 -> poly1305_update1_128
  | M256 -> poly1305_update1_256

let poly1305_update1 #s ctx text =
  let pre = get_precomp_r ctx in
  let acc = get_acc ctx in
  update1 pre text acc

inline_for_extraction noextract
let update1_last_st (s:field_spec) =
    p:precomp_r s
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
      (feval h1 acc).[0] == Scalar.poly1305_update1
        (feval h0 (gsub p 0ul 5ul)).[0] (v len) (as_seq h0 b) (feval h0 acc).[0])

inline_for_extraction noextract
val update1_last_: #s:field_spec -> update1_last_st s
let update1_last_ #s pre len b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_last e len b;
  fadd_mul_r acc e pre;
  pop_frame ()

[@CInline]
let poly1305_update1_last_32 : update1_last_st M32 = update1_last_
[@CInline]
let poly1305_update1_last_128 : update1_last_st M128 = update1_last_
[@CInline]
let poly1305_update1_last_256 : update1_last_st M256 = update1_last_

inline_for_extraction noextract
val update1_last: #s:field_spec -> update1_last_st s
let update1_last #s =
  match s with
  | M32 -> poly1305_update1_last_32
  | M128 -> poly1305_update1_last_128
  | M256 -> poly1305_update1_last_256

inline_for_extraction noextract
let updaten_st (s:field_spec) =
    p:precomp_r s
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
        Vec.poly1305_update_nblocks #(width s) (feval h0 (gsub p 10ul 5ul)) (as_seq h0 b) (feval h0 acc))

inline_for_extraction noextract
val updaten_: #s:field_spec -> updaten_st s
let updaten_ #s pre b acc =
  push_frame ();
  let e = create (nlimb s) (limb_zero s) in
  poly1305_encode_blocks e b;
  fmul_rn acc acc pre;
  fadd acc acc e;
  pop_frame ()

[@CInline]
let poly1305_updaten_32 : updaten_st M32 = updaten_ #M32
[@CInline]
let poly1305_updaten_128 : updaten_st M128 = updaten_ #M128
[@CInline]
let poly1305_updaten_256 : updaten_st M256 = updaten_ #M256

inline_for_extraction noextract
val updaten: #s:field_spec -> updaten_st s
let updaten #s pre b acc =
  match s with
  | M32 -> poly1305_updaten_32 pre b acc
  | M128 -> poly1305_updaten_128 pre b acc
  | M256 -> poly1305_updaten_256 pre b acc

inline_for_extraction noextract
val poly1305_update_multi_f:
    #s:field_spec
  -> p:precomp_r s
  -> bs:size_t{v bs == width s * Scalar.size_block}
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
      LSeq.repeat_blocks_f #uint8 #(Vec.elem (width s))
	(v bs) (as_seq h0 text) (Vec.poly1305_update_nblocks #(width s) (feval h0 (gsub p 10ul 5ul))) (v nb) (v i) (feval h0 acc))

let poly1305_update_multi_f #s pre bs nb len text i acc=
  assert ((v i + 1) * v bs <= v nb * v bs);
  let block = sub #_ #_ #len text (i *! bs) bs in
  let h1 = ST.get () in
  as_seq_gsub h1 text (i *! bs) bs;
  updaten #s pre block acc

#set-options "--max_fuel 1"

inline_for_extraction noextract
val poly1305_update_multi_loop:
    #s:field_spec
  -> bs:size_t{v bs == width s * Scalar.size_block}
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
     (let acc1 = LSeq.repeat_blocks_multi #uint8 #(Vec.elem (width s)) (v bs) (as_seq h0 text)
       (Vec.poly1305_update_nblocks (feval h0 (gsub pre 10ul 5ul))) (feval h0 acc) in
     (feval h1 acc).[0] == Vec.normalize_n #(width s) acc1 (feval h0 (gsub pre 0ul 5ul)).[0]))
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
    felem_fits h acc (2, 3, 2, 2, 2) /\
    F32xN.load_precompute_r_post #(width s) h pre /\
    feval h acc == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc) in

  Lib.Loops.for (size 0) nb inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc) (v i);
      poly1305_update_multi_f #s pre bs nb len text i acc);
  fmul_rn_normalize acc pre

#set-options "--z3rlimit 500 --max_fuel 0"

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
      Vec.poly1305_update_multi #(width s) (as_seq h0 text)
        (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])
let poly1305_update_multi #s len text pre acc =
  let bs = blocklen s in
  assert (v bs == width s * Vec.size_block);
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
  assert (feval h0 (gsub pre 10ul 5ul) == Vec.compute_rw ((feval h0 (gsub pre 0ul 5ul)).[0]));
  poly1305_update_multi_loop #s bs len1 text1 pre acc

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
      LSeq.repeat_blocks_f #uint8 #(Scalar.felem) 16
	(as_seq h0 text) (Scalar.poly1305_update1 (feval h0 (gsub p 0ul 5ul)).[0] 16) (v nb) (v i) (feval h0 acc).[0])
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
      (feval h1 acc).[0] == Scalar.poly1305_update_last
	(feval h0 (gsub p 0ul 5ul)).[0] (v rem) (as_seq h0 text) (feval h0 acc).[0])
let poly1305_update1_rem #s pre rem b acc =
  if (rem >. 0ul) then update1_last #s pre rem b acc

#set-options "--max_fuel 1"

inline_for_extraction noextract
val poly1305_update_scalar:
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
      Scalar.poly1305_update (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])
let poly1305_update_scalar #s len text pre acc =
  let nb = len /. 16ul in
  let rem = len %. 16ul in
  let h0 = ST.get () in
  LSeq.lemma_repeat_blocks #uint8 #Scalar.felem 16 (as_seq h0 text)
  (Scalar.poly1305_update1 (feval h0 (gsub pre 0ul 5ul)).[0] 16)
  (Scalar.poly1305_update_last (feval h0 (gsub pre 0ul 5ul)).[0])
  (feval h0 acc).[0];

  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f 16 (as_seq h0 text)
      (Scalar.poly1305_update1 (feval h0 (gsub pre 0ul 5ul)).[0] 16) (v nb) in

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

inline_for_extraction noextract
val poly1305_update_vec:
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
      Vec.poly1305_update_vec #(width s) (as_seq h0 text) (feval h0 acc).[0] (feval h0 (gsub pre 0ul 5ul)).[0])
let poly1305_update_vec #s len text pre acc =
  let sz_block = blocklen s in
  assert (v sz_block == width s * Vec.size_block);
  let len0 = (len /. sz_block) *! sz_block in
  let t0 = sub text 0ul len0 in
  let h0 = ST.get () in
  assert (as_seq h0 t0 == FStar.Seq.slice (as_seq h0 text) 0 (v len0));
  //FStar.Math.Lemmas.multiple_modulo_lemma (v (len /. sz_block)) (v (blocklen s));
  if len0 >. 0ul then poly1305_update_multi len0 t0 pre acc;

  let len1 = len -! len0 in
  let t1 = sub text len0 len1 in
  let h1 = ST.get () in
  assert (as_seq h1 t1 == FStar.Seq.slice (as_seq h0 text) (v len0) (v len));
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
  poly1305_update_vec #s len text pre acc

inline_for_extraction noextract
let poly1305_update #s =
  match s with
  | M32 -> poly1305_update32
  | _ -> poly1305_update_128_256 #s

inline_for_extraction noextract
val poly1305_finish_: #s:field_spec -> poly1305_finish_st s
let poly1305_finish_ #s tag key ctx =
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

[@CInline]
let poly1305_finish_32 : poly1305_finish_st M32 = poly1305_finish_ #M32
[@CInline]
let poly1305_finish_128 : poly1305_finish_st M128 = poly1305_finish_ #M128
[@CInline]
let poly1305_finish_256 : poly1305_finish_st M256 = poly1305_finish_ #M256

let poly1305_finish #s tag key ctx =
  match s with
  | M32 -> poly1305_finish_32 tag key ctx
  | M128 -> poly1305_finish_128 tag key ctx
  | M256 -> poly1305_finish_256 tag key ctx

#set-options "--z3rlimit 150"

let mk_poly1305_mac #s poly1305_init poly1305_update poly1305_finish tag len text key =
  push_frame ();
  let ctx = create (nlimb s +. precomplen s) (limb_zero s) in
  poly1305_init ctx key;
  poly1305_update ctx len text;
  poly1305_finish tag key ctx;
  pop_frame ()
