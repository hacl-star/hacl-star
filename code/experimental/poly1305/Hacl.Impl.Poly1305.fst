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

friend Lib.Sequence
friend Lib.LoopCombinators

#reset-options "--z3rlimit 50 --max_fuel 2 --using_facts_from '* -FStar.Seq'"

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

#set-options "--z3rlimit 100"

inline_for_extraction
val poly1305_encode_last:
    #s:field_spec
  -> f:felem s
  -> len:size_t{v len < 16}
  -> b:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h b /\ live h f /\ disjoint b f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      (Math.Lemmas.pow2_le_compat 128 (8 * v len);
      assert_norm (pow2 128 < S.prime);
      feval h1 f == LSeq.map (S.pfadd (pow2 (8 * v len)))
        (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)))))
let poly1305_encode_last #s f len b =
  push_frame();
  let tmp = create 16ul (u8 0) in
  copy (sub tmp 0ul len) (sub b 0ul len);
  let h0 = ST.get () in
  assume (BSeq.nat_from_bytes_le (as_seq h0 b) == BSeq.nat_from_bytes_le (as_seq h0 tmp));
  load_felem_le f tmp;
  let h1 = ST.get () in
  assert (feval h1 f == LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)));
  LSeq.eq_intro (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 tmp)))
    (LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)));
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) < pow2 (v len * 8));
  Math.Lemmas.pow2_le_compat 128 (v len * 8);
  assume (F32xN.felem_less #(width s) h1 f (pow2 (v len * 8)));
  set_bit f (len *! 8ul);
  let h2 = ST.get () in
  assert (feval h2 f == LSeq.map (S.pfadd (pow2 (v len * 8))) (feval h1 f));
  pop_frame()

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
type poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s +. precomplen s)

(*
inline_for_extraction
val get_acc: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_acc #s (ctx:poly1305_ctx s) = sub ctx (size 0) (nlimb s)


(*
inline_for_extraction
val get_precomp_r: #s:field_spec -> ctx:poly1305_ctx s -> Stack (precomp_r s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_precomp_r #s (ctx:poly1305_ctx s) = sub ctx (nlimb s) (precomplen s)

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
     (let (acc_s, r_s) = S.poly1305_init (as_seq h0 key) in
      let acc = gsub ctx 0ul (nlimb s) in
      let p = gsub ctx (nlimb s) (precomplen s) in
      F32xN.load_precompute_r_post #(width s) h1 p /\
      feval h1 (gsub p 0ul 5ul) == r_s /\ feval h1 acc == acc_s))
let poly1305_init_ #s ctx key =
  let kr = sub key 0ul 16ul in
  let acc = get_acc ctx in
  let precomp_r = get_precomp_r ctx in
  let h0 = ST.get () in
  set_zero acc;
  let h1 = ST.get () in
  LSeq.eq_intro (feval h1 acc) (fst (S.poly1305_init (as_seq h0 key)));
  poly1305_encode_r precomp_r kr

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_init_32 (ctx:poly1305_ctx M32) (k:lbuffer uint8 32ul) = poly1305_init_ #M32 ctx k
[@CInline]
let poly1305_init_128 (ctx:poly1305_ctx M128) (k:lbuffer uint8 32ul) = poly1305_init_ #M128 ctx k
inline_for_extraction
let poly1305_init_256 (ctx:poly1305_ctx M256) (k:lbuffer uint8 32ul) = poly1305_init_ #M256 ctx k

inline_for_extraction noextract
val poly1305_init:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h key /\ disjoint ctx key)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
     (let (acc_s, r_s) = S.poly1305_init (as_seq h0 key) in
      let acc = gsub ctx 0ul (nlimb s) in
      let p = gsub ctx (nlimb s) (precomplen s) in
      F32xN.load_precompute_r_post #(width s) h1 p /\
      feval h1 (gsub p 0ul 5ul) == r_s /\ feval h1 acc == acc_s))
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
      //F32xN.load_precompute_r_post #(width s) h p)
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
      //F32xN.load_precompute_r_post #(width s) h p)
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
    #s:field_spec{width s == 1}
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
    #s:field_spec{width s == 1}
  -> p:precomp_r s
  -> bs:size_t{v bs == 16} //{v bs == v (blocklen s)}
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
  updaten #s pre block acc

#reset-options "--max_fuel 2 --z3rlimit 150"

unfold
let op_String_Access #a #len = LSeq.index #a #len

inline_for_extraction
val poly1305_update_multi:
    #s:field_spec{width s == 1}
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

inline_for_extraction
val poly1305_update1:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h ctx /\ live h text)
    (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1)
let poly1305_update1 #s ctx len text =
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let blocks = len /. 16ul in
  let rem = len %. 16ul in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks ctx
  (fun i ->
    let b = sub text (i *. 16ul) 16ul in
    update1 #s pre b acc
  );
  if (rem >. 0ul) then (
    let b = sub text (blocks *. 16ul) rem in
    update1_last #s pre rem b acc)

inline_for_extraction
val poly1305_update_:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h ctx /\ live h text)
    (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1)
let poly1305_update_ #s ctx len text = admit();
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let sz_block = blocklen s in
  let len0 = (len /. sz_block) *. sz_block in
  let t0 = sub text 0ul len0 in
  poly1305_update_multi len0 t0 pre acc;

  let len = len -. len0 in
  let text = sub text len0 len in
  poly1305_update1 #s ctx len text

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_update_32 (ctx:poly1305_ctx M32) (len:size_t) (text:lbuffer uint8 len) = poly1305_update1 #M32 ctx len text
[@CInline]
let poly1305_update_128 (ctx:poly1305_ctx M128) (len:size_t) (text:lbuffer uint8 len) = poly1305_update_ #M128 ctx len text
inline_for_extraction
let poly1305_update_256 (ctx:poly1305_ctx M256) (len:size_t) (text:lbuffer uint8 len) = poly1305_update_ #M256 ctx len text

inline_for_extraction noextract
val poly1305_update:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h ctx /\ live h text)
    (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1)
let poly1305_update #s ctx len text =
  match s with
  | M32 -> poly1305_update_32 ctx len text
  | M128 -> poly1305_update_128 ctx len text
  | M256 -> poly1305_update_256 ctx len text
(* WRAPPER to Prevent Inlining *)


inline_for_extraction
val poly1305_finish_:
    #s:field_spec
  -> key:lbuffer uint8 32ul
  -> ctx:poly1305_ctx s
  -> tag:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h -> live h ctx /\ live h tag /\ live h key)
    (ensures  fun h0 _ h1 -> modifies (loc tag) h0 h1)
let poly1305_finish_ #s key ctx tag = admit();
  push_frame ();
  let acc = get_acc ctx in
  reduce_felem acc;

  let ks = sub key (size 16) (size 16) in
  let sk = create (nlimb s) (limb_zero s) in
  load_felem_le sk ks;

  //use u128 addition
  fadd acc acc sk;
  store_felem_le tag acc;
  pop_frame ()

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_finish_32 (key:lbuffer uint8 32ul) (ctx:poly1305_ctx M32) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M32 key ctx tag
[@CInline]
let poly1305_finish_128 (key:lbuffer uint8 32ul) (ctx:poly1305_ctx M128) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M128 key ctx tag
[@CInline]
let poly1305_finish_256 (key:lbuffer uint8 32ul) (ctx:poly1305_ctx M256) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M256 key ctx tag

inline_for_extraction noextract
val poly1305_finish:
    #s:field_spec
  -> key:lbuffer uint8 32ul
  -> ctx:poly1305_ctx s
  -> tag:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h -> live h ctx /\ live h tag /\ live h key)
    (ensures  fun h0 _ h1 -> modifies (loc tag) h0 h1)
let poly1305_finish #s key ctx tag =
   match s with
   | M32 -> poly1305_finish_32 key ctx tag
   | M128 -> poly1305_finish_128 key ctx tag
   | M256 -> poly1305_finish_256 key ctx tag
(* WRAPPER to Prevent Inlining *)



// inline_for_extraction
// val poly1305_mac:
//     #s:field_spec
//   -> tag:lbuffer uint8 16ul
//   -> len:size_t
//   -> text:lbuffer uint8 len
//   -> key:lbuffer uint8 32ul
//   -> Stack unit
//     (requires fun h -> live h text /\ live h tag /\ live h key)
//     (ensures  fun h0 _ h1 -> modifies (loc tag) h0 h1)
let poly1305_mac #s tag len text key =
  push_frame ();
  let ctx = create (nlimb s +. precomplen s) (limb_zero s) in
  poly1305_init ctx key;
  poly1305_update ctx len text;
  poly1305_finish key ctx tag;
  pop_frame ()
