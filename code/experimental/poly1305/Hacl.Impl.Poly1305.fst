module Hacl.Impl.Poly1305

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
module S = Spec.Poly1305
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module F32 = Hacl.Impl.Poly1305.Field32
module F64 = Hacl.Impl.Poly1305.Field64
module F128 = Hacl.Impl.Poly1305.Field128
module F256 = Hacl.Impl.Poly1305.Field256

inline_for_extraction
val poly1305_encode_block:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h -> live h b /\ live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      as_nat #s h1 f == pow2 128 + BSeq.nat_from_bytes_le (as_seq h0 b))
let poly1305_encode_block #s f b =
  load_felem_le f b;
  set_bit128 f

inline_for_extraction
val poly1305_encode_blocks:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 (blocklen s)
  -> Stack unit
    (requires fun h -> live h b /\ live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let poly1305_encode_blocks #s f b = admit();
  load_felems_le f b;
  set_bit128 f

#set-options "--max_fuel 0"

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
      as_nat h1 f == pow2 (8 * v len) + BSeq.nat_from_bytes_le (as_seq h0 b))
let poly1305_encode_last #s f len b =
  push_frame();
  let tmp = create 16ul (u8 0) in
  copy (sub tmp 0ul len) (sub b 0ul len);
  let h0 = ST.get () in
  assume (BSeq.nat_from_bytes_le (as_seq h0 tmp) == BSeq.nat_from_bytes_le (as_seq h0 b));
  load_felem_le f tmp;
  let h1 = ST.get () in
  assert (as_nat h1 f == BSeq.nat_from_bytes_le (as_seq h0 tmp));
  assert (BSeq.nat_from_bytes_le (as_seq h0 b) < pow2 (v len * 8));
  set_bit f (len *! 8ul);
  let h2 = ST.get () in
  assert (as_nat h2 f == pow2 (v len * 8) + BSeq.nat_from_bytes_le (as_seq h0 tmp));
  assert (as_nat h2 f == pow2 (8 * v len) + BSeq.nat_from_bytes_le (as_seq h0 b));
  pop_frame()

inline_for_extraction
val poly1305_encode_r:
    #s:field_spec
  -> p:precomp_r s
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h -> live h b /\ live h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
     (let r = gsub p 0ul (nlimb s) in
      let r5 = gsub p (nlimb s) (nlimb s) in
      as_nat h1 r == S.encode_r (as_seq h0 b)))
let poly1305_encode_r #s p b =
  let lo = uint_from_bytes_le (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le (sub b 8ul 8ul) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  load_precompute_r p lo hi;
  admit()

inline_for_extraction
type poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s *. 2ul +. precomplen s)

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

(*
inline_for_extraction
val get_s: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_s #s (ctx:poly1305_ctx s) = sub ctx (nlimb s +. precomplen s) (nlimb s)

#reset-options "--z3rlimit 50 --max_fuel 0"

inline_for_extraction
val poly1305_init_:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h -> live h ctx /\ live h key /\ disjoint ctx key)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      let st : S.state = S.poly1305_init (as_seq h0 key) in
      as_nat h1 acc == S.get_acc st /\
      as_nat h1 r == S.get_r st /\
      as_nat h1 sk == S.get_s st))
let poly1305_init_ #s ctx key =
  let kr = sub key 0ul 16ul in
  let ks = sub key 16ul 16ul in

  let acc = get_acc ctx in
  let precomp_r = get_precomp_r ctx in
  let sk = get_s ctx in

  let h0 = ST.get () in
  set_zero acc;
  poly1305_encode_r precomp_r kr;
  load_felem_le sk ks

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_init_32 (ctx:poly1305_ctx M32) (k:lbuffer uint8 32ul) = poly1305_init_ #M32 ctx k

inline_for_extraction
let poly1305_init_64 (ctx:poly1305_ctx M64) (k:lbuffer uint8 32ul) = poly1305_init_ #M64 ctx k

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
    (requires fun h -> live h ctx /\ live h key /\ disjoint ctx key)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      let st : S.state = S.poly1305_init (as_seq h0 key) in
      as_nat h1 acc == S.get_acc st /\
      as_nat h1 r == S.get_r st /\
      as_nat h1 sk == S.get_s st))
let poly1305_init #s ctx key =
  match s with
  | M32 -> poly1305_init_32 ctx key
  | M64 -> poly1305_init_64 ctx key
  | M128 -> poly1305_init_128 ctx key
  | M256 -> poly1305_init_256 ctx key
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val poly1305_nblocks:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t{v len % v (blocklen s) == 0}
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h ctx /\ live h text)
    (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1)
let poly1305_nblocks #s ctx len text =
  push_frame();
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let e = create (nlimb s) (limb_zero s) in

  let sz_block = blocklen s in
  let blocks = len /. sz_block  in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks ctx
  (fun i ->
    let b = sub text (i *! sz_block) sz_block in
    poly1305_encode_blocks e b;
    fmul_rn acc acc pre;
    fadd acc acc e
  );
  fmul_rn_normalize acc pre;
  pop_frame()

inline_for_extraction
val poly1305_update_:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h text /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      as_nat h r < S.prime /\ as_nat h sk < S.prime /\ as_nat h acc < S.prime))
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      let st : S.state = S.poly (as_seq h0 text)
	(S.create_st (as_nat h0 r) (as_nat h0 sk) (as_nat h0 acc)) in
      as_nat h1 acc == S.get_acc st /\
      as_nat h1 r == S.get_r st /\
      as_nat h1 sk == S.get_s st /\
      fadd_carry_pre h1 acc sk))
let poly1305_update_ #s ctx len text = admit();
  push_frame();
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in

  let sz_block = blocklen s in
  let len0 = if sz_block >. 16ul then (len /. sz_block) *. sz_block else 0ul in
  if (sz_block >. 16ul) then (
    let t0 = sub text 0ul len0 in
    poly1305_nblocks ctx len0 t0
  );

  let len = len -. len0 in
  let text = sub text len0 len in
  let e = create (nlimb s) (limb_zero s) in
  let blocks = len /. 16ul in
  let h0 = ST.get() in
  loop_nospec #h0 blocks ctx
  (fun i ->
    let b = sub text (i *! 16ul) 16ul in
    poly1305_encode_block e b;
    fadd_mul_r acc e pre
  );

  let rem = len %. 16ul in
  if (rem >. 0ul) then (
    let b = sub text (blocks *! 16ul) 16ul in
    poly1305_encode_last e rem b;
    fadd_mul_r acc e pre);
  reduce_felem acc;
  pop_frame()

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_update_32 (ctx:poly1305_ctx M32) (len:size_t) (text:lbuffer uint8 len) = poly1305_update_ #M32 ctx len text

inline_for_extraction
let poly1305_update_64 (ctx:poly1305_ctx M64) (len:size_t) (text:lbuffer uint8 len) = poly1305_update_ #M64 ctx len text

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
    (requires fun h ->
      live h ctx /\ live h text /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      as_nat h r < S.prime /\ as_nat h sk < S.prime /\ as_nat h acc < S.prime))
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      let st : S.state = S.poly (as_seq h0 text)
	(S.create_st (as_nat h0 r) (as_nat h0 sk) (as_nat h0 acc)) in
      as_nat h1 acc == S.get_acc st /\
      as_nat h1 r == S.get_r st /\
      as_nat h1 sk == S.get_s st /\
      fadd_carry_pre h1 acc sk))
let poly1305_update #s ctx len text =
  match s with
  | M32 -> poly1305_update_32 ctx len text
  | M64 -> poly1305_update_64 ctx len text
  | M128 -> poly1305_update_128 ctx len text
  | M256 -> poly1305_update_256 ctx len text
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val poly1305_finish_:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> tag:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h tag /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      as_nat h r < S.prime /\ as_nat h sk < S.prime /\ as_nat h acc < S.prime /\
      fadd_carry_pre h acc sk))
    (ensures  fun h0 _ h1 ->
      modifies (loc tag |+| loc ctx) h0 h1 /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      as_seq h1 tag == S.finish (S.create_st (as_nat h0 r) (as_nat h0 sk) (as_nat h0 acc))))
let poly1305_finish_ #s ctx tag =
  let acc = get_acc ctx in
  let sk = get_s ctx in

  fadd_carry acc acc sk;
  store_felem_le tag acc

(* WRAPPER TO PREVENT INLINING *)
[@CInline]
let poly1305_finish_32 (ctx:poly1305_ctx M32) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M32 ctx tag

inline_for_extraction
let poly1305_finish_64 (ctx:poly1305_ctx M64) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M64 ctx tag

[@CInline]
let poly1305_finish_128 (ctx:poly1305_ctx M128) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M128 ctx tag

inline_for_extraction
let poly1305_finish_256 (ctx:poly1305_ctx M256) (tag:lbuffer uint8 16ul) = poly1305_finish_ #M256 ctx tag

inline_for_extraction noextract
val poly1305_finish:
    #s:field_spec
  -> ctx:poly1305_ctx s
  -> tag:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h tag /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      as_nat h r < S.prime /\ as_nat h sk < S.prime /\ as_nat h acc < S.prime /\
      fadd_carry_pre h acc sk))
    (ensures  fun h0 _ h1 ->
      modifies (loc tag |+| loc ctx) h0 h1 /\
     (let acc = gsub ctx 0ul (nlimb s) in
      let precomp_r = gsub ctx (nlimb s) (precomplen s) in
      let r = gsub precomp_r 0ul (nlimb s) in
      let sk = gsub ctx (nlimb s +. precomplen s) (nlimb s) in
      as_seq h1 tag == S.finish (S.create_st (as_nat h0 r) (as_nat h0 sk) (as_nat h0 acc))))
let poly1305_finish #s ctx tag =
  match s with
  | M32 -> poly1305_finish_32 ctx tag
  | M64 -> poly1305_finish_64 ctx tag
  | M128 -> poly1305_finish_128 ctx tag
  | M256 -> poly1305_finish_256 ctx tag
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val poly1305_mac:
    #s:field_spec
  -> tag:lbuffer uint8 16ul
  -> len:size_t
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h text /\ live h tag /\ live h key /\
      disjoint tag text /\ disjoint tag key)
    (ensures  fun h0 _ h1 ->
       modifies (loc tag) h0 h1 /\
       as_seq h1 tag == S.poly1305 (as_seq h0 text) (as_seq h0 key))
let poly1305_mac #s tag len text key =
  push_frame();
  let ctx = create (nlimb s *. 2ul +. precomplen s) (limb_zero s) in
  poly1305_init ctx key;
  poly1305_update ctx len text;
  poly1305_finish ctx tag;
  pop_frame ()
