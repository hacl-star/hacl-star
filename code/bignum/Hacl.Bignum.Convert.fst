module Hacl.Bignum.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Bignum.Definitions

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence

module S = Hacl.Spec.Bignum.Convert

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val bn_from_uint:
    #t:limb_t
  -> len:size_t{0 < v len}
  -> x:limb t
  -> b:lbignum t len ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_from_uint (v len) x)

let bn_from_uint #t len x b =
  memset b (uint #t 0) len;
  b.(0ul) <- x


inline_for_extraction noextract
val bn_from_bytes_be_:
    #t:limb_t
  -> len:size_t{numbytes t * v len <= max_size_t}
  -> b:lbuffer uint8 (size (numbytes t) *! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_be_ (v len) (as_seq h0 b))

let bn_from_bytes_be_ #t len b res =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = S.bn_from_bytes_be_f (v len) (as_seq h b) in
  fill h0 len res spec
  (fun j -> uint_from_bytes_be (sub b ((len -! j -! 1ul) *! (size (numbytes t))) (size (numbytes t))))


inline_for_extraction noextract
let bn_from_bytes_be_st (t:limb_t) =
    len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum t (blocks len (size (numbytes t))) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_be (v len) (as_seq h0 b))


inline_for_extraction noextract
val mk_bn_from_bytes_be: #t:limb_t -> bn_from_bytes_be_st t
let mk_bn_from_bytes_be #t len b res =
  [@inline_let]
  let numb = size (numbytes t) in
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len numb in
  let tmpLen = numb *! bnLen in
  let tmp = create tmpLen (u8 0) in
  update_sub tmp (tmpLen -! len) len b;
  bn_from_bytes_be_ bnLen tmp res;
  pop_frame ()


[@CInline]
let bn_from_bytes_be_uint32 : bn_from_bytes_be_st U32 = mk_bn_from_bytes_be #U32
[@CInline]
let bn_from_bytes_be_uint64 : bn_from_bytes_be_st U64 = mk_bn_from_bytes_be #U64


inline_for_extraction noextract
val bn_from_bytes_be: #t:limb_t -> bn_from_bytes_be_st t
let bn_from_bytes_be #t =
  match t with
  | U32 -> bn_from_bytes_be_uint32
  | U64 -> bn_from_bytes_be_uint64


inline_for_extraction noextract
let new_bn_from_bytes_be_st (t:limb_t) =
    r:HS.rid
  -> len:size_t
  -> b:lbuffer uint8 len ->
  ST (B.buffer (limb t))
  (requires fun h ->
    live h b /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t /\
      B.len res == blocks len (size (numbytes t)) /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t (blocks len (size (numbytes t)))) == S.bn_from_bytes_be (v len) (as_seq h0 b)))


inline_for_extraction noextract
val new_bn_from_bytes_be: #t:limb_t -> new_bn_from_bytes_be_st t
let new_bn_from_bytes_be #t r len b =
  [@inline_let]
  let numb = size (numbytes t) in
  if len = 0ul || not (blocks len numb <=. 0xfffffffful `FStar.UInt32.div` numb) then
    B.null
  else
    let h0 = ST.get () in
    let res = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) (blocks len numb) in
    if B.is_null res then
      res
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len res == blocks len numb);
      let res: Lib.Buffer.buffer (limb t) = res in
      assert (B.length res == FStar.UInt32.v (blocks len numb));
      let res: lbignum t (blocks len numb) = res in
      mk_bn_from_bytes_be len b res;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      res


inline_for_extraction noextract
let bn_from_bytes_le_st (t:limb_t) =
    len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum t (blocks len (size (numbytes t))) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_le (v len) (as_seq h0 b))


inline_for_extraction noextract
val mk_bn_from_bytes_le: #t:limb_t -> bn_from_bytes_le_st t
let mk_bn_from_bytes_le #t len b res =
  [@inline_let]
  let numb = size (numbytes t) in
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len numb in
  let tmpLen = numb *! bnLen in
  let tmp = create tmpLen (u8 0) in
  update_sub tmp 0ul len b;
  uints_from_bytes_le res tmp;
  pop_frame ()


[@CInline]
let bn_from_bytes_le_uint32 : bn_from_bytes_le_st U32 = mk_bn_from_bytes_le #U32
[@CInline]
let bn_from_bytes_le_uint64 : bn_from_bytes_le_st U64 = mk_bn_from_bytes_le #U64


inline_for_extraction noextract
val bn_from_bytes_le: #t:limb_t -> bn_from_bytes_le_st t
let bn_from_bytes_le #t =
  match t with
  | U32 -> bn_from_bytes_le_uint32
  | U64 -> bn_from_bytes_le_uint64


inline_for_extraction noextract
val bn_to_bytes_be_:
    #t:limb_t
  -> len:size_t{numbytes t * v len <= max_size_t}
  -> b:lbignum t len
  -> res:lbuffer uint8 (size (numbytes t) *! len) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_be_ (v len) (as_seq h0 b))

let bn_to_bytes_be_ #t len b res =
  let numb = size (numbytes t) in
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = S.bn_to_bytes_be_f (v len) (as_seq h b) in
  fill_blocks h0 numb len res a_spec (fun _ _ -> ()) (fun _ -> LowStar.Buffer.loc_none) spec
  (fun j -> uint_to_bytes_be (sub res (j *! numb) numb) b.(len -! j -! 1ul));
  norm_spec [delta_only [`%S.bn_to_bytes_be_]] (S.bn_to_bytes_be_ (v len) (as_seq h0 b))


inline_for_extraction noextract
let bn_to_bytes_be_st (t:limb_t) (len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}) =
    b:lbignum t (blocks len (size (numbytes t)))
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_be (v len) (as_seq h0 b))


inline_for_extraction noextract
val mk_bn_to_bytes_be:
    #t:limb_t
  -> len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t} ->
  bn_to_bytes_be_st t len

let mk_bn_to_bytes_be #t len b res =
  [@inline_let]
  let numb = size (numbytes t) in
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len numb in
  let tmpLen = numb *! bnLen in
  let tmp = create tmpLen (u8 0) in
  bn_to_bytes_be_ bnLen b tmp;
  copy res (sub tmp (tmpLen -! len) len);
  pop_frame ()


[@CInline]
let bn_to_bytes_be_uint32 len : bn_to_bytes_be_st U32 len = mk_bn_to_bytes_be #U32 len
[@CInline]
let bn_to_bytes_be_uint64 len : bn_to_bytes_be_st U64 len = mk_bn_to_bytes_be #U64 len


inline_for_extraction noextract
val bn_to_bytes_be: #t:_ -> len:_ -> bn_to_bytes_be_st t len
let bn_to_bytes_be #t =
  match t with
  | U32 -> bn_to_bytes_be_uint32
  | U64 -> bn_to_bytes_be_uint64


inline_for_extraction noextract
let bn_to_bytes_le_st (t:limb_t) (len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}) =
    b:lbignum t (blocks len (size (numbytes t)))
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_le (v len) (as_seq h0 b))


inline_for_extraction noextract
val mk_bn_to_bytes_le:
    #t:limb_t
  -> len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t} ->
  bn_to_bytes_le_st t len

let mk_bn_to_bytes_le #t len b res =
  [@inline_let]
  let numb = size (numbytes t) in
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len numb in
  let tmpLen = numb *! bnLen in
  let tmp = create tmpLen (u8 0) in
  uints_to_bytes_le bnLen tmp b;
  copy res (sub tmp 0ul len);
  pop_frame ()


[@CInline]
let bn_to_bytes_le_uint32 len : bn_to_bytes_le_st U32 len = mk_bn_to_bytes_le #U32 len
[@CInline]
let bn_to_bytes_le_uint64 len : bn_to_bytes_le_st U64 len = mk_bn_to_bytes_le #U64 len


inline_for_extraction noextract
val bn_to_bytes_le: #t:_ -> len:_ -> bn_to_bytes_le_st t len
let bn_to_bytes_le #t =
  match t with
  | U32 -> bn_to_bytes_le_uint32
  | U64 -> bn_to_bytes_le_uint64
