module Hacl.Bignum.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.Convert

module HS = FStar.HyperStack


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val bn_from_uint:
    len:size_t{0 < v len}
  -> x:uint64
  -> b:lbignum len ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_from_uint (v len) x)

let bn_from_uint len x b =
  memset b (u64 0) len;
  b.(0ul) <- x


inline_for_extraction noextract
val bn_from_bytes_be_:
    len:size_t{8 * v len <= max_size_t}
  -> b:lbuffer uint8 (8ul *! len)
  -> res:lbignum len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_be_ (v len) (as_seq h0 b))

let bn_from_bytes_be_ len b res =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = S.bn_from_bytes_be_f (v len) (as_seq h b) in
  fill h0 len res spec
  (fun j -> uint_from_bytes_be (sub b ((len -! j -! 1ul) *! 8ul) 8ul))


inline_for_extraction noextract
val mk_bn_from_bytes_be:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum (blocks len 8ul) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_be (v len) (as_seq h0 b))

let mk_bn_from_bytes_be len b res =
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len 8ul in
  let tmpLen = 8ul *! bnLen in
  let tmp = create tmpLen (u8 0) in
  update_sub tmp (tmpLen -! len) len b;
  bn_from_bytes_be_ bnLen tmp res;
  pop_frame ()

[@CInline]
let bn_from_bytes_be = mk_bn_from_bytes_be

inline_for_extraction noextract
let new_bn_from_bytes_be_st =
    r:HS.rid
  -> len:size_t
  -> b:lbuffer uint8 len ->
  ST (B.buffer uint64)
  (requires fun h ->
    live h b /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t /\
      B.len res == blocks len 8ul /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum (blocks len 8ul))  == S.bn_from_bytes_be (v len) (as_seq h0 b)))

inline_for_extraction noextract
val new_bn_from_bytes_be: new_bn_from_bytes_be_st

let new_bn_from_bytes_be r len b =
  if len = 0ul || not (blocks len 8ul <=. 0xfffffffful `FStar.UInt32.div` 8ul) then
    B.null
  else
    let h0 = ST.get () in
    let res = LowStar.Monotonic.Buffer.mmalloc_partial r (u64 0) (blocks len 8ul) in
    if B.is_null res then
      res
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len res == blocks len 8ul);
      let res: Lib.Buffer.buffer Lib.IntTypes.uint64 = res in
      assert (B.length res == FStar.UInt32.v (blocks len 8ul));
      let res: lbignum (blocks len 8ul) = res in
      mk_bn_from_bytes_be len b res;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      res

val bn_from_bytes_le:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum (blocks len 8ul) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_le (v len) (as_seq h0 b))

[@CInline]
let bn_from_bytes_le len b res =
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len 8ul in
  let tmpLen = 8ul *! bnLen in
  let tmp = create tmpLen (u8 0) in
  update_sub tmp 0ul len b;
  uints_from_bytes_le res tmp;
  pop_frame ()


inline_for_extraction noextract
val bn_to_bytes_be_:
    len:size_t{8 * v len <= max_size_t}
  -> b:lbignum len
  -> res:lbuffer uint8 (8ul *! len) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_be_ (v len) (as_seq h0 b))

let bn_to_bytes_be_ len b res =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = S.bn_to_bytes_be_f (v len) (as_seq h b) in
  fill_blocks h0 8ul len res a_spec (fun _ _ -> ()) (fun _ -> LowStar.Buffer.loc_none) spec
  (fun j -> uint_to_bytes_be (sub res (j *! 8ul) 8ul) b.(len -! j -! 1ul));
  norm_spec [delta_only [`%S.bn_to_bytes_be_]] (S.bn_to_bytes_be_ (v len) (as_seq h0 b))


inline_for_extraction noextract
let bn_to_bytes_be_st (len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}) =
    b:lbignum (blocks len 8ul)
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_be (v len) (as_seq h0 b))

inline_for_extraction noextract
val mk_bn_to_bytes_be: len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t} -> bn_to_bytes_be_st len

let mk_bn_to_bytes_be len b res =
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len 8ul in
  let tmpLen = 8ul *! bnLen in
  let tmp = create tmpLen (u8 0) in
  bn_to_bytes_be_ bnLen b tmp;
  copy res (sub tmp (tmpLen -! len) len);
  pop_frame ()

/// This wrapper avoids inlining in callers to preserve the shape of the RSAPSS code.
[@CInline]
let bn_to_bytes_be = mk_bn_to_bytes_be

val bn_to_bytes_le:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbignum (blocks len 8ul)
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_le (v len) (as_seq h0 b))

[@CInline]
let bn_to_bytes_le len b res =
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len 8ul in
  let tmpLen = 8ul *! bnLen in
  let tmp = create tmpLen (u8 0) in
  uints_to_bytes_le bnLen tmp b;
  copy res (sub tmp 0ul len);
  pop_frame ()
