module Hacl.Bignum.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Bignum

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.RSAPSS
module SC = Hacl.Spec.Bignum.Convert


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bignum_from_bytes_:
    len:size_t{8 * v len <= max_size_t}
  -> b:lbuffer uint8 (8ul *! len)
  -> res:lbignum len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == SC.bignum_from_bytes_ (v len) (as_seq h0 b))

let bignum_from_bytes_ len b res =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = SC.bignum_from_bytes_f (v len) (as_seq h b) in
  fill h0 len res spec
  (fun j -> uint_from_bytes_be (sub b ((len -! j -! 1ul) *! 8ul) 8ul))


val bignum_from_bytes:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum (blocks len 8ul) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res == S.os2ip #(v len) (as_seq h0 b))

[@CInline]
let bignum_from_bytes len b res =
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len 8ul in
  let tmpLen = 8ul *! bnLen in
  let tmp = create tmpLen (u8 0) in
  update_sub tmp (tmpLen -! len) len b;
  bignum_from_bytes_ bnLen tmp res;
  SC.bignum_from_bytes_lemma (v len) (as_seq h0 b);
  pop_frame ()


inline_for_extraction noextract
val bignum_to_bytes_:
    len:size_t{8 * v len <= max_size_t}
  -> b:lbignum len
  -> res:lbuffer uint8 (8ul *! len) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == SC.bignum_to_bytes_ (v len) (as_seq h0 b))

let bignum_to_bytes_ len b res =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = SC.bignum_to_bytes_f (v len) (as_seq h b) in
  fill_blocks h0 8ul len res a_spec (fun _ _ -> ()) (fun _ -> LowStar.Buffer.loc_none) spec
  (fun j -> uint_to_bytes_be (sub res (j *! 8ul) 8ul) b.(len -! j -! 1ul));
  assert_norm (SC.bignum_to_bytes_ (v len) (as_seq h0 b) == norm [delta] SC.bignum_to_bytes_ (v len) (as_seq h0 b))


val bignum_to_bytes:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbignum (blocks len 8ul)
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h b /\ live h res /\ disjoint res b /\
    bn_v h b < pow2 (8 * v len))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.i2osp #(v len) (bn_v h0 b))

[@CInline]
let bignum_to_bytes len b res =
  let h0 = ST.get () in
  push_frame ();
  let bnLen = blocks len 8ul in
  let tmpLen = 8ul *! bnLen in
  let tmp = create tmpLen (u8 0) in
  bignum_to_bytes_ bnLen b tmp;
  copy res (sub tmp (tmpLen -! len) len);
  SC.bignum_to_bytes_lemma (v len) (as_seq h0 b);
  pop_frame ()
