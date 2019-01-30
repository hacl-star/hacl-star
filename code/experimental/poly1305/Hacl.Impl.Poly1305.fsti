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
module F32xN = Hacl.Impl.Poly1305.Field32xN

#reset-options "--z3rlimit 50"

inline_for_extraction
val poly1305_init:
    #s:field_spec
  -> key:lbuffer uint8 32ul
  -> pre:precomp_r s
  -> acc:felem s
  -> Stack unit
    (requires fun h ->
      live h pre /\ live h acc /\  live h key /\
      disjoint pre key /\ disjoint acc key /\
      disjoint pre acc)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc |+| loc pre) h0 h1 /\
      F32xN.load_precompute_r_post #(width s) h1 pre /\
      felem_fits h1 acc (0, 0, 0, 0, 0) /\
      (feval h1 acc, feval h1 (gsub pre 0ul 5ul)) == S.poly1305_init (as_seq h0 key))

inline_for_extraction
val poly1305_update:
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
      feval h1 acc ==
      S.poly #(width s) (as_seq h0 text) (feval h0 acc) (feval h0 (gsub pre 0ul 5ul)))

inline_for_extraction noextract
val poly1305_finish:
    #s:field_spec
  -> key:lbuffer uint8 32ul
  -> acc:felem s
  -> tag:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h tag /\ live h key /\
      disjoint acc tag /\ disjoint key tag /\
      disjoint acc key /\
      F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h acc))
    (ensures  fun h0 _ h1 ->
      modifies (loc tag |+| loc acc) h0 h1 /\
      as_seq h1 tag == S.finish #(width s) (as_seq h0 key) (feval h0 acc))

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
      as_seq h1 tag == S.poly1305 #(width s) (as_seq h0 text) (as_seq h0 key))
