module Hacl.Bignum

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Base
open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum
module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val bn_mask_lt:
    len:size_t
  -> a:lbignum len
  -> b:lbignum len ->
  Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == v (S.bn_mask_lt (as_seq h0 a) (as_seq h0 b)))


inline_for_extraction noextract
val bn_add_eq_len:
    aLen:size_t
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_add (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_sub_eq_len:
    aLen:size_t
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (c_out, as_seq h1 res) == S.bn_sub (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_add:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum bLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_add (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_sub:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum bLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (c_out, as_seq h1 res) == S.bn_sub (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_add_mod_n:
    len:size_t{v len > 0}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint n a /\ disjoint n b /\ disjoint n res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_add_mod_n (as_seq h0 n) (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_mul:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum bLen
  -> res:lbignum (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_mul1_lshift_add_in_place:
    aLen:size_t
  -> a:lbignum aLen
  -> b:uint64
  -> resLen:size_t
  -> j:size_t{v j + v aLen < v resLen}
  -> res:lbignum resLen ->
  Stack uint64
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul1_lshift_add (as_seq h0 a) b (v j) (as_seq h0 res))


inline_for_extraction noextract
val bn_rshift:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i < v len}
  -> res:lbignum (len -! i) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_rshift (as_seq h0 b) (v i))


inline_for_extraction noextract
val bn_sub_mask:
    len:size_t{v len > 0}
  -> n:lbignum len
  -> a:lbignum len ->
  Stack unit
  (requires fun h -> live h n /\ live h a /\ disjoint n a)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_sub_mask (as_seq h0 n) (as_seq h0 a))


val bn_is_less:
    len:size_t
  -> a:lbignum len
  -> b:lbignum len ->
  Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_less (as_seq h0 a) (as_seq h0 b))

///
///  Get and set i-th bit of a bignum
///

val bn_is_bit_set:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack bool
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_is_bit_set (as_seq h0 b) (v i))


val bn_bit_set:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_bit_set (as_seq h0 b) (v i))

///
///  Conversion functions for bignum
///

inline_for_extraction noextract
val bn_from_bytes_be:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum (blocks len 8ul) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_be (v len) (as_seq h0 b))


inline_for_extraction noextract
val bn_to_bytes_be:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbignum (blocks len 8ul)
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_be (v len) (as_seq h0 b))
