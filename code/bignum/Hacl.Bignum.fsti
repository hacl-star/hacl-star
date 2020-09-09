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
val bn_reduce_once:
    aLen:size_t{v aLen > 0}
  -> n:lbignum aLen
  -> c:carry
  -> a:lbignum aLen ->
  Stack unit
  (requires fun h -> live h a /\ live h n /\ disjoint a n)
  (ensures  fun h0 c_out h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_reduce_once (as_seq h0 n) c (as_seq h0 a))


inline_for_extraction noextract
let bn_add_mod_n_st (len:size_t{v len > 0}) =
    n:lbignum len
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
val bn_add_mod_n: len:size_t{v len > 0} -> bn_add_mod_n_st len


inline_for_extraction noextract
let bn_karatsuba_mul_st (#aLen:size_t{0 < v aLen /\ 4 * v aLen <= max_size_t})
  (a:lbignum aLen)
  (b:lbignum aLen) =
  res:lbignum (aLen +! aLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))

inline_for_extraction noextract
val bn_karatsuba_mul:
    aLen:size_t{0 < v aLen /\ 4 * v aLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> bn_karatsuba_mul_st a b


inline_for_extraction noextract
let bn_mul_st (#aLen:size_t)
  (a:lbignum aLen)
  (#bLen:size_t{v aLen + v bLen <= max_size_t})
  (b:lbignum bLen) =
  res:lbignum (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))

inline_for_extraction noextract
val bn_mul:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum bLen
  -> bn_mul_st a b


inline_for_extraction noextract
let bn_karatsuba_sqr_st (#aLen:size_t{0 < v aLen /\ 4 * v aLen <= max_size_t})
  (a:lbignum aLen) =
  res:lbignum (aLen +! aLen) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 a))


inline_for_extraction noextract
val bn_karatsuba_sqr:
    aLen:size_t{0 < v aLen /\ 4 * v aLen <= max_size_t}
  -> a:lbignum aLen
  -> bn_karatsuba_sqr_st a


inline_for_extraction noextract
let bn_sqr_st (#aLen:size_t{0 < v aLen /\ v aLen + v aLen <= max_size_t})
  (a:lbignum aLen) =
  res:lbignum (aLen +! aLen) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 a))

inline_for_extraction noextract
val bn_sqr:
    aLen:size_t{0 < v aLen /\ v aLen + v aLen <= max_size_t}
  -> a:lbignum aLen
  -> bn_sqr_st a

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
let bn_sub_mask_st (len:size_t{v len > 0}) =
    n:lbignum len
  -> a:lbignum len ->
  Stack unit
  (requires fun h -> live h n /\ live h a /\ disjoint n a)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_sub_mask (as_seq h0 n) (as_seq h0 a))

inline_for_extraction noextract
val bn_sub_mask: len:size_t{v len > 0} -> bn_sub_mask_st len
///
///  Get and set i-th bit of a bignum
///

val bn_get_ith_bit:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_get_ith_bit (as_seq h0 b) (v i))

/// A now common pattern in HACL*: inline_for_extraction and stateful type
/// abbreviations, to maximize code sharing.
inline_for_extraction noextract
let bn_set_ith_bit_st (len:size_t) =
    b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_set_ith_bit (as_seq h0 b) (v i))

val bn_set_ith_bit: len:size_t -> bn_set_ith_bit_st len


inline_for_extraction noextract
val bn_get_num_bits:
    len:size_t{0 < v len /\ 64 * v len <= max_size_t}
  -> b:lbignum len ->
  Stack size_t
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.bn_get_num_bits (as_seq h0 b))


inline_for_extraction noextract
val cswap2:
    len:size_t
  -> bit:uint64
  -> b1:lbuffer uint64 len
  -> b2:lbuffer uint64 len ->
  Stack unit
  (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
  (ensures  fun h0 _ h1 -> modifies (loc b1 |+| loc b2) h0 h1 /\
    (as_seq h1 b1, as_seq h1 b2) == S.cswap2 bit (as_seq h0 b1) (as_seq h0 b2))


/// Start of the len-based specialization infrastructure.
///
/// Essentially, we wish to describe a type class of basic bignum operations
/// needed to implement Montgomery reduction. This will allow us to generate
/// specialized versions of modular exponentiation for a given bignum size.
///
/// This is done "by hand" because the specialization pattern is more
/// complicated than other pieces of code (chacha, poly, curve), meaning I don't
/// (yet) know how to automate it with a tactic. So, a type class seems like the
/// most efficient way to go about it.
///
/// The operations of the type class were found by essentially reading the code,
/// writing down which operations from Hacl.Bignum are (transitively) needed to
/// implement modular exponentiation, and figuring out for each call-site
/// whether they can be specialized for the bignum size, or whether they have to
/// been inline-for-extraction'd.

#set-options "--fuel 0 --ifuel 0"

let meta_len = len: size_t { 0 < v len /\ 128 * v len <= max_size_t }

/// This type class is entirely meta-level and will not appear after partial
/// evaluation in the resulting C code. Clients can take this type class as a
/// parameter if they want the benefits of a function set specialized for a
/// given bignum length.
inline_for_extraction noextract
class bn (len: meta_len) = {
  bit_set: bn_set_ith_bit_st len;
  add_mod_n: bn_add_mod_n_st len;
  mul: a:lbignum len -> b:lbignum len -> bn_karatsuba_mul_st a b;
  sqr: a:lbignum len -> bn_karatsuba_sqr_st a;
  sub_mask: bn_sub_mask_st len;
}

/// This is a default implementation that *will* generate code depending on
/// `len` at run-time! Only use if you want to generate run-time generic
/// functions!
inline_for_extraction noextract
let mk_runtime_bn (len: meta_len) = {
  bit_set = bn_set_ith_bit len;
  add_mod_n = bn_add_mod_n len;
  mul = (fun a b -> bn_karatsuba_mul len a b);
  sqr = (fun a -> bn_karatsuba_sqr len a);
  sub_mask = bn_sub_mask len;
}

///
///  Bignum comparison and test functions
///

inline_for_extraction noextract
val bn_is_odd:
    len:size_t{v len > 0}
  -> a:lbignum len ->
  Stack uint64
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_odd #(v len) (as_seq h0 a))


inline_for_extraction noextract
val bn_eq_mask:
    len:size_t
  -> a:lbignum len
  -> b:lbignum len ->
  Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_eq_mask #(v len) (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_is_zero_mask:
    len:size_t{v len > 0}
  -> a:lbignum len ->
  Stack uint64
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_zero_mask #(v len) (as_seq h0 a))


inline_for_extraction noextract
let bn_lt_mask_st (len:size_t) =
    a:lbignum len
  -> b:lbignum len ->
  Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == v (S.bn_lt_mask (as_seq h0 a) (as_seq h0 b)))


inline_for_extraction noextract
val mk_bn_lt_mask: len:size_t -> bn_lt_mask_st len

val bn_lt_mask: len:size_t -> bn_lt_mask_st len


inline_for_extraction noextract
val bn_lt_pow2_mask:
    len:size_t{0 < v len /\ 64 * v len <= max_size_t}
  -> b:lbignum len
  -> x:size_t{v x < 64 * v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_lt_pow2_mask #(v len) (as_seq h0 b) (v x))


inline_for_extraction noextract
val bn_gt_pow2_mask:
    len:size_t{0 < v len /\ 64 * v len <= max_size_t}
  -> b:lbignum len
  -> x:size_t{v x < 64 * v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_gt_pow2_mask #(v len) (as_seq h0 b) (v x))

///
///  Conversion functions for bignum
///

inline_for_extraction noextract
val bn_from_uint:
    len:size_t{0 < v len}
  -> x:uint64
  -> b:lbignum len ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_from_uint (v len) x)


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


inline_for_extraction noextract
val bn_from_bytes_le:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum (blocks len 8ul) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_le (v len) (as_seq h0 b))


inline_for_extraction noextract
val bn_to_bytes_le:
    len:size_t{0 < v len /\ 8 * v (blocks len 8ul) <= max_size_t}
  -> b:lbignum (blocks len 8ul)
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_le (v len) (as_seq h0 b))
