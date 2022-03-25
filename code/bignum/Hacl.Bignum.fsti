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
val bn_add1:
    #t:limb_t
  -> aLen:size_t{0 < v aLen}
  -> a:lbignum t aLen
  -> b1:limb t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_add1 (as_seq h0 a) b1 in
    c_out == c /\ as_seq h1 res == r))


inline_for_extraction noextract
val bn_sub1:
    #t:limb_t
  -> aLen:size_t{0 < v aLen}
  -> a:lbignum t aLen
  -> b1:limb t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_sub1 (as_seq h0 a) b1 in
    c_out == c /\ as_seq h1 res == r))


inline_for_extraction noextract
let bn_add_eq_len_st (t:limb_t) (len:size_t) =
     a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_add (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_add_eq_len: #t:limb_t -> len:size_t -> bn_add_eq_len_st t len


inline_for_extraction noextract
let bn_sub_eq_len_st (t:limb_t) (len:size_t) =
     a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (c_out, as_seq h1 res) == S.bn_sub (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_sub_eq_len: #t:limb_t -> len:size_t -> bn_sub_eq_len_st t len


inline_for_extraction noextract
let bn_add_st (t:limb_t) =
    aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum t bLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_add (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_add: #t:limb_t -> bn_add_st t


inline_for_extraction noextract
let bn_sub_st (t:limb_t) =
    aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum t bLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (c_out, as_seq h1 res) == S.bn_sub (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_sub: #t:limb_t -> bn_sub_st t


inline_for_extraction noextract
val bn_reduce_once:
    #t:limb_t
  -> aLen:size_t{v aLen > 0}
  -> n:lbignum t aLen
  -> c:carry t
  -> a:lbignum t aLen ->
  Stack unit
  (requires fun h -> live h a /\ live h n /\ disjoint a n)
  (ensures  fun h0 c_out h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_reduce_once (as_seq h0 n) c (as_seq h0 a))


inline_for_extraction noextract
let bn_add_mod_n_st (t:limb_t) (len:size_t{v len > 0}) =
    n:lbignum t len
  -> a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint n a /\ disjoint n b /\ disjoint n res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_add_mod_n (as_seq h0 n) (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_add_mod_n: #t:limb_t -> len:size_t{v len > 0} -> bn_add_mod_n_st t len


inline_for_extraction noextract
let bn_sub_mod_n_st (t:limb_t) (len:size_t{v len > 0}) =
    n:lbignum t len
  -> a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint n a /\ disjoint n b /\ disjoint n res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_sub_mod_n (as_seq h0 n) (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_sub_mod_n: #t:limb_t -> len:size_t{v len > 0} -> bn_sub_mod_n_st t len


inline_for_extraction noextract
val bn_mul1:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> l:limb t
  -> res:lbignum t aLen ->
  Stack (limb t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint res a)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul1 (as_seq h0 a) l)


inline_for_extraction noextract
let bn_karatsuba_mul_st (t:limb_t) (len:size_t{0 < v len /\ 4 * v len <= max_size_t}) (a:lbignum t len) =
    b:lbignum t len
  -> res:lbignum t (len +! len) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_karatsuba_mul:
    #t:limb_t
  -> len:size_t{0 < v len /\ 4 * v len <= max_size_t}
  -> a:lbignum t len ->
  bn_karatsuba_mul_st t len a


inline_for_extraction noextract
let bn_mul_st (t:limb_t) (aLen:size_t) (bLen:size_t{0 < v bLen /\ v aLen + v bLen <= max_size_t}) (a:lbignum t aLen) =
    b:lbignum t bLen
  -> res:lbignum t (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_mul:
    #t:limb_t
  -> aLen:size_t
  -> bLen:size_t{0 < v bLen /\ v aLen + v bLen <= max_size_t}
  -> a:lbignum t aLen ->
  bn_mul_st t aLen bLen a


inline_for_extraction noextract
let bn_karatsuba_sqr_st (t:limb_t) (len:size_t{0 < v len /\ 4 * v len <= max_size_t}) (a:lbignum t len) =
  res:lbignum t (len +! len) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 a))


inline_for_extraction noextract
val bn_karatsuba_sqr:
    #t:limb_t
  -> len:size_t{0 < v len /\ 4 * v len <= max_size_t}
  -> a:lbignum t len ->
  bn_karatsuba_sqr_st t len a


inline_for_extraction noextract
let bn_sqr_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) (a:lbignum t len) =
  res:lbignum t (len +! len) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 a))


inline_for_extraction noextract
val bn_sqr:
    #t:limb_t
  -> len:size_t{0 < v len /\ v len + v len <= max_size_t}
  -> a:lbignum t len ->
  bn_sqr_st t len a


inline_for_extraction noextract
val bn_mul1_lshift_add_in_place:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> b:limb t
  -> resLen:size_t
  -> j:size_t{v j + v aLen <= v resLen}
  -> res:lbignum t resLen ->
  Stack (limb t)
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul1_lshift_add (as_seq h0 a) b (v j) (as_seq h0 res))


inline_for_extraction noextract
val bn_rshift:
    #t:limb_t
  -> len:size_t
  -> b:lbignum t len
  -> i:size_t{v i < v len}
  -> res:lbignum t (len -! i) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_rshift (as_seq h0 b) (v i))


inline_for_extraction noextract
val bn_sub_mask:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> n:lbignum t len
  -> a:lbignum t len ->
  Stack unit
  (requires fun h -> live h n /\ live h a /\ disjoint n a)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_sub_mask (as_seq h0 n) (as_seq h0 a))

///
///  Get and set i-th bit of a bignum
///

inline_for_extraction noextract
val bn_get_ith_bit:
    #t:limb_t
  -> len:size_t
  -> b:lbignum t len
  -> i:size_t{v i / bits t < v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_get_ith_bit (as_seq h0 b) (v i))


inline_for_extraction noextract
val bn_get_bits:
    #t:limb_t
  -> len:size_t
  -> b:lbignum t len
  -> i:size_t
  -> l:size_t{v l < bits t /\ v i / bits t < v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_get_bits (as_seq h0 b) (v i) (v l))


inline_for_extraction noextract
val bn_set_ith_bit:
    #t:limb_t
  -> len:size_t
  -> b:lbignum t len
  -> i:size_t{v i / bits t < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_set_ith_bit (as_seq h0 b) (v i))


inline_for_extraction noextract
val cswap2:
    #t:limb_t
  -> len:size_t
  -> bit:limb t
  -> b1:lbignum t len
  -> b2:lbignum t len ->
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

inline_for_extraction noextract
let meta_len (t:limb_t) = len:size_t{0 < v len /\ 2 * bits t * v len <= max_size_t}

/// This type class is entirely meta-level and will not appear after partial
/// evaluation in the resulting C code. Clients can take this type class as a
/// parameter if they want the benefits of a function set specialized for a
/// given bignum length.
inline_for_extraction noextract
class bn (t:limb_t) = {
  len: meta_len t;
  add: bn_add_eq_len_st t len;
  sub: bn_sub_eq_len_st t len;
  add_mod_n: bn_add_mod_n_st t len;
  sub_mod_n: bn_sub_mod_n_st t len;
  mul: a:lbignum t len -> bn_karatsuba_mul_st t len a;
  sqr: a:lbignum t len -> bn_karatsuba_sqr_st t len a;
}


inline_for_extraction noextract
val mk_runtime_bn: t:limb_t -> len:meta_len t -> bn t

val mk_runtime_bn_len_lemma: t:limb_t -> len:meta_len t ->
  Lemma ((mk_runtime_bn t len).len == len) [SMTPat (mk_runtime_bn t len)]

///
///  Bignum comparison and test functions
///

inline_for_extraction noextract
val bn_is_odd:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> a:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_odd (as_seq h0 a))


inline_for_extraction noextract
let bn_eq_mask_st (t:limb_t) (len:size_t) =
    a:lbignum t len
  -> b:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_eq_mask (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_eq_mask: #t:limb_t -> len:size_t -> bn_eq_mask_st t len


inline_for_extraction noextract
val bn_is_zero_mask:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> a:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_zero_mask (as_seq h0 a))


inline_for_extraction noextract
let bn_lt_mask_st (t:limb_t) (len:size_t) =
    a:lbignum t len
  -> b:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_lt_mask (as_seq h0 a) (as_seq h0 b))


inline_for_extraction noextract
val bn_lt_mask: #t:limb_t -> len:size_t -> bn_lt_mask_st t len


inline_for_extraction noextract
val bn_lt_pow2_mask:
    #t:limb_t
  -> len:size_t{0 < v len /\ bits t * v len <= max_size_t}
  -> b:lbignum t len
  -> x:size_t{v x < bits t * v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_lt_pow2_mask (as_seq h0 b) (v x))


inline_for_extraction noextract
val bn_gt_pow2_mask:
    #t:limb_t
  -> len:size_t{0 < v len /\ bits t * v len <= max_size_t}
  -> b:lbignum t len
  -> x:size_t{v x < bits t * v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_gt_pow2_mask (as_seq h0 b) (v x))

///
///  Conversion functions for bignum
///

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


inline_for_extraction noextract
val bn_from_bytes_be:
    #t:limb_t
  -> len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum t (blocks len (size (numbytes t))) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_be (v len) (as_seq h0 b))


inline_for_extraction noextract
val bn_to_bytes_be:
    #t:limb_t
  -> len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}
  -> b:lbignum t (blocks len (size (numbytes t)))
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_be (v len) (as_seq h0 b))


inline_for_extraction noextract
val bn_from_bytes_le:
    #t:limb_t
  -> len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}
  -> b:lbuffer uint8 len
  -> res:lbignum t (blocks len (size (numbytes t))) ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_from_bytes_le (v len) (as_seq h0 b))


inline_for_extraction noextract
val bn_to_bytes_le:
    #t:limb_t
  -> len:size_t{0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t}
  -> b:lbignum t (blocks len (size (numbytes t)))
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_to_bytes_le (v len) (as_seq h0 b))
