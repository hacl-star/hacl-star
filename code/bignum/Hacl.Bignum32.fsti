module Hacl.Bignum32

open FStar.Mul

module BN = Hacl.Bignum
module BS = Hacl.Bignum.SafeAPI
module MA = Hacl.Bignum.MontArithmetic

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U32

inline_for_extraction noextract
let lbignum = Hacl.Bignum.Definitions.lbignum

let pbn_mont_ctx_u32 = MA.pbn_mont_ctx_u32

[@@ CPrologue
"/*******************************************************************************

A verified bignum library.

This is a 32-bit optimized version, where bignums are represented as an array
of `len` unsigned 32-bit integers, i.e. uint32_t[len].

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/\n";
Comment
"Write `a + b mod 2 ^ (32 * len)` in `res`.

  This function returns the carry.
  
  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly equal memory
    location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[out] res Points to `len` number of limbs where the carry is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`."]
val add: len:BN.meta_len t_limbs -> BN.bn_add_eq_len_st t_limbs len

[@@ Comment "Write `a - b mod 2 ^ (32 * len)` in `res`.

  This functions returns the carry.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly
    equal memory location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[out] res Points to `len` number of limbs where the carry is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`."]
val sub: len:BN.meta_len t_limbs -> BN.bn_sub_eq_len_st t_limbs len

[@@ Comment "Write `(a + b) mod n` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly
    equal memory location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `res`.
  @param[out] res Points to `len` number of limbs where the result is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `a < n`
    - `b < n`"]
val add_mod: len:BN.meta_len t_limbs -> BN.bn_add_mod_n_st t_limbs len

[@@ Comment "Write `(a - b) mod n` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly
    equal memory location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `res`.
  @param[out] res Points to `len` number of limbs where the result is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `a < n`
    - `b < n`"]
val sub_mod: len:BN.meta_len t_limbs -> BN.bn_sub_mod_n_st t_limbs len

[@@ Comment "Write `a * b` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `b` and `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a` and `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory locations of `a` and `b`."]
val mul: len:BN.meta_len t_limbs -> a:lbignum t_limbs len -> BN.bn_karatsuba_mul_st t_limbs len a

[@@ Comment "Write `a * a` in `res`.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory location of `a`."]
val sqr: len:BN.meta_len t_limbs -> a:lbignum t_limbs len -> BN.bn_karatsuba_sqr_st t_limbs len a

[@@ Comment "Write `a mod n` in `res`.

  @param[in] a Points to `2*len` number of limbs, i.e. `uint32_t[2*len]`. Must be
    disjoint from the memory location of `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `n`.
  
  @return `false` if any precondition is violated, `true` otherwise.
  
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `1 < n`
    - `n % 2 = 1`"]
val mod: len:BN.meta_len t_limbs -> BS.bn_mod_slow_safe_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  This function is *NOT* constant-time on the argument `b`. See the
  `mod_exp_consttime_*` functions for constant-time variants.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `n` and `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `n`.
    
  @return `false` if any preconditions are violated, `true` otherwise.
  
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`
    - `b < pow2 bBits`
    - `a < n`"]
val mod_exp_vartime: len:BN.meta_len t_limbs -> BS.bn_mod_exp_safe_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  This function is constant-time over its argument `b`, at the cost of a slower
  execution time than `mod_exp_vartime_*`.
  
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `n` and `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `n`.
    
  @return `false` if any preconditions are violated, `true` otherwise.

  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`
    - `b < pow2 bBits`
    - `a < n`"]
val mod_exp_consttime: len:BN.meta_len t_limbs -> BS.bn_mod_exp_safe_st t_limbs len

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `n` and `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a` and `n`.
    
  @return `false` if any preconditions (except the precondition: `n` is a prime)
    are violated, `true` otherwise.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n` is a prime
    - `n % 2 = 1`
    - `1 < n`
    - `0 < a`
    - `a < n`"]
val mod_inv_prime_vartime: len:BN.meta_len t_limbs -> BS.bn_mod_inv_prime_safe_st t_limbs len

[@@ CPrologue
"\n/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/\n";

Comment "Heap-allocate and initialize a montgomery context.

  @param n Points to `len` number of limbs, i.e. `uint32_t[len]`.

  @return A pointer to an allocated and initialized Montgomery context is returned.
    Clients will need to call `Hacl_Bignum32_mont_ctx_free` on the return value to
    avoid memory leaks.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`"]
val mont_ctx_init: len:BN.meta_len t_limbs -> MA.bn_field_init_st t_limbs len

[@@ Comment "Deallocate the memory previously allocated by Hacl_Bignum32_mont_ctx_init.

  @param k Points to a Montgomery context obtained through `Hacl_Bignum32_mont_ctx_init`."]
val mont_ctx_free: MA.bn_field_free_st t_limbs

[@@ Comment "Write `a mod n` in `res`.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `2*len` number of limbs, i.e. `uint32_t[2*len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a`."]
val mod_precomp: len:Ghost.erased _ -> BS.bn_mod_slow_ctx_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  This function is *NOT* constant-time on the argument `b`. See the
  `mod_exp_consttime_*` functions for constant-time variants.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `b < pow2 bBits`
    - `a < n`"]
val mod_exp_vartime_precomp: len:Ghost.erased _ -> BS.bn_mod_exp_ctx_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than `mod_exp_vartime_*`.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `b < pow2 bBits`
    - `a < n`"]
val mod_exp_consttime_precomp: len:Ghost.erased _ -> BS.bn_mod_exp_ctx_st t_limbs len

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  @param[in] k Points to a Montgomery context obtained through `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n` is a prime
    - `0 < a`
    - `a < n`"]
val mod_inv_prime_vartime_precomp: len:Ghost.erased _ -> BS.bn_mod_inv_prime_ctx_st t_limbs len

[@@ CPrologue
"\n/********************/
/* Loads and stores */
/********************/\n";
Comment
"Load a bid-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks."]
val new_bn_from_bytes_be: BS.new_bn_from_bytes_be_st t_limbs

[@@ Comment "Load a little-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks."]
val new_bn_from_bytes_le: BS.new_bn_from_bytes_le_st t_limbs

[@@ Comment "Serialize a bignum into big-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`."]
val bn_to_bytes_be: len:_ -> Hacl.Bignum.Convert.bn_to_bytes_be_st t_limbs len

[@@ Comment "Serialize a bignum into little-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`."]
val bn_to_bytes_le: len:_ -> Hacl.Bignum.Convert.bn_to_bytes_le_st t_limbs len

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment "Returns 2^32 - 1 if a < b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if `a < b`, otherwise, `0`."]
val lt_mask: len:_ -> BN.bn_lt_mask_st t_limbs len

[@@ Comment "Returns 2^32 - 1 if a = b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if a = b, otherwise, `0`."]
val eq_mask: len:_ -> BN.bn_eq_mask_st t_limbs len
