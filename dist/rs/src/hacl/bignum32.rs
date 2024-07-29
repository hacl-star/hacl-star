#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub type pbn_mont_ctx_u32 <'a> = &'a [crate::hacl::bignum::bn_mont_ctx_u32];

/**
Write `a + b mod 2 ^ (32 * len)` in `res`.

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
    exactly equal memory location to `a` or `b`.
*/
pub fn
add(len: u32, a: &[u32], b: &[u32], res: &mut [u32]) ->
    u32
{ crate::hacl::bignum_base::bn_add_eq_len_u32(len, a, b, res) }

/**
Write `a - b mod 2 ^ (32 * len)` in `res`.

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
    exactly equal memory location to `a` or `b`.
*/
pub fn
sub(len: u32, a: &[u32], b: &[u32], res: &mut [u32]) ->
    u32
{ crate::hacl::bignum_base::bn_sub_eq_len_u32(len, a, b, res) }

/**
Write `(a + b) mod n` in `res`.

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
    - `b < n`
*/
pub fn
add_mod(len: u32, n: &[u32], a: &[u32], b: &[u32], res: &mut [u32])
{
    let mut a_copy: Vec<u32> = vec![0u32; len as usize];
    let mut b_copy: Vec<u32> = vec![0u32; len as usize];
    ((&mut a_copy)[0usize..len as usize]).copy_from_slice(&a[0usize..len as usize]);
    ((&mut b_copy)[0usize..len as usize]).copy_from_slice(&b[0usize..len as usize]);
    crate::hacl::bignum::bn_add_mod_n_u32(len, n, &a_copy, &b_copy, res)
}

/**
Write `(a - b) mod n` in `res`.

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
    - `b < n`
*/
pub fn
sub_mod(len: u32, n: &[u32], a: &[u32], b: &[u32], res: &mut [u32])
{ crate::hacl::bignum::bn_sub_mod_n_u32(len, n, a, b, res) }

/**
Write `a * b` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `b` and `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a` and `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory locations of `a` and `b`.
*/
pub fn
mul(len: u32, a: &[u32], b: &[u32], res: &mut [u32])
{
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_mul_uint32(len, a, b, &mut tmp, res)
}

/**
Write `a * a` in `res`.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory location of `a`.
*/
pub fn
sqr(len: u32, a: &[u32], res: &mut [u32])
{
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_sqr_uint32(len, a, &mut tmp, res)
}

#[inline] fn bn_slow_precomp(
    len: u32,
    n: &[u32],
    mu: u32,
    r2: &[u32],
    a: &[u32],
    res: &mut [u32]
)
{
    let mut a_mod: Vec<u32> = vec![0u32; len as usize];
    let mut a1: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    ((&mut a1)[0usize..len.wrapping_add(len) as usize]).copy_from_slice(
        &a[0usize..len.wrapping_add(len) as usize]
    );
    crate::hacl::bignum::bn_almost_mont_reduction_u32(len, n, mu, &mut a1, &mut a_mod);
    crate::hacl::bignum::bn_to_mont_u32(len, n, mu, r2, &a_mod, res)
}

/**
Write `a mod n` in `res`.

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
    - `n % 2 = 1`
*/
pub fn
r#mod(len: u32, n: &[u32], a: &[u32], res: &mut [u32]) ->
    bool
{
    let mut one: Vec<u32> = vec![0u32; len as usize];
    ((&mut one)[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = (&acc)[0usize];
    let is_valid_m: u32 = m0 & m1;
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    {
        let mut r2: Vec<u32> = vec![0u32; len as usize];
        crate::hacl::bignum::bn_precomp_r2_mod_n_u32(len, nBits, n, &mut r2);
        let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
        bn_slow_precomp(len, n, mu, &r2, a, res)
    }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Write `a ^ b mod n` in `res`.

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
    - `a < n`
*/
pub fn
mod_exp_vartime(len: u32, n: &[u32], a: &[u32], bBits: u32, b: &[u32], res: &mut [u32]) ->
    bool
{
    let is_valid_m: u32 = crate::hacl::bignum::bn_check_mod_exp_u32(len, n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    { crate::hacl::bignum::bn_mod_exp_vartime_u32(len, nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Write `a ^ b mod n` in `res`.

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
    - `a < n`
*/
pub fn
mod_exp_consttime(len: u32, n: &[u32], a: &[u32], bBits: u32, b: &[u32], res: &mut [u32]) ->
    bool
{
    let is_valid_m: u32 = crate::hacl::bignum::bn_check_mod_exp_u32(len, n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    { crate::hacl::bignum::bn_mod_exp_consttime_u32(len, nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Write `a ^ (-1) mod n` in `res`.

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
    - `a < n`
*/
pub fn
mod_inv_prime_vartime(len: u32, n: &[u32], a: &[u32], res: &mut [u32]) ->
    bool
{
    let mut one: Vec<u32> = vec![0u32; len as usize];
    ((&mut one)[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = (&acc)[0usize];
    let m00: u32 = m0 & m1;
    let bn_zero: Vec<u32> = vec![0u32; len as usize];
    let mut mask: [u32; 1] = [0xFFFFFFFFu32; 1usize];
    for i in 0u32..len
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], (&bn_zero)[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
    };
    let mask1: u32 = (&mask)[0usize];
    let res1: u32 = mask1;
    let m10: u32 = res1;
    let mut acc0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] = beq & (&acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m2: u32 = (&acc0)[0usize];
    let is_valid_m: u32 = m00 & ! m10 & m2;
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    {
        let mut n2: Vec<u32> = vec![0u32; len as usize];
        let c0: u32 =
            crate::lib::inttypes_intrinsics::sub_borrow_u32(
                0u32,
                n[0usize],
                2u32,
                &mut (&mut n2)[0usize..]
            );
        let c: u32 =
            if 1u32 < len
            {
                let a1: (&[u32], &[u32]) = n.split_at(1usize);
                let res10: (&mut [u32], &mut [u32]) = (&mut n2).split_at_mut(1usize);
                let mut c: [u32; 1] = [c0; 1usize];
                for i in 0u32..len.wrapping_sub(1u32).wrapping_div(4u32)
                {
                    let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
                    let res_i: (&mut [u32], &mut [u32]) =
                        res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u32(
                            (&c)[0usize],
                            t1,
                            0u32,
                            res_i.1
                        );
                    ();
                    let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                    let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u32(
                            (&c)[0usize],
                            t10,
                            0u32,
                            res_i0.1
                        );
                    ();
                    let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                    let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u32(
                            (&c)[0usize],
                            t11,
                            0u32,
                            res_i1.1
                        );
                    ();
                    let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                    let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u32(
                            (&c)[0usize],
                            t12,
                            0u32,
                            res_i2.1
                        );
                    ();
                    ();
                    ()
                };
                ();
                for
                i
                in
                len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_mul(4u32)..len.wrapping_sub(1u32)
                {
                    let t1: u32 = a1.1[i as usize];
                    let res_i: (&mut [u32], &mut [u32]) = res10.1.split_at_mut(i as usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u32(
                            (&c)[0usize],
                            t1,
                            0u32,
                            res_i.1
                        );
                    ();
                    ()
                };
                let c1: u32 = (&c)[0usize];
                c1
            }
            else
            { c0 };
        crate::lowstar::ignore::ignore::<u32>(c);
        crate::hacl::bignum::bn_mod_exp_vartime_u32(
            len,
            nBits,
            n,
            a,
            32u32.wrapping_mul(len),
            &n2,
            res
        )
    }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Heap-allocate and initialize a montgomery context.

  @param n Points to `len` number of limbs, i.e. `uint32_t[len]`.

  @return A pointer to an allocated and initialized Montgomery context is returned.
    Clients will need to call `Hacl_Bignum32_mont_ctx_free` on the return value to
    avoid memory leaks.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`
*/
pub fn
mont_ctx_init(len: u32, n: &[u32]) ->
    Vec<crate::hacl::bignum::bn_mont_ctx_u32>
{
    let mut r2: Vec<u32> = vec![0u32; len as usize];
    let mut n1: Vec<u32> = vec![0u32; len as usize];
    let r21: &mut [u32] = &mut r2;
    let n11: &mut [u32] = &mut n1;
    (n11[0usize..len as usize]).copy_from_slice(&n[0usize..len as usize]);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    crate::hacl::bignum::bn_precomp_r2_mod_n_u32(len, nBits, n, r21);
    let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
    let res: crate::hacl::bignum::bn_mont_ctx_u32 =
        crate::hacl::bignum::bn_mont_ctx_u32 { len: len, n: n11.to_vec(), mu: mu, r2: r21.to_vec() };
    let buf: Vec<crate::hacl::bignum::bn_mont_ctx_u32> =
        {
            let mut tmp: Vec<crate::hacl::bignum::bn_mont_ctx_u32> = Vec::new();
            tmp.push(res);
            tmp
        };
    buf
}

/**
Write `a mod n` in `res`.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `2*len` number of limbs, i.e. `uint32_t[2*len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a`.
*/
pub fn
mod_precomp(k: &[crate::hacl::bignum::bn_mont_ctx_u32], a: &[u32], res: &mut [u32])
{
    let len1: u32 = (k[0usize]).len;
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    bn_slow_precomp(len1, n, mu, r2, a, res)
}

/**
Write `a ^ b mod n` in `res`.

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
    - `a < n`
*/
pub fn
mod_exp_vartime_precomp(
    k: &[crate::hacl::bignum::bn_mont_ctx_u32],
    a: &[u32],
    bBits: u32,
    b: &[u32],
    res: &mut [u32]
)
{
    let len1: u32 = (k[0usize]).len;
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    crate::hacl::bignum::bn_mod_exp_vartime_precomp_u32(len1, n, mu, r2, a, bBits, b, res)
}

/**
Write `a ^ b mod n` in `res`.

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
    - `a < n`
*/
pub fn
mod_exp_consttime_precomp(
    k: &[crate::hacl::bignum::bn_mont_ctx_u32],
    a: &[u32],
    bBits: u32,
    b: &[u32],
    res: &mut [u32]
)
{
    let len1: u32 = (k[0usize]).len;
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    crate::hacl::bignum::bn_mod_exp_consttime_precomp_u32(len1, n, mu, r2, a, bBits, b, res)
}

/**
Write `a ^ (-1) mod n` in `res`.

  @param[in] k Points to a Montgomery context obtained through `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n` is a prime
    - `0 < a`
    - `a < n`
*/
pub fn
mod_inv_prime_vartime_precomp(
    k: &[crate::hacl::bignum::bn_mont_ctx_u32],
    a: &[u32],
    res: &mut [u32]
)
{
    let len1: u32 = (k[0usize]).len;
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    let mut n2: Vec<u32> = vec![0u32; len1 as usize];
    let c0: u32 =
        crate::lib::inttypes_intrinsics::sub_borrow_u32(
            0u32,
            n[0usize],
            2u32,
            &mut (&mut n2)[0usize..]
        );
    let c: u32 =
        if 1u32 < len1
        {
            let a1: (&[u32], &[u32]) = n.split_at(1usize);
            let res1: (&mut [u32], &mut [u32]) = (&mut n2).split_at_mut(1usize);
            let mut c: [u32; 1] = [c0; 1usize];
            for i in 0u32..len1.wrapping_sub(1u32).wrapping_div(4u32)
            {
                let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
                let res_i: (&mut [u32], &mut [u32]) =
                    res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1);
                ();
                let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&c)[0usize],
                        t10,
                        0u32,
                        res_i0.1
                    );
                ();
                let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&c)[0usize],
                        t11,
                        0u32,
                        res_i1.1
                    );
                ();
                let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&c)[0usize],
                        t12,
                        0u32,
                        res_i2.1
                    );
                ();
                ();
                ()
            };
            ();
            for
            i
            in
            len1.wrapping_sub(1u32).wrapping_div(4u32).wrapping_mul(4u32)..len1.wrapping_sub(1u32)
            {
                let t1: u32 = a1.1[i as usize];
                let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(i as usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1);
                ();
                ()
            };
            let c1: u32 = (&c)[0usize];
            c1
        }
        else
        { c0 };
    crate::lowstar::ignore::ignore::<u32>(c);
    crate::hacl::bignum::bn_mod_exp_vartime_precomp_u32(
        len1,
        n,
        mu,
        r2,
        a,
        32u32.wrapping_mul(len1),
        &n2,
        res
    )
}

/**
Load a bid-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks.
*/
pub fn
new_bn_from_bytes_be(len: u32, b: &[u8]) ->
    Vec<u32>
{
    if
    len == 0u32
    ||
    ! (len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) <= 1073741823u32)
    { (&[]).to_vec() }
    else
    {
        let mut res: Vec<u32> =
            vec![0u32; len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) as usize];
        if false
        { res }
        else
        {
            let res1: &mut [u32] = &mut res;
            let res2: &mut [u32] = res1;
            let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
            let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
            let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
            ((&mut tmp)[tmpLen.wrapping_sub(len) as usize..tmpLen.wrapping_sub(len) as usize
            +
            len as usize]).copy_from_slice(&b[0usize..len as usize]);
            for i in 0u32..bnLen
            {
                let u: u32 =
                    crate::lowstar::endianness::load32_be(
                        &(&tmp)[bnLen.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(4u32) as usize..]
                    );
                let x: u32 = u;
                let os: (&mut [u32], &mut [u32]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            };
            res2.to_vec()
        }
    }
}

/**
Load a little-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks.
*/
pub fn
new_bn_from_bytes_le(len: u32, b: &[u8]) ->
    Vec<u32>
{
    if
    len == 0u32
    ||
    ! (len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) <= 1073741823u32)
    { (&[]).to_vec() }
    else
    {
        let mut res: Vec<u32> =
            vec![0u32; len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) as usize];
        if false
        { res }
        else
        {
            let res1: &mut [u32] = &mut res;
            let res2: &mut [u32] = res1;
            let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
            let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
            let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
            ((&mut tmp)[0usize..len as usize]).copy_from_slice(&b[0usize..len as usize]);
            for i in 0u32..len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32)
            {
                let bj: (&[u8], &[u8]) = (&tmp).split_at(i.wrapping_mul(4u32) as usize);
                let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
                let r1: u32 = u;
                let x: u32 = r1;
                let os: (&mut [u32], &mut [u32]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            };
            res2.to_vec()
        }
    }
}

/**
Serialize a bignum into big-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`.
*/
pub fn
bn_to_bytes_be(len: u32, b: &[u32], res: &mut [u8])
{
    let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
    let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
    let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
    for i in 0u32..bnLen
    {
        crate::lowstar::endianness::store32_be(
            &mut (&mut tmp)[i.wrapping_mul(4u32) as usize..],
            b[bnLen.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    };
    (res[0usize..len as usize]).copy_from_slice(
        &(&(&tmp)[tmpLen.wrapping_sub(len) as usize..])[0usize..len as usize]
    )
}

/**
Serialize a bignum into little-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`.
*/
pub fn
bn_to_bytes_le(len: u32, b: &[u32], res: &mut [u8])
{
    let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
    let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
    let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
    for i in 0u32..bnLen
    {
        crate::lowstar::endianness::store32_le(
            &mut (&mut tmp)[i.wrapping_mul(4u32) as usize..],
            b[i as usize]
        )
    };
    (res[0usize..len as usize]).copy_from_slice(&(&(&tmp)[0usize..])[0usize..len as usize])
}

/**
Returns 2^32 - 1 if a < b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if `a < b`, otherwise, `0`.
*/
pub fn
lt_mask(len: u32, a: &[u32], b: &[u32]) ->
    u32
{
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], b[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    (&acc)[0usize]
}

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if a = b, otherwise, `0`.
*/
pub fn
eq_mask(len: u32, a: &[u32], b: &[u32]) ->
    u32
{
    let mut mask: [u32; 1] = [0xFFFFFFFFu32; 1usize];
    for i in 0u32..len
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
    };
    let mask1: u32 = (&mask)[0usize];
    mask1
}
