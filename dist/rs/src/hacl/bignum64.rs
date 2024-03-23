#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub type pbn_mont_ctx_u64 <'a> = &'a mut [crate::hacl::bignum::bn_mont_ctx_u64];

pub fn add(len: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{ crate::hacl::bignum_base::bn_add_eq_len_u64(len, a, b, res) }

pub fn sub(len: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{ crate::hacl::bignum_base::bn_sub_eq_len_u64(len, a, b, res) }

pub fn add_mod(len: u32, n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut a_copy: Vec<u64> = vec![0u64; len as usize];
    let mut b_copy: Vec<u64> = vec![0u64; len as usize];
    ((&mut a_copy)[0usize..len as usize]).copy_from_slice(&a[0usize..len as usize]);
    ((&mut b_copy)[0usize..len as usize]).copy_from_slice(&b[0usize..len as usize]);
    crate::hacl::bignum::bn_add_mod_n_u64(len, n, &mut a_copy, &mut b_copy, res)
}

pub fn sub_mod(len: u32, n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{ crate::hacl::bignum::bn_sub_mod_n_u64(len, n, a, b, res) }

pub fn mul(len: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_mul_uint64(len, a, b, &mut tmp, res)
}

pub fn sqr(len: u32, a: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_sqr_uint64(len, a, &mut tmp, res)
}

#[inline] fn bn_slow_precomp(
    len: u32,
    n: &mut [u64],
    mu: u64,
    r2: &mut [u64],
    a: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut a_mod: Vec<u64> = vec![0u64; len as usize];
    let mut a1: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    ((&mut a1)[0usize..len.wrapping_add(len) as usize]).copy_from_slice(
        &a[0usize..len.wrapping_add(len) as usize]
    );
    crate::hacl::bignum::bn_almost_mont_reduction_u64(len, n, mu, &mut a1, &mut a_mod);
    crate::hacl::bignum::bn_to_mont_u64(len, n, mu, r2, &mut a_mod, res)
}

pub fn r#mod(len: u32, n: &mut [u64], a: &mut [u64], res: &mut [u64]) -> bool
{
    let mut one: Vec<u64> = vec![0u64; len as usize];
    ((&mut one)[0usize..len as usize]).copy_from_slice(&vec![0u64; len as usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = (&mut acc)[0usize];
    let is_valid_m: u64 = m0 & m1;
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(len, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    {
        let mut r2: Vec<u64> = vec![0u64; len as usize];
        crate::hacl::bignum::bn_precomp_r2_mod_n_u64(len, nBits, n, &mut r2);
        let mu: u64 = crate::hacl::bignum::mod_inv_uint64(n[0usize]);
        bn_slow_precomp(len, n, mu, &mut r2, a, res)
    }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u64; len as usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mod_exp_vartime(
    len: u32,
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    bool
{
    let is_valid_m: u64 = crate::hacl::bignum::bn_check_mod_exp_u64(len, n, a, bBits, b);
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(len, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    { crate::hacl::bignum::bn_mod_exp_vartime_u64(len, nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u64; len as usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mod_exp_consttime(
    len: u32,
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    bool
{
    let is_valid_m: u64 = crate::hacl::bignum::bn_check_mod_exp_u64(len, n, a, bBits, b);
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(len, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    { crate::hacl::bignum::bn_mod_exp_consttime_u64(len, nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u64; len as usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mod_inv_prime_vartime(len: u32, n: &mut [u64], a: &mut [u64], res: &mut [u64]) -> bool
{
    let mut one: Vec<u64> = vec![0u64; len as usize];
    ((&mut one)[0usize..len as usize]).copy_from_slice(&vec![0u64; len as usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = (&mut acc)[0usize];
    let m00: u64 = m0 & m1;
    let mut bn_zero: Vec<u64> = vec![0u64; len as usize];
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    for i in 0u32..len
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], (&mut bn_zero)[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
    };
    let mask1: u64 = (&mut mask)[0usize];
    let res1: u64 = mask1;
    let m10: u64 = res1;
    let mut acc0: [u64; 1] = [0u64; 1usize];
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] =
            beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m2: u64 = (&mut acc0)[0usize];
    let is_valid_m: u64 = m00 & ! m10 & m2;
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(len, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    {
        let mut n2: Vec<u64> = vec![0u64; len as usize];
        let c0: u64 =
            crate::lib::inttypes_intrinsics::sub_borrow_u64(
                0u64,
                n[0usize],
                2u64,
                &mut (&mut n2)[0usize..]
            );
        let c: u64 =
            if 1u32 < len
            {
                let a1: (&mut [u64], &mut [u64]) = n.split_at_mut(1usize);
                let res10: (&mut [u64], &mut [u64]) = (&mut n2).split_at_mut(1usize);
                let mut c: [u64; 1] = [c0; 1usize];
                for i in 0u32..len.wrapping_sub(1u32).wrapping_div(4u32)
                {
                    let t1: u64 = a1.1[4u32.wrapping_mul(i) as usize];
                    let res_i: (&mut [u64], &mut [u64]) =
                        res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u64(
                            (&mut c)[0usize],
                            t1,
                            0u64,
                            res_i.1
                        );
                    ();
                    let t10: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                    let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u64(
                            (&mut c)[0usize],
                            t10,
                            0u64,
                            res_i0.1
                        );
                    ();
                    let t11: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                    let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u64(
                            (&mut c)[0usize],
                            t11,
                            0u64,
                            res_i1.1
                        );
                    ();
                    let t12: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                    let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u64(
                            (&mut c)[0usize],
                            t12,
                            0u64,
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
                    let t1: u64 = a1.1[i as usize];
                    let res_i: (&mut [u64], &mut [u64]) = res10.1.split_at_mut(i as usize);
                    (&mut c)[0usize] =
                        crate::lib::inttypes_intrinsics::sub_borrow_u64(
                            (&mut c)[0usize],
                            t1,
                            0u64,
                            res_i.1
                        );
                    ();
                    ()
                };
                let c1: u64 = (&mut c)[0usize];
                c1
            }
            else
            { c0 };
        crate::lowstar::ignore::ignore::<u64>(c);
        crate::hacl::bignum::bn_mod_exp_vartime_u64(
            len,
            nBits,
            n,
            a,
            64u32.wrapping_mul(len),
            &mut n2,
            res
        )
    }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u64; len as usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mont_ctx_init(len: u32, n: &mut [u64]) -> Vec<crate::hacl::bignum::bn_mont_ctx_u64>
{
    let mut r2: Vec<u64> = vec![0u64; len as usize];
    let mut n1: Vec<u64> = vec![0u64; len as usize];
    let r21: &mut [u64] = &mut r2;
    let n11: &mut [u64] = &mut n1;
    (n11[0usize..len as usize]).copy_from_slice(&n[0usize..len as usize]);
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(len, n) as u32);
    crate::hacl::bignum::bn_precomp_r2_mod_n_u64(len, nBits, n, r21);
    let mu: u64 = crate::hacl::bignum::mod_inv_uint64(n[0usize]);
    let mut res: crate::hacl::bignum::bn_mont_ctx_u64 =
        crate::hacl::bignum::bn_mont_ctx_u64 { len: len, n: n11.to_vec(), mu: mu, r2: r21.to_vec() };
    let mut buf: Vec<crate::hacl::bignum::bn_mont_ctx_u64> =
        {
            let mut tmp: Vec<crate::hacl::bignum::bn_mont_ctx_u64> = Vec::new();
            tmp.push(res);
            tmp
        };
    buf
}

pub fn mod_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u64],
    a: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let len1: u32 = (k[0usize]).len;
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    bn_slow_precomp(len1, n, mu, r2, a, res)
}

pub fn mod_exp_vartime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let len1: u32 = (k[0usize]).len;
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    crate::hacl::bignum::bn_mod_exp_vartime_precomp_u64(len1, n, mu, r2, a, bBits, b, res)
}

pub fn mod_exp_consttime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let len1: u32 = (k[0usize]).len;
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    crate::hacl::bignum::bn_mod_exp_consttime_precomp_u64(len1, n, mu, r2, a, bBits, b, res)
}

pub fn mod_inv_prime_vartime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u64],
    a: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let len1: u32 = (k[0usize]).len;
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    let mut n2: Vec<u64> = vec![0u64; len1 as usize];
    let c0: u64 =
        crate::lib::inttypes_intrinsics::sub_borrow_u64(
            0u64,
            n[0usize],
            2u64,
            &mut (&mut n2)[0usize..]
        );
    let c: u64 =
        if 1u32 < len1
        {
            let a1: (&mut [u64], &mut [u64]) = n.split_at_mut(1usize);
            let res1: (&mut [u64], &mut [u64]) = (&mut n2).split_at_mut(1usize);
            let mut c: [u64; 1] = [c0; 1usize];
            for i in 0u32..len1.wrapping_sub(1u32).wrapping_div(4u32)
            {
                let t1: u64 = a1.1[4u32.wrapping_mul(i) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u64(
                        (&mut c)[0usize],
                        t1,
                        0u64,
                        res_i.1
                    );
                ();
                let t10: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u64(
                        (&mut c)[0usize],
                        t10,
                        0u64,
                        res_i0.1
                    );
                ();
                let t11: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u64(
                        (&mut c)[0usize],
                        t11,
                        0u64,
                        res_i1.1
                    );
                ();
                let t12: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u64(
                        (&mut c)[0usize],
                        t12,
                        0u64,
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
                let t1: u64 = a1.1[i as usize];
                let res_i: (&mut [u64], &mut [u64]) = res1.1.split_at_mut(i as usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u64(
                        (&mut c)[0usize],
                        t1,
                        0u64,
                        res_i.1
                    );
                ();
                ()
            };
            let c1: u64 = (&mut c)[0usize];
            c1
        }
        else
        { c0 };
    crate::lowstar::ignore::ignore::<u64>(c);
    crate::hacl::bignum::bn_mod_exp_vartime_precomp_u64(
        len1,
        n,
        mu,
        r2,
        a,
        64u32.wrapping_mul(len1),
        &mut n2,
        res
    )
}

pub fn new_bn_from_bytes_be(len: u32, b: &mut [u8]) -> Vec<u64>
{
    if
    len == 0u32 || ! (len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32) <= 536870911u32)
    { (&mut []).to_vec() }
    else
    {
        let mut res: Vec<u64> =
            vec![0u64; len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32) as usize];
        if false
        { res }
        else
        {
            let res1: &mut [u64] = &mut res;
            let res2: &mut [u64] = res1;
            let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
            let tmpLen: u32 = 8u32.wrapping_mul(bnLen);
            let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
            ((&mut tmp)[tmpLen.wrapping_sub(len) as usize..tmpLen.wrapping_sub(len) as usize
            +
            len as usize]).copy_from_slice(&b[0usize..len as usize]);
            for i in 0u32..bnLen
            {
                let u: u64 =
                    crate::lowstar::endianness::load64_be(
                        &mut
                        (&mut tmp)[bnLen.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32)
                        as
                        usize..]
                    );
                let x: u64 = u;
                let os: (&mut [u64], &mut [u64]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            };
            res2.to_vec()
        }
    }
}

pub fn new_bn_from_bytes_le(len: u32, b: &mut [u8]) -> Vec<u64>
{
    if
    len == 0u32 || ! (len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32) <= 536870911u32)
    { (&mut []).to_vec() }
    else
    {
        let mut res: Vec<u64> =
            vec![0u64; len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32) as usize];
        if false
        { res }
        else
        {
            let res1: &mut [u64] = &mut res;
            let res2: &mut [u64] = res1;
            let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
            let tmpLen: u32 = 8u32.wrapping_mul(bnLen);
            let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
            ((&mut tmp)[0usize..len as usize]).copy_from_slice(&b[0usize..len as usize]);
            for i in 0u32..len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32)
            {
                let bj: (&mut [u8], &mut [u8]) =
                    (&mut tmp).split_at_mut(i.wrapping_mul(8u32) as usize);
                let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
                let r1: u64 = u;
                let x: u64 = r1;
                let os: (&mut [u64], &mut [u64]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            };
            res2.to_vec()
        }
    }
}

pub fn bn_to_bytes_be(len: u32, b: &mut [u64], res: &mut [u8]) -> ()
{
    let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let tmpLen: u32 = 8u32.wrapping_mul(bnLen);
    let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
    for i in 0u32..bnLen
    {
        crate::lowstar::endianness::store64_be(
            &mut (&mut tmp)[i.wrapping_mul(8u32) as usize..],
            b[bnLen.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    };
    (res[0usize..len as usize]).copy_from_slice(
        &(&mut (&mut tmp)[tmpLen.wrapping_sub(len) as usize..])[0usize..len as usize]
    )
}

pub fn bn_to_bytes_le(len: u32, b: &mut [u64], res: &mut [u8]) -> ()
{
    let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let tmpLen: u32 = 8u32.wrapping_mul(bnLen);
    let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
    for i in 0u32..bnLen
    {
        crate::lowstar::endianness::store64_le(
            &mut (&mut tmp)[i.wrapping_mul(8u32) as usize..],
            b[i as usize]
        )
    };
    (res[0usize..len as usize]).copy_from_slice(&(&mut (&mut tmp)[0usize..])[0usize..len as usize])
}

pub fn lt_mask(len: u32, a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], b[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    (&mut acc)[0usize]
}

pub fn eq_mask(len: u32, a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    for i in 0u32..len
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
    };
    let mask1: u64 = (&mut mask)[0usize];
    mask1
}
