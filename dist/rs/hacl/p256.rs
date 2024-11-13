#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn bn_is_zero_mask4(f: &mut [u64]) -> u64
{
    let mut bn_zero: [u64; 4] = [0u64; 4usize];
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = fstar::uint64::eq_mask(f[i as usize], (&mut bn_zero)[i as usize]);
            (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
        }
    );
    let mask1: u64 = (&mut mask)[0usize];
    let res: u64 = mask1;
    res
}

#[inline] fn bn_is_zero_vartime4(f: &mut [u64]) -> bool
{
    let m: u64 = crate::p256::bn_is_zero_mask4(f);
    m == 0xFFFFFFFFFFFFFFFFu64
}

#[inline] fn bn_is_eq_mask4(a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
            (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
        }
    );
    let mask1: u64 = (&mut mask)[0usize];
    mask1
}

#[inline] fn bn_is_eq_vartime4(a: &mut [u64], b: &mut [u64]) -> bool
{
    let m: u64 = crate::p256::bn_is_eq_mask4(a, b);
    m == 0xFFFFFFFFFFFFFFFFu64
}

#[inline] fn bn_cmovznz4(res: &mut [u64], cin: u64, x: &mut [u64], y: &mut [u64])
{
    let mask: u64 = ! fstar::uint64::eq_mask(cin, 0u64);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = x[i as usize];
            let x1: u64 = uu____0 ^ mask & (y[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x1
        }
    )
}

#[inline] fn bn_add_mod4(res: &mut [u64], n: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = x[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = y[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    let c0: u64 = (&mut c)[0usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = res[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = n[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = tmp.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    let c10: u64 = (&mut c1)[0usize];
    let c2: u64 = c0.wrapping_sub(c10);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x1: u64 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x1
        }
    )
}

#[inline] fn bn_sub4(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> u64
{
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = x[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = y[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    let c0: u64 = (&mut c)[0usize];
    c0
}

#[inline] fn bn_sub_mod4(res: &mut [u64], n: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = x[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = y[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = y[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    let c0: u64 = (&mut c)[0usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = res[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = n[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = tmp.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    let c10: u64 = (&mut c1)[0usize];
    lowstar::ignore::ignore::<u64>(c10);
    let c2: u64 = 0u64.wrapping_sub(c0);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x1: u64 = c2 & (&mut tmp)[i as usize] | ! c2 & res[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x1
        }
    )
}

#[inline] fn bn_mul4(res: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    (res[0usize..8usize]).copy_from_slice(&[0u64; 8usize]);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let bj: u64 = y[i as usize];
            let res_j: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            {
                let a_i: u64 = x[4u32.wrapping_mul(0u32) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    res_j.1.split_at_mut(4u32.wrapping_mul(0u32) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, bj, (&mut c)[0usize], res_i.1);
                let a_i0: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, bj, (&mut c)[0usize], res_i0.1);
                let a_i1: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, bj, (&mut c)[0usize], res_i1.1);
                let a_i2: u64 = x[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, bj, (&mut c)[0usize], res_i2.1)
            };
            let r: u64 = (&mut c)[0usize];
            res[4u32.wrapping_add(i) as usize] = r
        }
    )
}

#[inline] fn bn_sqr4(res: &mut [u64], x: &mut [u64])
{
    (res[0usize..8usize]).copy_from_slice(&[0u64; 8usize]);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let a_j: u64 = x[i as usize];
            let ab: (&mut [u64], &mut [u64]) = x.split_at_mut(0usize);
            let res_j: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            for i0 in 0u32..i.wrapping_div(4u32)
            {
                let a_i: u64 = ab.1[4u32.wrapping_mul(i0) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, a_j, (&mut c)[0usize], res_i.1);
                let a_i0: u64 = ab.1[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, a_j, (&mut c)[0usize], res_i0.1);
                let a_i1: u64 = ab.1[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, a_j, (&mut c)[0usize], res_i1.1);
                let a_i2: u64 = ab.1[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, a_j, (&mut c)[0usize], res_i2.1)
            };
            for i0 in i.wrapping_div(4u32).wrapping_mul(4u32)..i
            {
                let a_i: u64 = ab.1[i0 as usize];
                let res_i: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(i0 as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, a_j, (&mut c)[0usize], res_i.1)
            };
            let r: u64 = (&mut c)[0usize];
            res[i.wrapping_add(i) as usize] = r
        }
    );
    let mut a_copy: [u64; 8] = [0u64; 8usize];
    let mut b_copy: [u64; 8] = [0u64; 8usize];
    ((&mut a_copy)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
    ((&mut b_copy)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
    let r: u64 = bignum::bignum_base::bn_add_eq_len_u64(8u32, &mut a_copy, &mut b_copy, res);
    let c0: u64 = r;
    lowstar::ignore::ignore::<u64>(c0);
    let mut tmp: [u64; 8] = [0u64; 8usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let res1: fstar::uint128::uint128 =
                fstar::uint128::mul_wide(x[i as usize], x[i as usize]);
            let hi: u64 =
                fstar::uint128::uint128_to_uint64(fstar::uint128::shift_right(res1, 64u32));
            let lo: u64 = fstar::uint128::uint128_to_uint64(res1);
            (&mut tmp)[2u32.wrapping_mul(i) as usize] = lo;
            (&mut tmp)[2u32.wrapping_mul(i).wrapping_add(1u32) as usize] = hi
        }
    );
    let mut a_copy0: [u64; 8] = [0u64; 8usize];
    let mut b_copy0: [u64; 8] = [0u64; 8usize];
    ((&mut a_copy0)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
    ((&mut b_copy0)[0usize..8usize]).copy_from_slice(&(&mut tmp)[0usize..8usize]);
    let r0: u64 = bignum::bignum_base::bn_add_eq_len_u64(8u32, &mut a_copy0, &mut b_copy0, res);
    let c1: u64 = r0;
    lowstar::ignore::ignore::<u64>(c1)
}

#[inline] fn bn_to_bytes_be4(res: &mut [u8], f: &mut [u64])
{
    let mut tmp: [u8; 32] = [0u8; 32usize];
    lowstar::ignore::ignore::<&mut [u8]>(&mut tmp);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_be(
            &mut res[i.wrapping_mul(8u32) as usize..],
            f[4u32.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    )
}

#[inline] fn bn_from_bytes_be4(res: &mut [u64], b: &mut [u8])
{
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let u: u64 =
                lowstar::endianness::load64_be(
                    &mut b[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
                );
            let x: u64 = u;
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn bn2_to_bytes_be4(res: &mut [u8], x: &mut [u64], y: &mut [u64])
{
    crate::p256::bn_to_bytes_be4(&mut res[0usize..], x);
    crate::p256::bn_to_bytes_be4(&mut res[32usize..], y)
}

#[inline] fn make_prime(n: &mut [u64])
{
    n[0usize] = 0xffffffffffffffffu64;
    n[1usize] = 0xffffffffu64;
    n[2usize] = 0x0u64;
    n[3usize] = 0xffffffff00000001u64
}

#[inline] fn make_order(n: &mut [u64])
{
    n[0usize] = 0xf3b9cac2fc632551u64;
    n[1usize] = 0xbce6faada7179e84u64;
    n[2usize] = 0xffffffffffffffffu64;
    n[3usize] = 0xffffffff00000000u64
}

#[inline] fn make_a_coeff(a: &mut [u64])
{
    a[0usize] = 0xfffffffffffffffcu64;
    a[1usize] = 0x3ffffffffu64;
    a[2usize] = 0x0u64;
    a[3usize] = 0xfffffffc00000004u64
}

#[inline] fn make_b_coeff(b: &mut [u64])
{
    b[0usize] = 0xd89cdf6229c4bddfu64;
    b[1usize] = 0xacf005cd78843090u64;
    b[2usize] = 0xe5a220abf7212ed6u64;
    b[3usize] = 0xdc30061d04874834u64
}

#[inline] fn make_g_x(n: &mut [u64])
{
    n[0usize] = 0x79e730d418a9143cu64;
    n[1usize] = 0x75ba95fc5fedb601u64;
    n[2usize] = 0x79fb732b77622510u64;
    n[3usize] = 0x18905f76a53755c6u64
}

#[inline] fn make_g_y(n: &mut [u64])
{
    n[0usize] = 0xddf25357ce95560au64;
    n[1usize] = 0x8b4ab8e4ba19e45cu64;
    n[2usize] = 0xd2e88688dd21f325u64;
    n[3usize] = 0x8571ff1825885d85u64
}

#[inline] fn make_fmont_R2(n: &mut [u64])
{
    n[0usize] = 0x3u64;
    n[1usize] = 0xfffffffbffffffffu64;
    n[2usize] = 0xfffffffffffffffeu64;
    n[3usize] = 0x4fffffffdu64
}

#[inline] fn make_fzero(n: &mut [u64])
{
    n[0usize] = 0u64;
    n[1usize] = 0u64;
    n[2usize] = 0u64;
    n[3usize] = 0u64
}

#[inline] fn make_fone(n: &mut [u64])
{
    n[0usize] = 0x1u64;
    n[1usize] = 0xffffffff00000000u64;
    n[2usize] = 0xffffffffffffffffu64;
    n[3usize] = 0xfffffffeu64
}

#[inline] fn bn_is_lt_prime_mask4(f: &mut [u64]) -> u64
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    crate::p256::make_prime(&mut tmp);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&(&mut tmp)[0usize..4usize]);
    let c: u64 = crate::p256::bn_sub4(&mut tmp, f, &mut y_copy);
    let c0: u64 = c;
    0u64.wrapping_sub(c0)
}

#[inline] fn feq_mask(a: &mut [u64], b: &mut [u64]) -> u64
{
    let r: u64 = crate::p256::bn_is_eq_mask4(a, b);
    r
}

#[inline] fn fadd(res: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut n: [u64; 4] = [0u64; 4usize];
    crate::p256::make_prime(&mut n);
    crate::p256::bn_add_mod4(res, &mut n, x, y)
}

#[inline] fn fsub(res: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut n: [u64; 4] = [0u64; 4usize];
    crate::p256::make_prime(&mut n);
    crate::p256::bn_sub_mod4(res, &mut n, x, y)
}

#[inline] fn fnegate_conditional_vartime(f: &mut [u64], is_negate: bool)
{
    let mut zero: [u64; 4] = [0u64; 4usize];
    if is_negate
    {
        let mut y_copy: [u64; 4] = [0u64; 4usize];
        ((&mut y_copy)[0usize..4usize]).copy_from_slice(&f[0usize..4usize]);
        crate::p256::fsub(f, &mut zero, &mut y_copy)
    }
}

#[inline] fn mont_reduction(res: &mut [u64], x: &mut [u64])
{
    let mut n: [u64; 4] = [0u64; 4usize];
    crate::p256::make_prime(&mut n);
    let mut c0: [u64; 1] = [0u64; 1usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let qj: u64 = 1u64.wrapping_mul(x[i as usize]);
            let res_j: (&mut [u64], &mut [u64]) = x.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            {
                let a_i: u64 = (&mut n)[4u32.wrapping_mul(0u32) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    res_j.1.split_at_mut(4u32.wrapping_mul(0u32) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, qj, (&mut c)[0usize], res_i.1);
                let a_i0: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, qj, (&mut c)[0usize], res_i0.1);
                let a_i1: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, qj, (&mut c)[0usize], res_i1.1);
                let a_i2: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, qj, (&mut c)[0usize], res_i2.1)
            };
            let r: u64 = (&mut c)[0usize];
            let c1: u64 = r;
            let res_j0: u64 = x[4u32.wrapping_add(i) as usize];
            let resb: (&mut [u64], &mut [u64]) = x.split_at_mut(i as usize + 4usize);
            (&mut c0)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&mut c0)[0usize], c1, res_j0, resb.1)
        }
    );
    (res[0usize..4usize]).copy_from_slice(&(&mut x[4usize..])[0usize..4usize]);
    let c00: u64 = (&mut c0)[0usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = res[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = (&mut n)[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = tmp.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    let c1: u64 = (&mut c)[0usize];
    let c2: u64 = c00.wrapping_sub(c1);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x1: u64 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x1
        }
    )
}

#[inline] fn fmul(res: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::p256::bn_mul4(&mut tmp, x, y);
    crate::p256::mont_reduction(res, &mut tmp)
}

#[inline] fn fsqr(res: &mut [u64], x: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::p256::bn_sqr4(&mut tmp, x);
    crate::p256::mont_reduction(res, &mut tmp)
}

#[inline] fn from_mont(res: &mut [u64], a: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    ((&mut tmp)[0usize..4usize]).copy_from_slice(&a[0usize..4usize]);
    crate::p256::mont_reduction(res, &mut tmp)
}

#[inline] fn to_mont(res: &mut [u64], a: &mut [u64])
{
    let mut r2modn: [u64; 4] = [0u64; 4usize];
    crate::p256::make_fmont_R2(&mut r2modn);
    crate::p256::fmul(res, a, &mut r2modn)
}

#[inline] fn fmul_by_b_coeff(res: &mut [u64], x: &mut [u64])
{
    let mut b_coeff: [u64; 4] = [0u64; 4usize];
    crate::p256::make_b_coeff(&mut b_coeff);
    crate::p256::fmul(res, &mut b_coeff, x)
}

#[inline] fn fcube(res: &mut [u64], x: &mut [u64])
{
    crate::p256::fsqr(res, x);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&res[0usize..4usize]);
    crate::p256::fmul(res, &mut x_copy, x)
}

#[inline] fn finv(res: &mut [u64], a: &mut [u64])
{
    let mut tmp: [u64; 16] = [0u64; 16usize];
    let x30: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let x2: (&mut [u64], &mut [u64]) = x30.1.split_at_mut(4usize);
    let tmp1: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(4usize);
    (tmp1.0[0usize..4usize]).copy_from_slice(&a[0usize..4usize]);
    {
        let mut x_copy: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
        crate::p256::fsqr(tmp1.0, &mut x_copy)
    };
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
    crate::p256::fmul(tmp1.0, &mut x_copy, a);
    (x2.0[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
    {
        let mut x_copy0: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&x2.0[0usize..4usize]);
        crate::p256::fsqr(x2.0, &mut x_copy0)
    };
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&x2.0[0usize..4usize]);
    crate::p256::fmul(x2.0, &mut x_copy0, a);
    (tmp2.0[0usize..4usize]).copy_from_slice(&x2.0[0usize..4usize]);
    krml::unroll_for!(
        3,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy1: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
            crate::p256::fsqr(tmp2.0, &mut x_copy1)
        }
    );
    let mut x_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    crate::p256::fmul(tmp2.0, &mut x_copy1, x2.0);
    (tmp2.1[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    krml::unroll_for!(
        6,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy2: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
            crate::p256::fsqr(tmp2.1, &mut x_copy2)
        }
    );
    let mut x_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    crate::p256::fmul(tmp2.1, &mut x_copy2, tmp2.0);
    (tmp2.0[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    krml::unroll_for!(
        3,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy3: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
            crate::p256::fsqr(tmp2.0, &mut x_copy3)
        }
    );
    let mut x_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    crate::p256::fmul(tmp2.0, &mut x_copy3, x2.0);
    (x2.0[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    krml::unroll_for!(
        15,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy4: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&x2.0[0usize..4usize]);
            crate::p256::fsqr(x2.0, &mut x_copy4)
        }
    );
    let mut x_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&x2.0[0usize..4usize]);
    crate::p256::fmul(x2.0, &mut x_copy4, tmp2.0);
    (tmp2.0[0usize..4usize]).copy_from_slice(&x2.0[0usize..4usize]);
    krml::unroll_for!(
        2,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy5: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
            crate::p256::fsqr(tmp2.0, &mut x_copy5)
        }
    );
    let mut x_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    crate::p256::fmul(tmp2.0, &mut x_copy5, tmp1.0);
    (tmp1.0[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    krml::unroll_for!(
        32,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy6: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
            crate::p256::fsqr(tmp1.0, &mut x_copy6)
        }
    );
    let mut x_copy6: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
    crate::p256::fmul(tmp1.0, &mut x_copy6, a);
    for _i in 0u32..128u32
    {
        let mut x_copy7: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy7)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
        crate::p256::fsqr(tmp1.0, &mut x_copy7)
    };
    let mut x_copy7: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy7)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
    crate::p256::fmul(tmp1.0, &mut x_copy7, tmp2.0);
    krml::unroll_for!(
        32,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy8: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy8)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
            crate::p256::fsqr(tmp1.0, &mut x_copy8)
        }
    );
    let mut x_copy8: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy8)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
    crate::p256::fmul(tmp1.0, &mut x_copy8, tmp2.0);
    krml::unroll_for!(
        30,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy9: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy9)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
            crate::p256::fsqr(tmp1.0, &mut x_copy9)
        }
    );
    let mut x_copy9: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy9)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
    crate::p256::fmul(tmp1.0, &mut x_copy9, x2.0);
    krml::unroll_for!(
        2,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy10: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy10)[0usize..4usize]).copy_from_slice(&tmp1.0[0usize..4usize]);
            crate::p256::fsqr(tmp1.0, &mut x_copy10)
        }
    );
    crate::p256::fmul(tmp2.0, tmp1.0, a);
    (res[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize])
}

#[inline] fn fsqrt(res: &mut [u64], a: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    let tmp1: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(4usize);
    (tmp2.0[0usize..4usize]).copy_from_slice(&a[0usize..4usize]);
    {
        let mut x_copy: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
        crate::p256::fsqr(tmp2.0, &mut x_copy)
    };
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    crate::p256::fmul(tmp2.0, &mut x_copy, a);
    (tmp2.1[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    krml::unroll_for!(
        2,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy0: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
            crate::p256::fsqr(tmp2.1, &mut x_copy0)
        }
    );
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    crate::p256::fmul(tmp2.1, &mut x_copy0, tmp2.0);
    (tmp2.0[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    krml::unroll_for!(
        4,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy1: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
            crate::p256::fsqr(tmp2.0, &mut x_copy1)
        }
    );
    let mut x_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    crate::p256::fmul(tmp2.0, &mut x_copy1, tmp2.1);
    (tmp2.1[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    krml::unroll_for!(
        8,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy2: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
            crate::p256::fsqr(tmp2.1, &mut x_copy2)
        }
    );
    let mut x_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    crate::p256::fmul(tmp2.1, &mut x_copy2, tmp2.0);
    (tmp2.0[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    krml::unroll_for!(
        16,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy3: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
            crate::p256::fsqr(tmp2.0, &mut x_copy3)
        }
    );
    let mut x_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    crate::p256::fmul(tmp2.0, &mut x_copy3, tmp2.1);
    (tmp2.1[0usize..4usize]).copy_from_slice(&tmp2.0[0usize..4usize]);
    krml::unroll_for!(
        32,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy4: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
            crate::p256::fsqr(tmp2.1, &mut x_copy4)
        }
    );
    let mut x_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    crate::p256::fmul(tmp2.1, &mut x_copy4, a);
    for _i in 0u32..96u32
    {
        let mut x_copy5: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
        crate::p256::fsqr(tmp2.1, &mut x_copy5)
    };
    let mut x_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
    crate::p256::fmul(tmp2.1, &mut x_copy5, a);
    for _i in 0u32..94u32
    {
        let mut x_copy6: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize]);
        crate::p256::fsqr(tmp2.1, &mut x_copy6)
    };
    (res[0usize..4usize]).copy_from_slice(&tmp2.1[0usize..4usize])
}

#[inline] fn make_base_point(p: &mut [u64])
{
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(4usize);
    crate::p256::make_g_x(y.0);
    crate::p256::make_g_y(z.0);
    crate::p256::make_fone(z.1)
}

#[inline] fn make_point_at_inf(p: &mut [u64])
{
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(4usize);
    crate::p256::make_fzero(y.0);
    crate::p256::make_fone(z.0);
    crate::p256::make_fzero(z.1)
}

#[inline] fn is_point_at_inf_vartime(p: &mut [u64]) -> bool
{
    let pz: (&mut [u64], &mut [u64]) = p.split_at_mut(8usize);
    crate::p256::bn_is_zero_vartime4(pz.1)
}

#[inline] fn to_aff_point(res: &mut [u64], p: &mut [u64])
{
    let mut zinv: [u64; 4] = [0u64; 4usize];
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    let pz: (&mut [u64], &mut [u64]) = py.1.split_at_mut(4usize);
    let x: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    crate::p256::finv(&mut zinv, pz.1);
    crate::p256::fmul(y.0, py.0, &mut zinv);
    crate::p256::fmul(y.1, pz.0, &mut zinv);
    let mut a_copy: [u64; 4] = [0u64; 4usize];
    ((&mut a_copy)[0usize..4usize]).copy_from_slice(&y.0[0usize..4usize]);
    crate::p256::from_mont(y.0, &mut a_copy);
    let mut a_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut a_copy0)[0usize..4usize]).copy_from_slice(&y.1[0usize..4usize]);
    crate::p256::from_mont(y.1, &mut a_copy0)
}

#[inline] fn to_aff_point_x(res: &mut [u64], p: &mut [u64])
{
    let mut zinv: [u64; 4] = [0u64; 4usize];
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let pz: (&mut [u64], &mut [u64]) = px.1.split_at_mut(8usize);
    crate::p256::finv(&mut zinv, pz.1);
    crate::p256::fmul(res, pz.0, &mut zinv);
    let mut a_copy: [u64; 4] = [0u64; 4usize];
    ((&mut a_copy)[0usize..4usize]).copy_from_slice(&res[0usize..4usize]);
    crate::p256::from_mont(res, &mut a_copy)
}

#[inline] fn to_proj_point(res: &mut [u64], p: &mut [u64])
{
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    let rx: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let ry: (&mut [u64], &mut [u64]) = rx.1.split_at_mut(4usize);
    let rz: (&mut [u64], &mut [u64]) = ry.1.split_at_mut(4usize);
    crate::p256::to_mont(ry.0, py.0);
    crate::p256::to_mont(rz.0, py.1);
    crate::p256::make_fone(rz.1)
}

#[inline] fn is_on_curve_vartime(p: &mut [u64]) -> bool
{
    let mut rp: [u64; 4] = [0u64; 4usize];
    let mut tx: [u64; 4] = [0u64; 4usize];
    let mut ty: [u64; 4] = [0u64; 4usize];
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    crate::p256::to_mont(&mut tx, py.0);
    crate::p256::to_mont(&mut ty, py.1);
    let mut tmp: [u64; 4] = [0u64; 4usize];
    crate::p256::fcube(&mut rp, &mut tx);
    crate::p256::make_a_coeff(&mut tmp);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut tmp)[0usize..4usize]);
    crate::p256::fmul(&mut tmp, &mut x_copy, &mut tx);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&(&mut rp)[0usize..4usize]);
    crate::p256::fadd(&mut rp, &mut tmp, &mut y_copy);
    crate::p256::make_b_coeff(&mut tmp);
    let mut y_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy0)[0usize..4usize]).copy_from_slice(&(&mut rp)[0usize..4usize]);
    crate::p256::fadd(&mut rp, &mut tmp, &mut y_copy0);
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&(&mut ty)[0usize..4usize]);
    crate::p256::fsqr(&mut ty, &mut x_copy0);
    let r: u64 = crate::p256::feq_mask(&mut ty, &mut rp);
    let r0: bool = r == 0xFFFFFFFFFFFFFFFFu64;
    r0
}

#[inline] fn aff_point_store(res: &mut [u8], p: &mut [u64])
{
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    crate::p256::bn2_to_bytes_be4(res, py.0, py.1)
}

#[inline] fn point_store(res: &mut [u8], p: &mut [u64])
{
    let mut aff_p: [u64; 8] = [0u64; 8usize];
    crate::p256::to_aff_point(&mut aff_p, p);
    crate::p256::aff_point_store(res, &mut aff_p)
}

#[inline] fn aff_point_load_vartime(p: &mut [u64], b: &mut [u8]) -> bool
{
    let p_x: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    let p_y: (&mut [u8], &mut [u8]) = p_x.1.split_at_mut(32usize);
    let bn_p_x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let bn_p_y: (&mut [u64], &mut [u64]) = bn_p_x.1.split_at_mut(4usize);
    crate::p256::bn_from_bytes_be4(bn_p_y.0, p_y.0);
    crate::p256::bn_from_bytes_be4(bn_p_y.1, p_y.1);
    let px: (&mut [u64], &mut [u64]) = bn_p_y.0.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = bn_p_y.1.split_at_mut(0usize);
    let lessX: u64 = crate::p256::bn_is_lt_prime_mask4(px.1);
    let lessY: u64 = crate::p256::bn_is_lt_prime_mask4(py.1);
    let res: u64 = lessX & lessY;
    let is_xy_valid: bool = res == 0xFFFFFFFFFFFFFFFFu64;
    if ! is_xy_valid { false } else { crate::p256::is_on_curve_vartime(p) }
}

#[inline] fn load_point_vartime(p: &mut [u64], b: &mut [u8]) -> bool
{
    let mut p_aff: [u64; 8] = [0u64; 8usize];
    let res: bool = crate::p256::aff_point_load_vartime(&mut p_aff, b);
    if res { crate::p256::to_proj_point(p, &mut p_aff) };
    res
}

#[inline] fn aff_point_decompress_vartime(x: &mut [u64], y: &mut [u64], s: &mut [u8]) -> bool
{
    let s0: u8 = s[0usize];
    let s01: u8 = s0;
    if ! (s01 == 0x02u8 || s01 == 0x03u8)
    { false }
    else
    {
        let xb: (&mut [u8], &mut [u8]) = s.split_at_mut(1usize);
        crate::p256::bn_from_bytes_be4(x, xb.1);
        let is_x_valid: u64 = crate::p256::bn_is_lt_prime_mask4(x);
        let is_x_valid1: bool = is_x_valid == 0xFFFFFFFFFFFFFFFFu64;
        let is_y_odd: bool = s01 == 0x03u8;
        if ! is_x_valid1
        { false }
        else
        {
            let mut y2M: [u64; 4] = [0u64; 4usize];
            let mut xM: [u64; 4] = [0u64; 4usize];
            let mut yM: [u64; 4] = [0u64; 4usize];
            crate::p256::to_mont(&mut xM, x);
            let mut tmp: [u64; 4] = [0u64; 4usize];
            crate::p256::fcube(&mut y2M, &mut xM);
            crate::p256::make_a_coeff(&mut tmp);
            let mut x_copy: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut tmp)[0usize..4usize]);
            crate::p256::fmul(&mut tmp, &mut x_copy, &mut xM);
            let mut y_copy: [u64; 4] = [0u64; 4usize];
            ((&mut y_copy)[0usize..4usize]).copy_from_slice(&(&mut y2M)[0usize..4usize]);
            crate::p256::fadd(&mut y2M, &mut tmp, &mut y_copy);
            crate::p256::make_b_coeff(&mut tmp);
            let mut y_copy0: [u64; 4] = [0u64; 4usize];
            ((&mut y_copy0)[0usize..4usize]).copy_from_slice(&(&mut y2M)[0usize..4usize]);
            crate::p256::fadd(&mut y2M, &mut tmp, &mut y_copy0);
            crate::p256::fsqrt(&mut yM, &mut y2M);
            crate::p256::from_mont(y, &mut yM);
            let mut x_copy0: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&(&mut yM)[0usize..4usize]);
            crate::p256::fsqr(&mut yM, &mut x_copy0);
            let r: u64 = crate::p256::feq_mask(&mut yM, &mut y2M);
            let is_y_valid: bool = r == 0xFFFFFFFFFFFFFFFFu64;
            let is_y_valid0: bool = is_y_valid;
            if ! is_y_valid0
            { false }
            else
            {
                let is_y_odd1: u64 = y[0usize] & 1u64;
                let is_y_odd2: bool = is_y_odd1 == 1u64;
                crate::p256::fnegate_conditional_vartime(y, is_y_odd2 != is_y_odd);
                true
            }
        }
    }
}

#[inline] fn point_double(res: &mut [u64], p: &mut [u64])
{
    let mut tmp: [u64; 20] = [0u64; 20usize];
    let x3: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(4usize);
    let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(4usize);
    let t0: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(4usize);
    let t2: (&mut [u64], &mut [u64]) = t1.1.split_at_mut(4usize);
    let t3: (&mut [u64], &mut [u64]) = t2.1.split_at_mut(4usize);
    let t4: (&mut [u64], &mut [u64]) = t3.1.split_at_mut(4usize);
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(4usize);
    crate::p256::fsqr(t1.0, y.0);
    crate::p256::fsqr(t2.0, z.0);
    crate::p256::fsqr(t3.0, z.1);
    crate::p256::fmul(t4.0, y.0, z.0);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&t4.0[0usize..4usize]);
    let mut x_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&(&mut x_copy)[0usize..4usize]);
    crate::p256::fadd(t4.0, &mut x_copy1, &mut x_copy);
    crate::p256::fmul(t4.1, z.0, z.1);
    let x0: (&mut [u64], &mut [u64]) = y.0.split_at_mut(0usize);
    let z0: (&mut [u64], &mut [u64]) = z.1.split_at_mut(0usize);
    crate::p256::fmul(z3.1, x0.1, z0.1);
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    let mut x_copy10: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy10)[0usize..4usize]).copy_from_slice(&(&mut x_copy0)[0usize..4usize]);
    crate::p256::fadd(z3.1, &mut x_copy10, &mut x_copy0);
    crate::p256::fmul_by_b_coeff(z3.0, t3.0);
    let mut x_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fsub(z3.0, &mut x_copy2, z3.1);
    let mut x_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(y3.0, &mut x_copy3, z3.0);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(z3.0, y3.0, &mut y_copy);
    crate::p256::fsub(y3.0, t2.0, z3.0);
    let mut y_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy0)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(z3.0, t2.0, &mut y_copy0);
    let mut y_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy1)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fmul(z3.0, y3.0, &mut y_copy1);
    let mut x_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fmul(y3.0, &mut x_copy4, t4.0);
    let mut x_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&t3.0[0usize..4usize]);
    crate::p256::fadd(t4.0, &mut x_copy5, t3.0);
    let mut x_copy6: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&t3.0[0usize..4usize]);
    crate::p256::fadd(t3.0, &mut x_copy6, t4.0);
    let mut x_copy7: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy7)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fmul_by_b_coeff(z3.1, &mut x_copy7);
    let mut x_copy8: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy8)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fsub(z3.1, &mut x_copy8, t3.0);
    let mut x_copy9: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy9)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fsub(z3.1, &mut x_copy9, t1.0);
    let mut x_copy11: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy11)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fadd(t4.0, &mut x_copy11, z3.1);
    let mut x_copy12: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy12)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fadd(z3.1, &mut x_copy12, t4.0);
    let mut x_copy13: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy13)[0usize..4usize]).copy_from_slice(&t1.0[0usize..4usize]);
    crate::p256::fadd(t4.0, &mut x_copy13, t1.0);
    let mut y_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy2)[0usize..4usize]).copy_from_slice(&t1.0[0usize..4usize]);
    crate::p256::fadd(t1.0, t4.0, &mut y_copy2);
    let mut x_copy14: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy14)[0usize..4usize]).copy_from_slice(&t1.0[0usize..4usize]);
    crate::p256::fsub(t1.0, &mut x_copy14, t3.0);
    let mut x_copy15: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy15)[0usize..4usize]).copy_from_slice(&t1.0[0usize..4usize]);
    crate::p256::fmul(t1.0, &mut x_copy15, z3.1);
    let mut x_copy16: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy16)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(z3.0, &mut x_copy16, t1.0);
    let mut x_copy17: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy17)[0usize..4usize]).copy_from_slice(&t4.1[0usize..4usize]);
    crate::p256::fadd(t1.0, &mut x_copy17, t4.1);
    let mut y_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy3)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fmul(z3.1, t1.0, &mut y_copy3);
    let mut x_copy18: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy18)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fsub(y3.0, &mut x_copy18, z3.1);
    crate::p256::fmul(z3.1, t1.0, t2.0);
    let mut x_copy19: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy19)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    let mut x_copy110: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy110)[0usize..4usize]).copy_from_slice(&(&mut x_copy19)[0usize..4usize]);
    crate::p256::fadd(z3.1, &mut x_copy110, &mut x_copy19);
    let mut x_copy20: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy20)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    let mut x_copy111: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy111)[0usize..4usize]).copy_from_slice(&(&mut x_copy20)[0usize..4usize]);
    crate::p256::fadd(z3.1, &mut x_copy111, &mut x_copy20)
}

#[inline] fn point_add(res: &mut [u64], p: &mut [u64], q: &mut [u64])
{
    let mut tmp: [u64; 36] = [0u64; 36usize];
    let t0: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(24usize);
    let x3: (&mut [u64], &mut [u64]) = t1.1.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(4usize);
    let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(4usize);
    let t01: (&mut [u64], &mut [u64]) = t1.0.split_at_mut(0usize);
    let t11: (&mut [u64], &mut [u64]) = t01.1.split_at_mut(4usize);
    let t2: (&mut [u64], &mut [u64]) = t11.1.split_at_mut(4usize);
    let t3: (&mut [u64], &mut [u64]) = t2.1.split_at_mut(4usize);
    let t4: (&mut [u64], &mut [u64]) = t3.1.split_at_mut(4usize);
    let t5: (&mut [u64], &mut [u64]) = t4.1.split_at_mut(4usize);
    let x1: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(4usize);
    let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(4usize);
    let x2: (&mut [u64], &mut [u64]) = q.split_at_mut(0usize);
    let y2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let z2: (&mut [u64], &mut [u64]) = y2.1.split_at_mut(4usize);
    crate::p256::fmul(t11.0, y1.0, y2.0);
    crate::p256::fmul(t2.0, z1.0, z2.0);
    crate::p256::fmul(t3.0, z1.1, z2.1);
    crate::p256::fadd(t4.0, y1.0, z1.0);
    crate::p256::fadd(t5.0, y2.0, z2.0);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&t4.0[0usize..4usize]);
    crate::p256::fmul(t4.0, &mut x_copy, t5.0);
    crate::p256::fadd(t5.0, t11.0, t2.0);
    let y10: (&mut [u64], &mut [u64]) = z1.0.split_at_mut(0usize);
    let z10: (&mut [u64], &mut [u64]) = z1.1.split_at_mut(0usize);
    let y20: (&mut [u64], &mut [u64]) = z2.0.split_at_mut(0usize);
    let z20: (&mut [u64], &mut [u64]) = z2.1.split_at_mut(0usize);
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&t4.0[0usize..4usize]);
    crate::p256::fsub(t4.0, &mut x_copy0, t5.0);
    crate::p256::fadd(t5.0, y10.1, z10.1);
    crate::p256::fadd(t5.1, y20.1, z20.1);
    let mut x_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&t5.0[0usize..4usize]);
    crate::p256::fmul(t5.0, &mut x_copy1, t5.1);
    crate::p256::fadd(t5.1, t2.0, t3.0);
    let mut x_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&t5.0[0usize..4usize]);
    crate::p256::fsub(t5.0, &mut x_copy2, t5.1);
    let x10: (&mut [u64], &mut [u64]) = y1.0.split_at_mut(0usize);
    let z11: (&mut [u64], &mut [u64]) = z10.1.split_at_mut(0usize);
    let x20: (&mut [u64], &mut [u64]) = y2.0.split_at_mut(0usize);
    let z21: (&mut [u64], &mut [u64]) = z20.1.split_at_mut(0usize);
    crate::p256::fadd(y3.0, x10.1, z11.1);
    crate::p256::fadd(z3.0, x20.1, z21.1);
    let mut x_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fmul(y3.0, &mut x_copy3, z3.0);
    crate::p256::fadd(z3.0, t11.0, t3.0);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fsub(z3.0, y3.0, &mut y_copy);
    crate::p256::fmul_by_b_coeff(z3.1, t3.0);
    crate::p256::fsub(y3.0, z3.0, z3.1);
    let mut x_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fadd(z3.1, &mut x_copy4, y3.0);
    let mut x_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fadd(y3.0, &mut x_copy5, z3.1);
    crate::p256::fsub(z3.1, t2.0, y3.0);
    let mut y_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy0)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fadd(y3.0, t2.0, &mut y_copy0);
    let mut x_copy6: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fmul_by_b_coeff(z3.0, &mut x_copy6);
    let mut x_copy7: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy7)[0usize..4usize]).copy_from_slice(&t3.0[0usize..4usize]);
    crate::p256::fadd(t2.0, &mut x_copy7, t3.0);
    let mut y_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy1)[0usize..4usize]).copy_from_slice(&t3.0[0usize..4usize]);
    crate::p256::fadd(t3.0, t2.0, &mut y_copy1);
    let mut x_copy8: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy8)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fsub(z3.0, &mut x_copy8, t3.0);
    let mut x_copy9: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy9)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fsub(z3.0, &mut x_copy9, t11.0);
    let mut x_copy10: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy10)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(t2.0, &mut x_copy10, z3.0);
    let mut y_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy2)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(z3.0, t2.0, &mut y_copy2);
    let mut x_copy11: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy11)[0usize..4usize]).copy_from_slice(&t11.0[0usize..4usize]);
    crate::p256::fadd(t2.0, &mut x_copy11, t11.0);
    let mut y_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy3)[0usize..4usize]).copy_from_slice(&t11.0[0usize..4usize]);
    crate::p256::fadd(t11.0, t2.0, &mut y_copy3);
    let mut x_copy12: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy12)[0usize..4usize]).copy_from_slice(&t11.0[0usize..4usize]);
    crate::p256::fsub(t11.0, &mut x_copy12, t3.0);
    crate::p256::fmul(t2.0, t5.0, z3.0);
    crate::p256::fmul(t3.0, t11.0, z3.0);
    crate::p256::fmul(z3.0, y3.0, z3.1);
    let mut x_copy13: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy13)[0usize..4usize]).copy_from_slice(&z3.0[0usize..4usize]);
    crate::p256::fadd(z3.0, &mut x_copy13, t3.0);
    let mut y_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy4)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fmul(y3.0, t4.0, &mut y_copy4);
    let mut x_copy14: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy14)[0usize..4usize]).copy_from_slice(&y3.0[0usize..4usize]);
    crate::p256::fsub(y3.0, &mut x_copy14, t2.0);
    let mut y_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy5)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fmul(z3.1, t5.0, &mut y_copy5);
    crate::p256::fmul(t2.0, t4.0, t11.0);
    let mut x_copy15: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy15)[0usize..4usize]).copy_from_slice(&z3.1[0usize..4usize]);
    crate::p256::fadd(z3.1, &mut x_copy15, t2.0);
    (res[0usize..12usize]).copy_from_slice(&t1.1[0usize..12usize])
}

#[inline] fn point_mul(res: &mut [u64], scalar: &mut [u64], p: &mut [u64])
{
    let mut table: [u64; 192] = [0u64; 192usize];
    let mut tmp: [u64; 12] = [0u64; 12usize];
    let t0: (&mut [u64], &mut [u64]) = table.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(12usize);
    crate::p256::make_point_at_inf(t1.0);
    (t1.1[0usize..12usize]).copy_from_slice(&p[0usize..12usize]);
    lowstar::ignore::ignore::<&mut [u64]>(&mut table);
    krml::unroll_for!(
        7,
        "i",
        0u32,
        1u32,
        {
            let t11: (&mut [u64], &mut [u64]) =
                table.split_at_mut(i.wrapping_add(1u32).wrapping_mul(12u32) as usize);
            let mut p_copy: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy)[0usize..12usize]).copy_from_slice(&t11.1[0usize..12usize]);
            crate::p256::point_double(&mut tmp, &mut p_copy);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(12u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(12u32)
            as
            usize
            +
            12usize]).copy_from_slice(&(&mut tmp)[0usize..12usize]);
            let t2: (&mut [u64], &mut [u64]) =
                table.split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(12u32) as usize
                );
            let mut p_copy0: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy0)[0usize..12usize]).copy_from_slice(&p[0usize..12usize]);
            crate::p256::point_add(&mut tmp, &mut p_copy0, t2.1);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(12u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(12u32)
            as
            usize
            +
            12usize]).copy_from_slice(&(&mut tmp)[0usize..12usize])
        }
    );
    crate::p256::make_point_at_inf(res);
    let mut tmp0: [u64; 12] = [0u64; 12usize];
    for i in 0u32..64u32
    {
        krml::unroll_for!(
            4,
            "_i",
            0u32,
            1u32,
            {
                let mut p_copy: [u64; 12] = [0u64; 12usize];
                ((&mut p_copy)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
                crate::p256::point_double(res, &mut p_copy)
            }
        );
        let k: u32 = 256u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar, k, 4u32);
        lowstar::ignore::ignore::<&mut [u64]>(&mut table);
        ((&mut tmp0)[0usize..12usize]).copy_from_slice(
            &(&mut (&mut table)[0usize..] as &mut [u64])[0usize..12usize]
        );
        krml::unroll_for!(
            15,
            "i0",
            0u32,
            1u32,
            {
                let c: u64 = fstar::uint64::eq_mask(bits_l, i0.wrapping_add(1u32) as u64);
                let res_j: (&mut [u64], &mut [u64]) =
                    table.split_at_mut(i0.wrapping_add(1u32).wrapping_mul(12u32) as usize);
                krml::unroll_for!(
                    12,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let x: u64 = c & res_j.1[i1 as usize] | ! c & (&mut tmp0)[i1 as usize];
                        let os: (&mut [u64], &mut [u64]) = tmp0.split_at_mut(0usize);
                        os.1[i1 as usize] = x
                    }
                )
            }
        );
        let mut p_copy: [u64; 12] = [0u64; 12usize];
        ((&mut p_copy)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
        crate::p256::point_add(res, &mut p_copy, &mut tmp0)
    }
}

#[inline] fn precomp_get_consttime(table: &mut [u64], bits_l: u64, tmp: &mut [u64])
{
    (tmp[0usize..12usize]).copy_from_slice(&(&mut table[0usize..])[0usize..12usize]);
    krml::unroll_for!(
        15,
        "i",
        0u32,
        1u32,
        {
            let c: u64 = fstar::uint64::eq_mask(bits_l, i.wrapping_add(1u32) as u64);
            let res_j: (&mut [u64], &mut [u64]) =
                table.split_at_mut(i.wrapping_add(1u32).wrapping_mul(12u32) as usize);
            krml::unroll_for!(
                12,
                "i0",
                0u32,
                1u32,
                {
                    let x: u64 = c & res_j.1[i0 as usize] | ! c & tmp[i0 as usize];
                    let os: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
                    os.1[i0 as usize] = x
                }
            )
        }
    )
}

#[inline] fn point_mul_g(res: &mut [u64], scalar: &mut [u64])
{
    let mut q1: [u64; 12] = [0u64; 12usize];
    crate::p256::make_base_point(&mut q1);
    let mut q2: [u64; 12] =
        [1499621593102562565u64, 16692369783039433128u64, 15337520135922861848u64,
            5455737214495366228u64, 17827017231032529600u64, 12413621606240782649u64,
            2290483008028286132u64, 15752017553340844820u64, 4846430910634234874u64,
            10861682798464583253u64, 15404737222404363049u64, 363586619281562022u64];
    let mut q3: [u64; 12] =
        [14619254753077084366u64, 13913835116514008593u64, 15060744674088488145u64,
            17668414598203068685u64, 10761169236902342334u64, 15467027479157446221u64,
            14989185522423469618u64, 14354539272510107003u64, 14298211796392133693u64,
            13270323784253711450u64, 13380964971965046957u64, 8686204248456909699u64];
    let mut q4: [u64; 12] =
        [7870395003430845958u64, 18001862936410067720u64, 8006461232116967215u64,
            5921313779532424762u64, 10702113371959864307u64, 8070517410642379879u64,
            7139806720777708306u64, 8253938546650739833u64, 17490482834545705718u64,
            1065249776797037500u64, 5018258455937968775u64, 14100621120178668337u64];
    let r1: (&mut [u64], &mut [u64]) = scalar.split_at_mut(0usize);
    let r2: (&mut [u64], &mut [u64]) = r1.1.split_at_mut(1usize);
    let r3: (&mut [u64], &mut [u64]) = r2.1.split_at_mut(1usize);
    let r4: (&mut [u64], &mut [u64]) = r3.1.split_at_mut(1usize);
    crate::p256::make_point_at_inf(res);
    let mut tmp: [u64; 12] = [0u64; 12usize];
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            krml::unroll_for!(
                4,
                "_i",
                0u32,
                1u32,
                {
                    let mut p_copy: [u64; 12] = [0u64; 12usize];
                    ((&mut p_copy)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
                    crate::p256::point_double(res, &mut p_copy)
                }
            );
            let k: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r4.1, k, 4u32);
            lowstar::ignore::ignore::<&mut [u64]>(
                &mut crate::p256_precomptable::precomp_g_pow2_192_table_w4
            );
            crate::p256::precomp_get_consttime(
                &mut crate::p256_precomptable::precomp_g_pow2_192_table_w4,
                bits_l,
                &mut tmp
            );
            let mut p_copy: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
            crate::p256::point_add(res, &mut p_copy, &mut tmp);
            let k0: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l0: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r4.0, k0, 4u32);
            lowstar::ignore::ignore::<&mut [u64]>(
                &mut crate::p256_precomptable::precomp_g_pow2_128_table_w4
            );
            crate::p256::precomp_get_consttime(
                &mut crate::p256_precomptable::precomp_g_pow2_128_table_w4,
                bits_l0,
                &mut tmp
            );
            let mut p_copy0: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy0)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
            crate::p256::point_add(res, &mut p_copy0, &mut tmp);
            let k1: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l1: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r3.0, k1, 4u32);
            lowstar::ignore::ignore::<&mut [u64]>(
                &mut crate::p256_precomptable::precomp_g_pow2_64_table_w4
            );
            crate::p256::precomp_get_consttime(
                &mut crate::p256_precomptable::precomp_g_pow2_64_table_w4,
                bits_l1,
                &mut tmp
            );
            let mut p_copy1: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy1)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
            crate::p256::point_add(res, &mut p_copy1, &mut tmp);
            let k2: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l2: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r2.0, k2, 4u32);
            lowstar::ignore::ignore::<&mut [u64]>(
                &mut crate::p256_precomptable::precomp_basepoint_table_w4
            );
            crate::p256::precomp_get_consttime(
                &mut crate::p256_precomptable::precomp_basepoint_table_w4,
                bits_l2,
                &mut tmp
            );
            let mut p_copy2: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy2)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
            crate::p256::point_add(res, &mut p_copy2, &mut tmp)
        }
    );
    lowstar::ignore::ignore::<&mut [u64]>(&mut q1);
    lowstar::ignore::ignore::<&mut [u64]>(&mut q2);
    lowstar::ignore::ignore::<&mut [u64]>(&mut q3);
    lowstar::ignore::ignore::<&mut [u64]>(&mut q4)
}

#[inline] fn point_mul_double_g(
    res: &mut [u64],
    scalar1: &mut [u64],
    scalar2: &mut [u64],
    q2: &mut [u64]
)
{
    let mut q1: [u64; 12] = [0u64; 12usize];
    crate::p256::make_base_point(&mut q1);
    let mut table2: [u64; 384] = [0u64; 384usize];
    let mut tmp: [u64; 12] = [0u64; 12usize];
    let t0: (&mut [u64], &mut [u64]) = table2.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(12usize);
    crate::p256::make_point_at_inf(t1.0);
    (t1.1[0usize..12usize]).copy_from_slice(&q2[0usize..12usize]);
    lowstar::ignore::ignore::<&mut [u64]>(&mut table2);
    krml::unroll_for!(
        15,
        "i",
        0u32,
        1u32,
        {
            let t11: (&mut [u64], &mut [u64]) =
                table2.split_at_mut(i.wrapping_add(1u32).wrapping_mul(12u32) as usize);
            let mut p_copy: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy)[0usize..12usize]).copy_from_slice(&t11.1[0usize..12usize]);
            crate::p256::point_double(&mut tmp, &mut p_copy);
            ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(12u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(12u32)
            as
            usize
            +
            12usize]).copy_from_slice(&(&mut tmp)[0usize..12usize]);
            let t2: (&mut [u64], &mut [u64]) =
                table2.split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(12u32) as usize
                );
            let mut p_copy0: [u64; 12] = [0u64; 12usize];
            ((&mut p_copy0)[0usize..12usize]).copy_from_slice(&q2[0usize..12usize]);
            crate::p256::point_add(&mut tmp, &mut p_copy0, t2.1);
            ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(12u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(12u32)
            as
            usize
            +
            12usize]).copy_from_slice(&(&mut tmp)[0usize..12usize])
        }
    );
    let mut tmp0: [u64; 12] = [0u64; 12usize];
    let i: u32 = 255u32;
    let bits_c: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar1, i, 5u32);
    let bits_l32: u32 = bits_c as u32;
    let a_bits_l: &mut [u64] =
        &mut
        (&mut crate::p256_precomptable::precomp_basepoint_table_w5)[bits_l32.wrapping_mul(12u32)
        as
        usize..];
    (res[0usize..12usize]).copy_from_slice(&a_bits_l[0usize..12usize]);
    let i0: u32 = 255u32;
    let bits_c0: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar2, i0, 5u32);
    let bits_l320: u32 = bits_c0 as u32;
    let a_bits_l0: (&mut [u64], &mut [u64]) =
        table2.split_at_mut(bits_l320.wrapping_mul(12u32) as usize);
    ((&mut tmp0)[0usize..12usize]).copy_from_slice(&a_bits_l0.1[0usize..12usize]);
    let mut p_copy: [u64; 12] = [0u64; 12usize];
    ((&mut p_copy)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
    crate::p256::point_add(res, &mut p_copy, &mut tmp0);
    let mut tmp1: [u64; 12] = [0u64; 12usize];
    for i1 in 0u32..51u32
    {
        krml::unroll_for!(
            5,
            "_i",
            0u32,
            1u32,
            {
                let mut p_copy0: [u64; 12] = [0u64; 12usize];
                ((&mut p_copy0)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
                crate::p256::point_double(res, &mut p_copy0)
            }
        );
        let k: u32 = 255u32.wrapping_sub(5u32.wrapping_mul(i1)).wrapping_sub(5u32);
        let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar2, k, 5u32);
        lowstar::ignore::ignore::<&mut [u64]>(&mut table2);
        let bits_l321: u32 = bits_l as u32;
        let a_bits_l1: (&mut [u64], &mut [u64]) =
            table2.split_at_mut(bits_l321.wrapping_mul(12u32) as usize);
        ((&mut tmp1)[0usize..12usize]).copy_from_slice(&a_bits_l1.1[0usize..12usize]);
        let mut p_copy0: [u64; 12] = [0u64; 12usize];
        ((&mut p_copy0)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
        crate::p256::point_add(res, &mut p_copy0, &mut tmp1);
        let k0: u32 = 255u32.wrapping_sub(5u32.wrapping_mul(i1)).wrapping_sub(5u32);
        let bits_l0: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar1, k0, 5u32);
        lowstar::ignore::ignore::<&mut [u64]>(
            &mut crate::p256_precomptable::precomp_basepoint_table_w5
        );
        let bits_l322: u32 = bits_l0 as u32;
        let a_bits_l2: &mut [u64] =
            &mut
            (&mut crate::p256_precomptable::precomp_basepoint_table_w5)[bits_l322.wrapping_mul(
                12u32
            )
            as
            usize..];
        ((&mut tmp1)[0usize..12usize]).copy_from_slice(&a_bits_l2[0usize..12usize]);
        let mut p_copy1: [u64; 12] = [0u64; 12usize];
        ((&mut p_copy1)[0usize..12usize]).copy_from_slice(&res[0usize..12usize]);
        crate::p256::point_add(res, &mut p_copy1, &mut tmp1)
    }
}

#[inline] fn bn_is_lt_order_mask4(f: &mut [u64]) -> u64
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    crate::p256::make_order(&mut tmp);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&(&mut tmp)[0usize..4usize]);
    let c: u64 = crate::p256::bn_sub4(&mut tmp, f, &mut y_copy);
    let c0: u64 = c;
    0u64.wrapping_sub(c0)
}

#[inline] fn bn_is_lt_order_and_gt_zero_mask4(f: &mut [u64]) -> u64
{
    let is_lt_order: u64 = crate::p256::bn_is_lt_order_mask4(f);
    let is_eq_zero: u64 = crate::p256::bn_is_zero_mask4(f);
    is_lt_order & ! is_eq_zero
}

#[inline] fn qmod_short(res: &mut [u64], x: &mut [u64])
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    crate::p256::make_order(&mut tmp);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&(&mut tmp)[0usize..4usize]);
    let c: u64 = crate::p256::bn_sub4(&mut tmp, x, &mut y_copy);
    let c0: u64 = c;
    crate::p256::bn_cmovznz4(res, c0, &mut tmp, x)
}

#[inline] fn qadd(res: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut n: [u64; 4] = [0u64; 4usize];
    crate::p256::make_order(&mut n);
    crate::p256::bn_add_mod4(res, &mut n, x, y)
}

#[inline] fn qmont_reduction(res: &mut [u64], x: &mut [u64])
{
    let mut n: [u64; 4] = [0u64; 4usize];
    crate::p256::make_order(&mut n);
    let mut c0: [u64; 1] = [0u64; 1usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let qj: u64 = 0xccd1c8aaee00bc4fu64.wrapping_mul(x[i as usize]);
            let res_j: (&mut [u64], &mut [u64]) = x.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            {
                let a_i: u64 = (&mut n)[4u32.wrapping_mul(0u32) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    res_j.1.split_at_mut(4u32.wrapping_mul(0u32) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, qj, (&mut c)[0usize], res_i.1);
                let a_i0: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, qj, (&mut c)[0usize], res_i0.1);
                let a_i1: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, qj, (&mut c)[0usize], res_i1.1);
                let a_i2: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, qj, (&mut c)[0usize], res_i2.1)
            };
            let r: u64 = (&mut c)[0usize];
            let c1: u64 = r;
            let res_j0: u64 = x[4u32.wrapping_add(i) as usize];
            let resb: (&mut [u64], &mut [u64]) = x.split_at_mut(i as usize + 4usize);
            (&mut c0)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&mut c0)[0usize], c1, res_j0, resb.1)
        }
    );
    (res[0usize..4usize]).copy_from_slice(&(&mut x[4usize..])[0usize..4usize]);
    let c00: u64 = (&mut c0)[0usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = res[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = (&mut n)[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = tmp.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = (&mut n)[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    let c1: u64 = (&mut c)[0usize];
    let c2: u64 = c00.wrapping_sub(c1);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x1: u64 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x1
        }
    )
}

#[inline] fn from_qmont(res: &mut [u64], x: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    ((&mut tmp)[0usize..4usize]).copy_from_slice(&x[0usize..4usize]);
    crate::p256::qmont_reduction(res, &mut tmp)
}

#[inline] fn qmul(res: &mut [u64], x: &mut [u64], y: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::p256::bn_mul4(&mut tmp, x, y);
    crate::p256::qmont_reduction(res, &mut tmp)
}

#[inline] fn qsqr(res: &mut [u64], x: &mut [u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::p256::bn_sqr4(&mut tmp, x);
    crate::p256::qmont_reduction(res, &mut tmp)
}

pub(crate) fn ecp256dh_i(public_key: &mut [u8], private_key: &mut [u8]) -> bool
{
    let mut tmp: [u64; 16] = [0u64; 16usize];
    let sk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let pk: (&mut [u64], &mut [u64]) = sk.1.split_at_mut(4usize);
    crate::p256::bn_from_bytes_be4(pk.0, private_key);
    let is_b_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(pk.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = (&mut oneq)[i as usize];
            let x: u64 = uu____0 ^ is_b_valid & (pk.0[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = pk.0.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_sk_valid: u64 = is_b_valid;
    crate::p256::point_mul_g(pk.1, pk.0);
    crate::p256::point_store(public_key, pk.1);
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64
}

pub(crate) fn ecp256dh_r(
    shared_secret: &mut [u8],
    their_pubkey: &mut [u8],
    private_key: &mut [u8]
) ->
    bool
{
    let mut tmp: [u64; 16] = [0u64; 16usize];
    let sk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let pk: (&mut [u64], &mut [u64]) = sk.1.split_at_mut(4usize);
    let is_pk_valid: bool = crate::p256::load_point_vartime(pk.1, their_pubkey);
    crate::p256::bn_from_bytes_be4(pk.0, private_key);
    let is_b_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(pk.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = (&mut oneq)[i as usize];
            let x: u64 = uu____0 ^ is_b_valid & (pk.0[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = pk.0.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_sk_valid: u64 = is_b_valid;
    let mut ss_proj: [u64; 12] = [0u64; 12usize];
    if is_pk_valid
    {
        crate::p256::point_mul(&mut ss_proj, pk.0, pk.1);
        crate::p256::point_store(shared_secret, &mut ss_proj)
    };
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64 && is_pk_valid
}

#[inline] fn qinv(res: &mut [u64], r: &mut [u64])
{
    let mut tmp: [u64; 28] = [0u64; 28usize];
    let x6: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let x_11: (&mut [u64], &mut [u64]) = x6.1.split_at_mut(4usize);
    let x_101: (&mut [u64], &mut [u64]) = x_11.1.split_at_mut(4usize);
    let x_111: (&mut [u64], &mut [u64]) = x_101.1.split_at_mut(4usize);
    let x_1111: (&mut [u64], &mut [u64]) = x_111.1.split_at_mut(4usize);
    let x_10101: (&mut [u64], &mut [u64]) = x_1111.1.split_at_mut(4usize);
    let x_101111: (&mut [u64], &mut [u64]) = x_10101.1.split_at_mut(4usize);
    (x_11.0[0usize..4usize]).copy_from_slice(&r[0usize..4usize]);
    {
        let mut x_copy: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
        crate::p256::qsqr(x_11.0, &mut x_copy)
    };
    crate::p256::qmul(x_101.0, x_11.0, r);
    crate::p256::qmul(x_111.0, x_11.0, x_101.0);
    crate::p256::qmul(x_1111.0, x_11.0, x_111.0);
    (x_11.0[0usize..4usize]).copy_from_slice(&x_111.0[0usize..4usize]);
    {
        let mut x_copy: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
        crate::p256::qsqr(x_11.0, &mut x_copy)
    };
    crate::p256::qmul(x_10101.0, x_111.0, x_11.0);
    {
        let mut x_copy: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
        crate::p256::qsqr(x_11.0, &mut x_copy)
    };
    crate::p256::qmul(x_101111.0, x_11.0, r);
    (x_11.0[0usize..4usize]).copy_from_slice(&x_101111.0[0usize..4usize]);
    {
        let mut x_copy: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
        crate::p256::qsqr(x_11.0, &mut x_copy)
    };
    crate::p256::qmul(x_101111.1, x_111.0, x_11.0);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
    crate::p256::qmul(x_11.0, x_101111.0, &mut y_copy);
    let mut tmp1: [u64; 4] = [0u64; 4usize];
    krml::unroll_for!(
        2,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
            crate::p256::qsqr(x_11.0, &mut x_copy)
        }
    );
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
    crate::p256::qmul(x_11.0, &mut x_copy, x_101.0);
    ((&mut tmp1)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
    krml::unroll_for!(
        8,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy0: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy0)
        }
    );
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy0, x_11.0);
    (x_11.0[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    krml::unroll_for!(
        16,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy1: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
            crate::p256::qsqr(x_11.0, &mut x_copy1)
        }
    );
    let mut x_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy1)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
    crate::p256::qmul(x_11.0, &mut x_copy1, &mut tmp1);
    ((&mut tmp1)[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize]);
    for _i in 0u32..64u32
    {
        let mut x_copy2: [u64; 4] = [0u64; 4usize];
        ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
        crate::p256::qsqr(&mut tmp1, &mut x_copy2)
    };
    let mut x_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy2)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy2, x_11.0);
    krml::unroll_for!(
        32,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy3: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy3)
        }
    );
    let mut x_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy3)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy3, x_11.0);
    krml::unroll_for!(
        6,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy4: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy4)
        }
    );
    let mut x_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy4)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy4, x_101111.1);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy5: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy5)
        }
    );
    let mut x_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy5)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy5, x_1111.0);
    krml::unroll_for!(
        4,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy6: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy6)
        }
    );
    let mut x_copy6: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy6)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy6, x_101.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy7: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy7)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy7)
        }
    );
    let mut x_copy7: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy7)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy7, x_10101.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy8: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy8)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy8)
        }
    );
    let mut x_copy8: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy8)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy8, x_101111.0);
    krml::unroll_for!(
        4,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy9: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy9)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy9)
        }
    );
    let mut x_copy9: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy9)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy9, x_111.0);
    krml::unroll_for!(
        3,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy10: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy10)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy10)
        }
    );
    let mut x_copy10: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy10)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy10, x_111.0);
    krml::unroll_for!(
        3,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy11: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy11)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy11)
        }
    );
    let mut x_copy11: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy11)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy11, x_111.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy12: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy12)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy12)
        }
    );
    let mut x_copy12: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy12)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy12, x_1111.0);
    krml::unroll_for!(
        9,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy13: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy13)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy13)
        }
    );
    let mut x_copy13: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy13)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy13, x_101111.1);
    krml::unroll_for!(
        6,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy14: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy14)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy14)
        }
    );
    let mut x_copy14: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy14)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy14, x_10101.0);
    krml::unroll_for!(
        2,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy15: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy15)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy15)
        }
    );
    let mut x_copy15: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy15)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy15, r);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy16: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy16)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy16)
        }
    );
    let mut x_copy16: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy16)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy16, r);
    krml::unroll_for!(
        6,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy17: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy17)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy17)
        }
    );
    let mut x_copy17: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy17)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy17, x_10101.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy18: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy18)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy18)
        }
    );
    let mut x_copy18: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy18)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy18, x_1111.0);
    krml::unroll_for!(
        4,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy19: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy19)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy19)
        }
    );
    let mut x_copy19: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy19)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy19, x_1111.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy20: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy20)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy20)
        }
    );
    let mut x_copy20: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy20)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy20, x_1111.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy21: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy21)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy21)
        }
    );
    let mut x_copy21: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy21)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy21, x_111.0);
    krml::unroll_for!(
        3,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy22: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy22)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy22)
        }
    );
    let mut x_copy22: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy22)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy22, x_101.0);
    krml::unroll_for!(
        10,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy23: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy23)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy23)
        }
    );
    let mut x_copy23: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy23)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy23, x_101111.1);
    krml::unroll_for!(
        2,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy24: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy24)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy24)
        }
    );
    let mut x_copy24: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy24)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy24, x_101.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy25: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy25)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy25)
        }
    );
    let mut x_copy25: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy25)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy25, x_101.0);
    krml::unroll_for!(
        5,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy26: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy26)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy26)
        }
    );
    let mut x_copy26: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy26)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy26, x_101.0);
    krml::unroll_for!(
        3,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy27: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy27)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy27)
        }
    );
    let mut x_copy27: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy27)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy27, r);
    krml::unroll_for!(
        7,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy28: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy28)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy28)
        }
    );
    let mut x_copy28: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy28)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy28, x_101111.0);
    krml::unroll_for!(
        6,
        "_i",
        0u32,
        1u32,
        {
            let mut x_copy29: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy29)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
            crate::p256::qsqr(&mut tmp1, &mut x_copy29)
        }
    );
    let mut x_copy29: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy29)[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    crate::p256::qmul(&mut tmp1, &mut x_copy29, x_10101.0);
    (x_11.0[0usize..4usize]).copy_from_slice(&(&mut tmp1)[0usize..4usize]);
    (res[0usize..4usize]).copy_from_slice(&x_11.0[0usize..4usize])
}

#[inline] fn qmul_mont(sinv: &mut [u64], b: &mut [u64], res: &mut [u64])
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    crate::p256::from_qmont(&mut tmp, b);
    crate::p256::qmul(res, sinv, &mut tmp)
}

#[inline] fn ecdsa_verify_msg_as_qelem(
    m_q: &mut [u64],
    public_key: &mut [u8],
    signature_r: &mut [u8],
    signature_s: &mut [u8]
) ->
    bool
{
    let mut tmp: [u64; 28] = [0u64; 28usize];
    let pk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let r_q: (&mut [u64], &mut [u64]) = pk.1.split_at_mut(12usize);
    let s_q: (&mut [u64], &mut [u64]) = r_q.1.split_at_mut(4usize);
    let u1: (&mut [u64], &mut [u64]) = s_q.1.split_at_mut(4usize);
    let u2: (&mut [u64], &mut [u64]) = u1.1.split_at_mut(4usize);
    let is_pk_valid: bool = crate::p256::load_point_vartime(r_q.0, public_key);
    crate::p256::bn_from_bytes_be4(s_q.0, signature_r);
    crate::p256::bn_from_bytes_be4(u1.0, signature_s);
    let is_r_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(s_q.0);
    let is_s_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(u1.0);
    let is_rs_valid: bool =
        is_r_valid == 0xFFFFFFFFFFFFFFFFu64 && is_s_valid == 0xFFFFFFFFFFFFFFFFu64;
    if ! (is_pk_valid && is_rs_valid)
    { false }
    else
    {
        let mut sinv: [u64; 4] = [0u64; 4usize];
        crate::p256::qinv(&mut sinv, u1.0);
        crate::p256::qmul_mont(&mut sinv, m_q, u2.0);
        crate::p256::qmul_mont(&mut sinv, s_q.0, u2.1);
        let mut res: [u64; 12] = [0u64; 12usize];
        crate::p256::point_mul_double_g(&mut res, u2.0, u2.1, r_q.0);
        if crate::p256::is_point_at_inf_vartime(&mut res)
        { false }
        else
        {
            let mut x: [u64; 4] = [0u64; 4usize];
            crate::p256::to_aff_point_x(&mut x, &mut res);
            let mut x_copy: [u64; 4] = [0u64; 4usize];
            ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut x)[0usize..4usize]);
            crate::p256::qmod_short(&mut x, &mut x_copy);
            let res1: bool = crate::p256::bn_is_eq_vartime4(&mut x, s_q.0);
            res1
        }
    }
}

#[inline] fn ecdsa_sign_msg_as_qelem(
    signature: &mut [u8],
    m_q: &mut [u64],
    private_key: &mut [u8],
    nonce: &mut [u8]
) ->
    bool
{
    let mut rsdk_q: [u64; 16] = [0u64; 16usize];
    let r_q: (&mut [u64], &mut [u64]) = rsdk_q.split_at_mut(0usize);
    let s_q: (&mut [u64], &mut [u64]) = r_q.1.split_at_mut(4usize);
    let d_a: (&mut [u64], &mut [u64]) = s_q.1.split_at_mut(4usize);
    let k_q: (&mut [u64], &mut [u64]) = d_a.1.split_at_mut(4usize);
    crate::p256::bn_from_bytes_be4(k_q.0, private_key);
    let is_b_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(k_q.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = (&mut oneq)[i as usize];
            let x: u64 = uu____0 ^ is_b_valid & (k_q.0[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = k_q.0.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_sk_valid: u64 = is_b_valid;
    crate::p256::bn_from_bytes_be4(k_q.1, nonce);
    let is_b_valid0: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(k_q.1);
    let mut oneq0: [u64; 4] = [0u64; 4usize];
    (&mut oneq0)[0usize] = 1u64;
    (&mut oneq0)[1usize] = 0u64;
    (&mut oneq0)[2usize] = 0u64;
    (&mut oneq0)[3usize] = 0u64;
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____1: u64 = (&mut oneq0)[i as usize];
            let x: u64 = uu____1 ^ is_b_valid0 & (k_q.1[i as usize] ^ uu____1);
            let os: (&mut [u64], &mut [u64]) = k_q.1.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_nonce_valid: u64 = is_b_valid0;
    let are_sk_nonce_valid: u64 = is_sk_valid & is_nonce_valid;
    let mut p: [u64; 12] = [0u64; 12usize];
    crate::p256::point_mul_g(&mut p, k_q.1);
    crate::p256::to_aff_point_x(s_q.0, &mut p);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&s_q.0[0usize..4usize]);
    crate::p256::qmod_short(s_q.0, &mut x_copy);
    let mut kinv: [u64; 4] = [0u64; 4usize];
    crate::p256::qinv(&mut kinv, k_q.1);
    crate::p256::qmul(d_a.0, s_q.0, k_q.0);
    let mut x_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy0)[0usize..4usize]).copy_from_slice(&m_q[0usize..4usize]);
    crate::p256::from_qmont(m_q, &mut x_copy0);
    let mut y_copy: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy)[0usize..4usize]).copy_from_slice(&d_a.0[0usize..4usize]);
    crate::p256::qadd(d_a.0, m_q, &mut y_copy);
    let mut y_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut y_copy0)[0usize..4usize]).copy_from_slice(&d_a.0[0usize..4usize]);
    crate::p256::qmul(d_a.0, &mut kinv, &mut y_copy0);
    crate::p256::bn2_to_bytes_be4(signature, s_q.0, d_a.0);
    let is_r_zero: u64 = crate::p256::bn_is_zero_mask4(s_q.0);
    let is_s_zero: u64 = crate::p256::bn_is_zero_mask4(d_a.0);
    let m: u64 = are_sk_nonce_valid & (! is_r_zero & ! is_s_zero);
    let res: bool = m == 0xFFFFFFFFFFFFFFFFu64;
    res
}

/**
Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
pub fn
ecdsa_sign_p256_sha2(
    signature: &mut [u8],
    msg_len: u32,
    msg: &mut [u8],
    private_key: &mut [u8],
    nonce: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 32] = [0u8; 32usize];
    crate::hash_sha2::hash_256(&mut mHash, msg, msg_len);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool = crate::p256::ecdsa_sign_msg_as_qelem(signature, &mut m_q, private_key, nonce);
    res
}

/**
Create an ECDSA signature using SHA2-384.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
pub fn
ecdsa_sign_p256_sha384(
    signature: &mut [u8],
    msg_len: u32,
    msg: &mut [u8],
    private_key: &mut [u8],
    nonce: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 48] = [0u8; 48usize];
    crate::hash_sha2::hash_384(&mut mHash, msg, msg_len);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool = crate::p256::ecdsa_sign_msg_as_qelem(signature, &mut m_q, private_key, nonce);
    res
}

/**
Create an ECDSA signature using SHA2-512.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
pub fn
ecdsa_sign_p256_sha512(
    signature: &mut [u8],
    msg_len: u32,
    msg: &mut [u8],
    private_key: &mut [u8],
    nonce: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 64] = [0u8; 64usize];
    crate::hash_sha2::hash_512(&mut mHash, msg, msg_len);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool = crate::p256::ecdsa_sign_msg_as_qelem(signature, &mut m_q, private_key, nonce);
    res
}

/**
Create an ECDSA signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-sign combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
  smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
  reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
  need to perform the left-padding themselves.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
pub fn
ecdsa_sign_p256_without_hash(
    signature: &mut [u8],
    msg_len: u32,
    msg: &mut [u8],
    private_key: &mut [u8],
    nonce: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 32] = [0u8; 32usize];
    ((&mut mHash)[0usize..32usize]).copy_from_slice(&(&mut msg[0usize..])[0usize..32usize]);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool = crate::p256::ecdsa_sign_msg_as_qelem(signature, &mut m_q, private_key, nonce);
    res
}

/**
Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
pub fn
ecdsa_verif_p256_sha2(
    msg_len: u32,
    msg: &mut [u8],
    public_key: &mut [u8],
    signature_r: &mut [u8],
    signature_s: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 32] = [0u8; 32usize];
    crate::hash_sha2::hash_256(&mut mHash, msg, msg_len);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool =
        crate::p256::ecdsa_verify_msg_as_qelem(&mut m_q, public_key, signature_r, signature_s);
    res
}

/**
Verify an ECDSA signature using SHA2-384.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
pub fn
ecdsa_verif_p256_sha384(
    msg_len: u32,
    msg: &mut [u8],
    public_key: &mut [u8],
    signature_r: &mut [u8],
    signature_s: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 48] = [0u8; 48usize];
    crate::hash_sha2::hash_384(&mut mHash, msg, msg_len);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool =
        crate::p256::ecdsa_verify_msg_as_qelem(&mut m_q, public_key, signature_r, signature_s);
    res
}

/**
Verify an ECDSA signature using SHA2-512.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
pub fn
ecdsa_verif_p256_sha512(
    msg_len: u32,
    msg: &mut [u8],
    public_key: &mut [u8],
    signature_r: &mut [u8],
    signature_s: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 64] = [0u8; 64usize];
    crate::hash_sha2::hash_512(&mut mHash, msg, msg_len);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool =
        crate::p256::ecdsa_verify_msg_as_qelem(&mut m_q, public_key, signature_r, signature_s);
    res
}

/**
Verify an ECDSA signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-verify combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
pub fn
ecdsa_verif_without_hash(
    msg_len: u32,
    msg: &mut [u8],
    public_key: &mut [u8],
    signature_r: &mut [u8],
    signature_s: &mut [u8]
) ->
    bool
{
    let mut m_q: [u64; 4] = [0u64; 4usize];
    let mut mHash: [u8; 32] = [0u8; 32usize];
    ((&mut mHash)[0usize..32usize]).copy_from_slice(&(&mut msg[0usize..])[0usize..32usize]);
    lowstar::ignore::ignore::<u32>(msg_len);
    let mHash32: (&mut [u8], &mut [u8]) = mHash.split_at_mut(0usize);
    crate::p256::bn_from_bytes_be4(&mut m_q, mHash32.1);
    let mut x_copy: [u64; 4] = [0u64; 4usize];
    ((&mut x_copy)[0usize..4usize]).copy_from_slice(&(&mut m_q)[0usize..4usize]);
    crate::p256::qmod_short(&mut m_q, &mut x_copy);
    let res: bool =
        crate::p256::ecdsa_verify_msg_as_qelem(&mut m_q, public_key, signature_r, signature_s);
    res
}

/**
Public key validation.

  The function returns `true` if a public key is valid and `false` otherwise.

  The argument `public_key` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The public key (x || y) is valid (with respect to SP 800-56A):
    • the public key is not the “point at infinity”, represented as O.
    • the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
pub fn
validate_public_key(public_key: &mut [u8]) ->
    bool
{
    let mut point_jac: [u64; 12] = [0u64; 12usize];
    let res: bool = crate::p256::load_point_vartime(&mut point_jac, public_key);
    res
}

/**
Private key validation.

  The function returns `true` if a private key is valid and `false` otherwise.

  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve
*/
pub fn
validate_private_key(private_key: &mut [u8]) ->
    bool
{
    let mut bn_sk: [u64; 4] = [0u64; 4usize];
    crate::p256::bn_from_bytes_be4(&mut bn_sk, private_key);
    let res: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(&mut bn_sk);
    res == 0xFFFFFFFFFFFFFFFFu64
}

/**
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is a valid point.
*/
pub fn
uncompressed_to_raw(pk: &mut [u8], pk_raw: &mut [u8]) ->
    bool
{
    let pk0: u8 = pk[0usize];
    if pk0 != 0x04u8
    { false }
    else
    {
        (pk_raw[0usize..64usize]).copy_from_slice(&(&mut pk[1usize..])[0usize..64usize]);
        true
    }
}

/**
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is a valid point.
*/
pub fn
compressed_to_raw(pk: &mut [u8], pk_raw: &mut [u8]) ->
    bool
{
    let mut xa: [u64; 4] = [0u64; 4usize];
    let mut ya: [u64; 4] = [0u64; 4usize];
    let b: bool = crate::p256::aff_point_decompress_vartime(&mut xa, &mut ya, pk);
    let pk_xb: (&mut [u8], &mut [u8]) = pk.split_at_mut(1usize);
    if b
    {
        (pk_raw[0usize..32usize]).copy_from_slice(&pk_xb.1[0usize..32usize]);
        crate::p256::bn_to_bytes_be4(&mut pk_raw[32usize..], &mut ya)
    };
    b
}

/**
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is a valid point.
*/
pub fn
raw_to_uncompressed(pk_raw: &mut [u8], pk: &mut [u8])
{
    pk[0usize] = 0x04u8;
    (pk[1usize..1usize + 64usize]).copy_from_slice(&pk_raw[0usize..64usize])
}

/**
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is a valid point.
*/
pub fn
raw_to_compressed(pk_raw: &mut [u8], pk: &mut [u8])
{
    let pk_x: (&mut [u8], &mut [u8]) = pk_raw.split_at_mut(0usize);
    let pk_y: (&mut [u8], &mut [u8]) = pk_x.1.split_at_mut(32usize);
    let mut bn_f: [u64; 4] = [0u64; 4usize];
    crate::p256::bn_from_bytes_be4(&mut bn_f, pk_y.1);
    let is_odd_f: u64 = (&mut bn_f)[0usize] & 1u64;
    pk[0usize] = (is_odd_f as u8).wrapping_add(0x02u8);
    (pk[1usize..1usize + 32usize]).copy_from_slice(&pk_y.0[0usize..32usize])
}

/**
Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve.
*/
pub fn
dh_initiator(public_key: &mut [u8], private_key: &mut [u8]) ->
    bool
{ crate::p256::ecp256dh_i(public_key, private_key) }

/**
Execute the diffie-hellmann key exchange.

  The function returns `true` for successful creation of an ECDH shared secret and
  `false` otherwise.

  The outparam `shared_secret` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `their_pubkey` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `their_pubkey` are valid.
*/
pub fn
dh_responder(shared_secret: &mut [u8], their_pubkey: &mut [u8], private_key: &mut [u8]) ->
    bool
{ crate::p256::ecp256dh_r(shared_secret, their_pubkey, private_key) }
