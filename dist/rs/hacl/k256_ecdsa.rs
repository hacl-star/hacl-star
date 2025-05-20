#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn bn_add_sa(aLen: u32, bLen: u32, b: &[u64], res: &mut [u64]) -> u64
{
    let res0: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let mut c: [u64; 1] = [0u64; 1usize];
    for i in 0u32..bLen.wrapping_div(4u32)
    {
        let t1: u64 = res0.1[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = (res0.1).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t1, t2, res_i.1);
        let t10: u64 = res0.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) =
            (res0.1).split_at_mut(4u32.wrapping_mul(i) as usize + 1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res0.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) =
            (res0.1).split_at_mut(4u32.wrapping_mul(i) as usize + 2usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res0.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) =
            (res0.1).split_at_mut(4u32.wrapping_mul(i) as usize + 3usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t12, t22, res_i2.1)
    };
    for i in bLen.wrapping_div(4u32).wrapping_mul(4u32)..bLen
    {
        let t1: u64 = res0.1[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (res0.1).split_at_mut(i as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t1, t2, res_i.1)
    };
    let c0: u64 = (&c)[0usize];
    if bLen < aLen
    {
        let res1: (&mut [u64], &mut [u64]) = (res0.1).split_at_mut(bLen as usize);
        let mut c1: [u64; 1] = [c0; 1usize];
        for i in 0u32..aLen.wrapping_sub(bLen).wrapping_div(4u32)
        {
            let t1: u64 = res1.1[4u32.wrapping_mul(i) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                (res1.1).split_at_mut(4u32.wrapping_mul(i) as usize);
            (&mut c1)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t1, 0u64, res_i.1);
            let t10: u64 = res1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) =
                (res1.1).split_at_mut(4u32.wrapping_mul(i) as usize + 1usize);
            (&mut c1)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t10, 0u64, res_i0.1);
            let t11: u64 = res1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) =
                (res1.1).split_at_mut(4u32.wrapping_mul(i) as usize + 2usize);
            (&mut c1)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t11, 0u64, res_i1.1);
            let t12: u64 = res1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) =
                (res1.1).split_at_mut(4u32.wrapping_mul(i) as usize + 3usize);
            (&mut c1)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t12, 0u64, res_i2.1)
        };
        for
        i
        in
        aLen.wrapping_sub(bLen).wrapping_div(4u32).wrapping_mul(4u32)..aLen.wrapping_sub(bLen)
        {
            let t1: u64 = res1.1[i as usize];
            let res_i: (&mut [u64], &mut [u64]) = (res1.1).split_at_mut(i as usize);
            (&mut c1)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t1, 0u64, res_i.1)
        };
        let c10: u64 = (&c1)[0usize];
        c10
    }
    else
    { c0 }
}

fn add4(a: &[u64], b: &[u64], res: &mut [u64]) -> u64
{
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = a[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = b[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t12, t22, res_i2.1)
    };
    (&c)[0usize]
}

fn add_mod4(n: &[u64], a: &[u64], b: &[u64], res: &mut [u64])
{
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = a[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = b[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t12, t22, res_i2.1)
    };
    let c0: u64 = (&c)[0usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = res[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = n[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = tmp.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c1)[0usize] = lib::inttypes_intrinsics::sub_borrow_u64((&c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&c1)[0usize], t12, t22, res_i2.1)
    };
    let c10: u64 = (&c1)[0usize];
    let c2: u64 = c0.wrapping_sub(c10);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = c2 & res[i as usize] | ! c2 & (&tmp)[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

fn sub_mod4(n: &[u64], a: &[u64], b: &[u64], res: &mut [u64])
{
    let mut c: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = a[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = b[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::sub_borrow_u64((&c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u64((&c)[0usize], t12, t22, res_i2.1)
    };
    let c0: u64 = (&c)[0usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    {
        let t1: u64 = res[4u32.wrapping_mul(0u32) as usize];
        let t2: u64 = n[4u32.wrapping_mul(0u32) as usize];
        let res_i: (&mut [u64], &mut [u64]) = tmp.split_at_mut(4u32.wrapping_mul(0u32) as usize);
        (&mut c1)[0usize] = lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u64((&c1)[0usize], t12, t22, res_i2.1)
    };
    let c10: u64 = (&c1)[0usize];
    lowstar::ignore::ignore::<u64>(c10);
    let c2: u64 = 0u64.wrapping_sub(c0);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = c2 & (&tmp)[i as usize] | ! c2 & res[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

fn mul4(a: &[u64], b: &[u64], res: &mut [u64])
{
    (res[0usize..8usize]).copy_from_slice(&[0u64; 8usize]);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let bj: u64 = b[i as usize];
            let res_j: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            {
                let a_i: u64 = a[4u32.wrapping_mul(0u32) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    (res_j.1).split_at_mut(4u32.wrapping_mul(0u32) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, bj, (&c)[0usize], res_i.1);
                let a_i0: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, bj, (&c)[0usize], res_i0.1);
                let a_i1: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, bj, (&c)[0usize], res_i1.1);
                let a_i2: u64 = a[4u32.wrapping_mul(0u32).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, bj, (&c)[0usize], res_i2.1)
            };
            let r: u64 = (&c)[0usize];
            res[4u32.wrapping_add(i) as usize] = r
        }
    )
}

fn sqr4(a: &[u64], res: &mut [u64])
{
    (res[0usize..8usize]).copy_from_slice(&[0u64; 8usize]);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let a_j: u64 = a[i as usize];
            let ab: (&[u64], &[u64]) = a.split_at(0usize);
            let res_j: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            for i0 in 0u32..i.wrapping_div(4u32)
            {
                let a_i: u64 = ab.1[4u32.wrapping_mul(i0) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    (res_j.1).split_at_mut(4u32.wrapping_mul(i0) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, a_j, (&c)[0usize], res_i.1);
                let a_i0: u64 = ab.1[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, a_j, (&c)[0usize], res_i0.1);
                let a_i1: u64 = ab.1[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, a_j, (&c)[0usize], res_i1.1);
                let a_i2: u64 = ab.1[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, a_j, (&c)[0usize], res_i2.1)
            };
            for i0 in i.wrapping_div(4u32).wrapping_mul(4u32)..i
            {
                let a_i: u64 = ab.1[i0 as usize];
                let res_i: (&mut [u64], &mut [u64]) = (res_j.1).split_at_mut(i0 as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, a_j, (&c)[0usize], res_i.1)
            };
            let r: u64 = (&c)[0usize];
            res[i.wrapping_add(i) as usize] = r
        }
    );
    let mut a_copy: [u64; 8] = [0u64; 8usize];
    let mut b_copy: [u64; 8] = [0u64; 8usize];
    ((&mut a_copy)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
    ((&mut b_copy)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
    let r: u64 = bignum::bignum_base::bn_add_eq_len_u64(8u32, &a_copy, &b_copy, res);
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
                fstar::uint128::mul_wide(a[i as usize], a[i as usize]);
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
    ((&mut b_copy0)[0usize..8usize]).copy_from_slice(&(&tmp)[0usize..8usize]);
    let r0: u64 = bignum::bignum_base::bn_add_eq_len_u64(8u32, &a_copy0, &b_copy0, res);
    let c1: u64 = r0;
    lowstar::ignore::ignore::<u64>(c1)
}

#[inline] fn is_qelem_zero(f: &[u64]) -> u64
{
    let bn_zero: [u64; 4] = [0u64; 4usize];
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = fstar::uint64::eq_mask(f[i as usize], (&bn_zero)[i as usize]);
            (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
        }
    );
    let mask1: u64 = (&mask)[0usize];
    let res: u64 = mask1;
    res
}

#[inline] fn is_qelem_zero_vartime(f: &[u64]) -> bool
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    f0 == 0u64 && f1 == 0u64 && f2 == 0u64 && f3 == 0u64
}

#[inline] fn load_qelem_check(f: &mut [u64], b: &[u8]) -> u64
{
    let mut n: [u64; 4] = [0u64; 4usize];
    (&mut n)[0usize] = 0xbfd25e8cd0364141u64;
    (&mut n)[1usize] = 0xbaaedce6af48a03bu64;
    (&mut n)[2usize] = 0xfffffffffffffffeu64;
    (&mut n)[3usize] = 0xffffffffffffffffu64;
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let u: u64 =
                lowstar::endianness::load64_be(
                    &b[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
                );
            let x: u64 = u;
            let os: (&mut [u64], &mut [u64]) = f.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_zero: u64 = crate::k256_ecdsa::is_qelem_zero(f);
    let mut acc: [u64; 1] = [0u64; 1usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let beq: u64 = fstar::uint64::eq_mask(f[i as usize], (&n)[i as usize]);
            let blt: u64 = ! fstar::uint64::gte_mask(f[i as usize], (&n)[i as usize]);
            (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & blt
        }
    );
    let is_lt_q: u64 = (&acc)[0usize];
    ! is_zero & is_lt_q
}

#[inline] fn load_qelem_vartime(f: &mut [u64], b: &[u8]) -> bool
{
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let u: u64 =
                lowstar::endianness::load64_be(
                    &b[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
                );
            let x: u64 = u;
            let os: (&mut [u64], &mut [u64]) = f.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_zero: bool = crate::k256_ecdsa::is_qelem_zero_vartime(f);
    let a0: u64 = f[0usize];
    let a1: u64 = f[1usize];
    let a2: u64 = f[2usize];
    let a3: u64 = f[3usize];
    let is_lt_q_b: bool =
        if a3 < 0xffffffffffffffffu64 || a2 < 0xfffffffffffffffeu64
        { true }
        else if a2 > 0xfffffffffffffffeu64
        { false }
        else if a1 < 0xbaaedce6af48a03bu64
        { true }
        else if a1 > 0xbaaedce6af48a03bu64 { false } else { a0 < 0xbfd25e8cd0364141u64 };
    ! is_zero && is_lt_q_b
}

#[inline] fn modq_short(out: &mut [u64], a: &[u64])
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    (&mut tmp)[0usize] = 0x402da1732fc9bebfu64;
    (&mut tmp)[1usize] = 0x4551231950b75fc4u64;
    (&mut tmp)[2usize] = 0x1u64;
    (&mut tmp)[3usize] = 0x0u64;
    let c: u64 = crate::k256_ecdsa::add4(a, &tmp, out);
    let mask: u64 = 0u64.wrapping_sub(c);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = mask & out[i as usize] | ! mask & a[i as usize];
            let os: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn load_qelem_modq(f: &mut [u64], b: &[u8])
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let u: u64 =
                lowstar::endianness::load64_be(
                    &b[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
                );
            let x: u64 = u;
            let os: (&mut [u64], &mut [u64]) = f.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    ((&mut tmp)[0usize..4usize]).copy_from_slice(&f[0usize..4usize]);
    crate::k256_ecdsa::modq_short(f, &tmp)
}

#[inline] fn store_qelem(b: &mut [u8], f: &[u64])
{
    let tmp: [u8; 32] = [0u8; 32usize];
    lowstar::ignore::ignore::<&[u8]>(&tmp);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_be(
            &mut b[i.wrapping_mul(8u32) as usize..],
            f[4u32.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    )
}

#[inline] fn qadd(out: &mut [u64], f1: &[u64], f2: &[u64])
{
    let mut n: [u64; 4] = [0u64; 4usize];
    (&mut n)[0usize] = 0xbfd25e8cd0364141u64;
    (&mut n)[1usize] = 0xbaaedce6af48a03bu64;
    (&mut n)[2usize] = 0xfffffffffffffffeu64;
    (&mut n)[3usize] = 0xffffffffffffffffu64;
    crate::k256_ecdsa::add_mod4(&n, f1, f2, out)
}

#[inline] fn mul_pow2_256_minus_q_add(
    len: u32,
    resLen: u32,
    t01: &[u64],
    a: &[u64],
    e: &[u64],
    res: &mut [u64]
) ->
    u64
{
    let mut tmp: Box<[u64]> = vec![0u64; len.wrapping_add(2u32) as usize].into_boxed_slice();
    ((&mut tmp)[0usize..len.wrapping_add(2u32) as usize]).copy_from_slice(
        &vec![0u64; len.wrapping_add(2u32) as usize].into_boxed_slice()
    );
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: u64 = t01[i as usize];
            let res_j: (&mut [u64], &mut [u64]) = tmp.split_at_mut(i as usize);
            let mut c: [u64; 1] = [0u64; 1usize];
            for i0 in 0u32..len.wrapping_div(4u32)
            {
                let a_i: u64 = a[4u32.wrapping_mul(i0) as usize];
                let res_i: (&mut [u64], &mut [u64]) =
                    (res_j.1).split_at_mut(4u32.wrapping_mul(i0) as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, bj, (&c)[0usize], res_i.1);
                let a_i0: u64 = a[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u64], &mut [u64]) = (res_i.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i0, bj, (&c)[0usize], res_i0.1);
                let a_i1: u64 = a[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u64], &mut [u64]) = (res_i0.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i1, bj, (&c)[0usize], res_i1.1);
                let a_i2: u64 = a[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u64], &mut [u64]) = (res_i1.1).split_at_mut(1usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i2, bj, (&c)[0usize], res_i2.1)
            };
            for i0 in len.wrapping_div(4u32).wrapping_mul(4u32)..len
            {
                let a_i: u64 = a[i0 as usize];
                let res_i: (&mut [u64], &mut [u64]) = (res_j.1).split_at_mut(i0 as usize);
                (&mut c)[0usize] =
                    bignum::bignum_base::mul_wide_add2_u64(a_i, bj, (&c)[0usize], res_i.1)
            };
            let r: u64 = (&c)[0usize];
            (&mut tmp)[len.wrapping_add(i) as usize] = r
        }
    );
    (res[2usize..2usize + len as usize]).copy_from_slice(&a[0usize..len as usize]);
    lowstar::ignore::ignore::<u64>(
        crate::k256_ecdsa::bn_add_sa(resLen, len.wrapping_add(2u32), &tmp, res)
    );
    let c: u64 = crate::k256_ecdsa::bn_add_sa(resLen, 4u32, e, res);
    c
}

#[inline] fn modq(out: &mut [u64], a: &[u64])
{
    let mut r: [u64; 4] = [0u64; 4usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    (&mut tmp)[0usize] = 0x402da1732fc9bebfu64;
    (&mut tmp)[1usize] = 0x4551231950b75fc4u64;
    (&mut tmp)[2usize] = 0x1u64;
    (&mut tmp)[3usize] = 0x0u64;
    let t01: (&[u64], &[u64]) = tmp.split_at(0usize);
    let mut m: [u64; 7] = [0u64; 7usize];
    let mut p: [u64; 5] = [0u64; 5usize];
    let a0: (&[u64], &[u64]) = a.split_at(0usize);
    let a1: (&[u64], &[u64]) = (a0.1).split_at(4usize);
    let c0: u64 =
        crate::k256_ecdsa::mul_pow2_256_minus_q_add(4u32, 7u32, t01.1, a1.1, a1.0, &mut m);
    lowstar::ignore::ignore::<u64>(c0);
    let m0: (&[u64], &[u64]) = m.split_at(0usize);
    let m1: (&[u64], &[u64]) = (m0.1).split_at(4usize);
    let c1: u64 =
        crate::k256_ecdsa::mul_pow2_256_minus_q_add(3u32, 5u32, t01.1, m1.1, m1.0, &mut p);
    lowstar::ignore::ignore::<u64>(c1);
    let p0: (&[u64], &[u64]) = p.split_at(0usize);
    let p1: (&[u64], &[u64]) = (p0.1).split_at(4usize);
    let c2: u64 =
        crate::k256_ecdsa::mul_pow2_256_minus_q_add(1u32, 4u32, t01.1, p1.1, p1.0, &mut r);
    let c00: u64 = c2;
    let c10: u64 = crate::k256_ecdsa::add4(&r, &tmp, out);
    let mask: u64 = 0u64.wrapping_sub(c00.wrapping_add(c10));
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = mask & out[i as usize] | ! mask & (&r)[i as usize];
            let os: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn qmul(out: &mut [u64], f1: &[u64], f2: &[u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::k256_ecdsa::mul4(f1, f2, &mut tmp);
    crate::k256_ecdsa::modq(out, &tmp)
}

#[inline] fn qsqr(out: &mut [u64], f: &[u64])
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::k256_ecdsa::sqr4(f, &mut tmp);
    crate::k256_ecdsa::modq(out, &tmp)
}

#[inline] fn qnegate_conditional_vartime(f: &mut [u64], is_negate: bool)
{
    let mut n: [u64; 4] = [0u64; 4usize];
    (&mut n)[0usize] = 0xbfd25e8cd0364141u64;
    (&mut n)[1usize] = 0xbaaedce6af48a03bu64;
    (&mut n)[2usize] = 0xfffffffffffffffeu64;
    (&mut n)[3usize] = 0xffffffffffffffffu64;
    let zero: [u64; 4] = [0u64; 4usize];
    if is_negate
    {
        let mut b_copy: [u64; 4] = [0u64; 4usize];
        ((&mut b_copy)[0usize..4usize]).copy_from_slice(&f[0usize..4usize]);
        crate::k256_ecdsa::sub_mod4(&n, &zero, &b_copy, f)
    }
}

#[inline] fn is_qelem_le_q_halved_vartime(f: &[u64]) -> bool
{
    let a0: u64 = f[0usize];
    let a1: u64 = f[1usize];
    let a2: u64 = f[2usize];
    let a3: u64 = f[3usize];
    if a3 < 0x7fffffffffffffffu64
    { true }
    else if a3 > 0x7fffffffffffffffu64
    { false }
    else if a2 < 0xffffffffffffffffu64 || a1 < 0x5d576e7357a4501du64
    { true }
    else if a1 > 0x5d576e7357a4501du64 { false } else { a0 <= 0xdfe92f46681b20a0u64 }
}

#[inline] fn qmul_shift_384(res: &mut [u64], a: &[u64], b: &[u64])
{
    let mut l: [u64; 8] = [0u64; 8usize];
    crate::k256_ecdsa::mul4(a, b, &mut l);
    let mut res_b_padded: [u64; 4] = [0u64; 4usize];
    ((&mut (&mut res_b_padded)[0usize..])[0usize..2usize]).copy_from_slice(
        &(&(&l)[6usize..])[0usize..2usize]
    );
    let c0: u64 =
        lib::inttypes_intrinsics::add_carry_u64(
            0u64,
            (&res_b_padded)[0usize],
            1u64,
            &mut res[0usize..]
        );
    let a1: (&[u64], &[u64]) = res_b_padded.split_at(1usize);
    let res1: (&mut [u64], &mut [u64]) = res.split_at_mut(1usize);
    let mut c: [u64; 1] = [c0; 1usize];
    krml::unroll_for!(
        3,
        "i",
        0u32,
        1u32,
        {
            let t1: u64 = a1.1[i as usize];
            let res_i: (&mut [u64], &mut [u64]) = (res1.1).split_at_mut(i as usize);
            (&mut c)[0usize] =
                lib::inttypes_intrinsics::add_carry_u64((&c)[0usize], t1, 0u64, res_i.1)
        }
    );
    let c1: u64 = (&c)[0usize];
    lowstar::ignore::ignore::<u64>(c1);
    let flag: u64 = ((&l)[5usize]).wrapping_shr(63u32);
    let mask: u64 = 0u64.wrapping_sub(flag);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = mask & res[i as usize] | ! mask & (&res_b_padded)[i as usize];
            let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn qsquare_times_in_place(out: &mut [u64], b: u32)
{
    for _i in 0u32..b
    {
        let mut f_copy: [u64; 4] = [0u64; 4usize];
        ((&mut f_copy)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
        crate::k256_ecdsa::qsqr(out, &f_copy)
    }
}

#[inline] fn qsquare_times(out: &mut [u64], a: &[u64], b: u32)
{
    (out[0usize..4usize]).copy_from_slice(&a[0usize..4usize]);
    for _i in 0u32..b
    {
        let mut f_copy: [u64; 4] = [0u64; 4usize];
        ((&mut f_copy)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
        crate::k256_ecdsa::qsqr(out, &f_copy)
    }
}

#[inline] fn qinv(out: &mut [u64], f: &[u64])
{
    let mut x_10: [u64; 4] = [0u64; 4usize];
    let mut x_11: [u64; 4] = [0u64; 4usize];
    let mut x_101: [u64; 4] = [0u64; 4usize];
    let mut x_111: [u64; 4] = [0u64; 4usize];
    let mut x_1001: [u64; 4] = [0u64; 4usize];
    let mut x_1011: [u64; 4] = [0u64; 4usize];
    let mut x_1101: [u64; 4] = [0u64; 4usize];
    crate::k256_ecdsa::qsquare_times(&mut x_10, f, 1u32);
    crate::k256_ecdsa::qmul(&mut x_11, &x_10, f);
    crate::k256_ecdsa::qmul(&mut x_101, &x_10, &x_11);
    crate::k256_ecdsa::qmul(&mut x_111, &x_10, &x_101);
    crate::k256_ecdsa::qmul(&mut x_1001, &x_10, &x_111);
    crate::k256_ecdsa::qmul(&mut x_1011, &x_10, &x_1001);
    crate::k256_ecdsa::qmul(&mut x_1101, &x_10, &x_1011);
    let mut x6: [u64; 4] = [0u64; 4usize];
    let mut x8: [u64; 4] = [0u64; 4usize];
    let mut x14: [u64; 4] = [0u64; 4usize];
    crate::k256_ecdsa::qsquare_times(&mut x6, &x_1101, 2u32);
    let mut f1_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy)[0usize..4usize]).copy_from_slice(&(&x6)[0usize..4usize]);
    crate::k256_ecdsa::qmul(&mut x6, &f1_copy, &x_1011);
    crate::k256_ecdsa::qsquare_times(&mut x8, &x6, 2u32);
    let mut f1_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy0)[0usize..4usize]).copy_from_slice(&(&x8)[0usize..4usize]);
    crate::k256_ecdsa::qmul(&mut x8, &f1_copy0, &x_11);
    crate::k256_ecdsa::qsquare_times(&mut x14, &x8, 6u32);
    let mut f1_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy1)[0usize..4usize]).copy_from_slice(&(&x14)[0usize..4usize]);
    crate::k256_ecdsa::qmul(&mut x14, &f1_copy1, &x6);
    let mut x56: [u64; 4] = [0u64; 4usize];
    crate::k256_ecdsa::qsquare_times(out, &x14, 14u32);
    let mut f1_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy2)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy2, &x14);
    crate::k256_ecdsa::qsquare_times(&mut x56, out, 28u32);
    let mut f1_copy3: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy3)[0usize..4usize]).copy_from_slice(&(&x56)[0usize..4usize]);
    crate::k256_ecdsa::qmul(&mut x56, &f1_copy3, out);
    crate::k256_ecdsa::qsquare_times(out, &x56, 56u32);
    let mut f1_copy4: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy4)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy4, &x56);
    crate::k256_ecdsa::qsquare_times_in_place(out, 14u32);
    let mut f1_copy5: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy5)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy5, &x14);
    crate::k256_ecdsa::qsquare_times_in_place(out, 3u32);
    let mut f1_copy6: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy6)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy6, &x_101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy7: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy7)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy7, &x_111);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy8: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy8)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy8, &x_101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 5u32);
    let mut f1_copy9: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy9)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy9, &x_1011);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy10: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy10)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy10, &x_1011);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy11: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy11)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy11, &x_111);
    crate::k256_ecdsa::qsquare_times_in_place(out, 5u32);
    let mut f1_copy12: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy12)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy12, &x_111);
    crate::k256_ecdsa::qsquare_times_in_place(out, 6u32);
    let mut f1_copy13: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy13)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy13, &x_1101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy14: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy14)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy14, &x_101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 3u32);
    let mut f1_copy15: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy15)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy15, &x_111);
    crate::k256_ecdsa::qsquare_times_in_place(out, 5u32);
    let mut f1_copy16: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy16)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy16, &x_1001);
    crate::k256_ecdsa::qsquare_times_in_place(out, 6u32);
    let mut f1_copy17: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy17)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy17, &x_101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 10u32);
    let mut f1_copy18: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy18)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy18, &x_111);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy19: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy19)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy19, &x_111);
    crate::k256_ecdsa::qsquare_times_in_place(out, 9u32);
    let mut f1_copy20: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy20)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy20, &x8);
    crate::k256_ecdsa::qsquare_times_in_place(out, 5u32);
    let mut f1_copy21: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy21)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy21, &x_1001);
    crate::k256_ecdsa::qsquare_times_in_place(out, 6u32);
    let mut f1_copy22: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy22)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy22, &x_1011);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy23: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy23)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy23, &x_1101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 5u32);
    let mut f1_copy24: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy24)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy24, &x_11);
    crate::k256_ecdsa::qsquare_times_in_place(out, 6u32);
    let mut f1_copy25: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy25)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy25, &x_1101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 10u32);
    let mut f1_copy26: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy26)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy26, &x_1101);
    crate::k256_ecdsa::qsquare_times_in_place(out, 4u32);
    let mut f1_copy27: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy27)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy27, &x_1001);
    crate::k256_ecdsa::qsquare_times_in_place(out, 6u32);
    let mut f1_copy28: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy28)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy28, f);
    crate::k256_ecdsa::qsquare_times_in_place(out, 8u32);
    let mut f1_copy29: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy29)[0usize..4usize]).copy_from_slice(&out[0usize..4usize]);
    crate::k256_ecdsa::qmul(out, &f1_copy29, &x6)
}

pub(crate) fn make_point_at_inf(p: &mut [u64])
{
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = (px.1).split_at_mut(5usize);
    let pz: (&mut [u64], &mut [u64]) = (py.1).split_at_mut(5usize);
    (py.0[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    (pz.0[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    pz.0[0usize] = 1u64;
    (pz.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize])
}

#[inline] fn to_aff_point(p_aff: &mut [u64], p: &[u64])
{
    let x: (&mut [u64], &mut [u64]) = p_aff.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = (x.1).split_at_mut(5usize);
    let x1: (&[u64], &[u64]) = p.split_at(0usize);
    let y1: (&[u64], &[u64]) = (x1.1).split_at(5usize);
    let z1: (&[u64], &[u64]) = (y1.1).split_at(5usize);
    let mut zinv: [u64; 5] = [0u64; 5usize];
    crate::bignum_k256::finv(&mut zinv, z1.1);
    crate::bignum_k256::fmul(y.0, y1.0, &zinv);
    crate::bignum_k256::fmul(y.1, z1.0, &zinv);
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&y.0[0usize..5usize]);
    crate::bignum_k256::fnormalize(y.0, &f_copy);
    let mut f_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy0)[0usize..5usize]).copy_from_slice(&y.1[0usize..5usize]);
    crate::bignum_k256::fnormalize(y.1, &f_copy0)
}

#[inline] fn to_aff_point_x(x: &mut [u64], p: &[u64])
{
    let x1: (&[u64], &[u64]) = p.split_at(0usize);
    let z1: (&[u64], &[u64]) = (x1.1).split_at(10usize);
    let mut zinv: [u64; 5] = [0u64; 5usize];
    crate::bignum_k256::finv(&mut zinv, z1.1);
    crate::bignum_k256::fmul(x, z1.0, &zinv);
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&x[0usize..5usize]);
    crate::bignum_k256::fnormalize(x, &f_copy)
}

#[inline] fn is_on_curve_vartime(p: &[u64]) -> bool
{
    let mut y2_exp: [u64; 5] = [0u64; 5usize];
    let x: (&[u64], &[u64]) = p.split_at(0usize);
    let y: (&[u64], &[u64]) = (x.1).split_at(5usize);
    let mut b: [u64; 5] = [0u64; 5usize];
    (&mut b)[0usize] = 0x7u64;
    (&mut b)[1usize] = 0u64;
    (&mut b)[2usize] = 0u64;
    (&mut b)[3usize] = 0u64;
    (&mut b)[4usize] = 0u64;
    crate::bignum_k256::fsqr(&mut y2_exp, y.0);
    let mut f1_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&(&y2_exp)[0usize..5usize]);
    crate::bignum_k256::fmul(&mut y2_exp, &f1_copy, y.0);
    let mut f1_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy0)[0usize..5usize]).copy_from_slice(&(&y2_exp)[0usize..5usize]);
    crate::bignum_k256::fadd(&mut y2_exp, &f1_copy0, &b);
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&(&y2_exp)[0usize..5usize]);
    crate::bignum_k256::fnormalize(&mut y2_exp, &f_copy);
    let mut y2_comp: [u64; 5] = [0u64; 5usize];
    crate::bignum_k256::fsqr(&mut y2_comp, y.1);
    let mut f_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy0)[0usize..5usize]).copy_from_slice(&(&y2_comp)[0usize..5usize]);
    crate::bignum_k256::fnormalize(&mut y2_comp, &f_copy0);
    let res: bool = crate::bignum_k256::is_felem_eq_vartime(&y2_exp, &y2_comp);
    let res0: bool = res;
    res0
}

#[inline] pub(crate) fn point_negate(out: &mut [u64], p: &[u64])
{
    let px: (&[u64], &[u64]) = p.split_at(0usize);
    let py: (&[u64], &[u64]) = (px.1).split_at(5usize);
    let pz: (&[u64], &[u64]) = (py.1).split_at(5usize);
    let ox: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let oy: (&mut [u64], &mut [u64]) = (ox.1).split_at_mut(5usize);
    let oz: (&mut [u64], &mut [u64]) = (oy.1).split_at_mut(5usize);
    oy.0[0usize] = py.0[0usize];
    oy.0[1usize] = py.0[1usize];
    oy.0[2usize] = py.0[2usize];
    oy.0[3usize] = py.0[3usize];
    oy.0[4usize] = py.0[4usize];
    oz.1[0usize] = pz.1[0usize];
    oz.1[1usize] = pz.1[1usize];
    oz.1[2usize] = pz.1[2usize];
    oz.1[3usize] = pz.1[3usize];
    oz.1[4usize] = pz.1[4usize];
    let a0: u64 = pz.0[0usize];
    let a1: u64 = pz.0[1usize];
    let a2: u64 = pz.0[2usize];
    let a3: u64 = pz.0[3usize];
    let a4: u64 = pz.0[4usize];
    let r0: u64 = 18014381329608892u64.wrapping_sub(a0);
    let r1: u64 = 18014398509481980u64.wrapping_sub(a1);
    let r2: u64 = 18014398509481980u64.wrapping_sub(a2);
    let r3: u64 = 18014398509481980u64.wrapping_sub(a3);
    let r4: u64 = 1125899906842620u64.wrapping_sub(a4);
    let f0: u64 = r0;
    let f1: u64 = r1;
    let f2: u64 = r2;
    let f3: u64 = r3;
    let f4: u64 = r4;
    oz.0[0usize] = f0;
    oz.0[1usize] = f1;
    oz.0[2usize] = f2;
    oz.0[3usize] = f3;
    oz.0[4usize] = f4;
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&oz.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(oz.0, &f_copy)
}

#[inline] fn point_negate_conditional_vartime(p: &mut [u64], is_negate: bool)
{
    if is_negate
    {
        let mut p_copy: [u64; 15] = [0u64; 15usize];
        ((&mut p_copy)[0usize..15usize]).copy_from_slice(&p[0usize..15usize]);
        crate::k256_ecdsa::point_negate(p, &p_copy)
    }
}

#[inline] fn aff_point_store(out: &mut [u8], p: &[u64])
{
    let px: (&[u64], &[u64]) = p.split_at(0usize);
    let py: (&[u64], &[u64]) = (px.1).split_at(5usize);
    crate::bignum_k256::store_felem(&mut out[0usize..], py.0);
    crate::bignum_k256::store_felem(&mut out[32usize..], py.1)
}

#[inline] pub(crate) fn point_store(out: &mut [u8], p: &[u64])
{
    let mut p_aff: [u64; 10] = [0u64; 10usize];
    crate::k256_ecdsa::to_aff_point(&mut p_aff, p);
    crate::k256_ecdsa::aff_point_store(out, &p_aff)
}

#[inline] pub(crate) fn aff_point_load_vartime(p: &mut [u64], b: &[u8]) -> bool
{
    let px: (&[u8], &[u8]) = b.split_at(0usize);
    let py: (&[u8], &[u8]) = (px.1).split_at(32usize);
    let bn_px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let bn_py: (&mut [u64], &mut [u64]) = (bn_px.1).split_at_mut(5usize);
    let is_x_valid: bool = crate::bignum_k256::load_felem_lt_prime_vartime(bn_py.0, py.0);
    let is_y_valid: bool = crate::bignum_k256::load_felem_lt_prime_vartime(bn_py.1, py.1);
    if is_x_valid && is_y_valid { crate::k256_ecdsa::is_on_curve_vartime(p) } else { false }
}

#[inline] fn load_point_vartime(p: &mut [u64], b: &[u8]) -> bool
{
    let mut p_aff: [u64; 10] = [0u64; 10usize];
    let res: bool = crate::k256_ecdsa::aff_point_load_vartime(&mut p_aff, b);
    if res
    {
        let x: (&[u64], &[u64]) = p_aff.split_at(0usize);
        let y: (&[u64], &[u64]) = (x.1).split_at(5usize);
        let x1: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
        let y1: (&mut [u64], &mut [u64]) = (x1.1).split_at_mut(5usize);
        let z1: (&mut [u64], &mut [u64]) = (y1.1).split_at_mut(5usize);
        (y1.0[0usize..5usize]).copy_from_slice(&y.0[0usize..5usize]);
        (z1.0[0usize..5usize]).copy_from_slice(&y.1[0usize..5usize]);
        (z1.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
        z1.1[0usize] = 1u64
    };
    res
}

#[inline] fn aff_point_decompress_vartime(x: &mut [u64], y: &mut [u64], s: &[u8]) -> bool
{
    let s0: u8 = s[0usize];
    let s01: u8 = s0;
    if ! (s01 == 0x02u8 || s01 == 0x03u8)
    { false }
    else
    {
        let xb: (&[u8], &[u8]) = s.split_at(1usize);
        let is_x_valid: bool = crate::bignum_k256::load_felem_lt_prime_vartime(x, xb.1);
        let is_y_odd: bool = s01 == 0x03u8;
        if ! is_x_valid
        { false }
        else
        {
            let mut y2: [u64; 5] = [0u64; 5usize];
            let mut b: [u64; 5] = [0u64; 5usize];
            (&mut b)[0usize] = 0x7u64;
            (&mut b)[1usize] = 0u64;
            (&mut b)[2usize] = 0u64;
            (&mut b)[3usize] = 0u64;
            (&mut b)[4usize] = 0u64;
            crate::bignum_k256::fsqr(&mut y2, x);
            let mut f1_copy: [u64; 5] = [0u64; 5usize];
            ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&(&y2)[0usize..5usize]);
            crate::bignum_k256::fmul(&mut y2, &f1_copy, x);
            let mut f1_copy0: [u64; 5] = [0u64; 5usize];
            ((&mut f1_copy0)[0usize..5usize]).copy_from_slice(&(&y2)[0usize..5usize]);
            crate::bignum_k256::fadd(&mut y2, &f1_copy0, &b);
            let mut f_copy: [u64; 5] = [0u64; 5usize];
            ((&mut f_copy)[0usize..5usize]).copy_from_slice(&(&y2)[0usize..5usize]);
            crate::bignum_k256::fnormalize(&mut y2, &f_copy);
            crate::bignum_k256::fsqrt(y, &y2);
            let mut f_copy0: [u64; 5] = [0u64; 5usize];
            ((&mut f_copy0)[0usize..5usize]).copy_from_slice(&y[0usize..5usize]);
            crate::bignum_k256::fnormalize(y, &f_copy0);
            let mut y2_comp: [u64; 5] = [0u64; 5usize];
            crate::bignum_k256::fsqr(&mut y2_comp, y);
            let mut f_copy1: [u64; 5] = [0u64; 5usize];
            ((&mut f_copy1)[0usize..5usize]).copy_from_slice(&(&y2_comp)[0usize..5usize]);
            crate::bignum_k256::fnormalize(&mut y2_comp, &f_copy1);
            let res: bool = crate::bignum_k256::is_felem_eq_vartime(&y2, &y2_comp);
            let is_y_valid: bool = res;
            let is_y_valid0: bool = is_y_valid;
            if ! is_y_valid0
            { false }
            else
            {
                let x0: u64 = y[0usize];
                let is_y_odd1: bool = x0 & 1u64 == 1u64;
                crate::bignum_k256::fnegate_conditional_vartime(y, is_y_odd1 != is_y_odd);
                true
            }
        }
    }
}

pub(crate) fn point_double(out: &mut [u64], p: &[u64])
{
    let mut tmp: [u64; 25] = [0u64; 25usize];
    let x1: (&[u64], &[u64]) = p.split_at(0usize);
    let y1: (&[u64], &[u64]) = (x1.1).split_at(5usize);
    let z1: (&[u64], &[u64]) = (y1.1).split_at(5usize);
    let x3: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = (x3.1).split_at_mut(5usize);
    let z3: (&mut [u64], &mut [u64]) = (y3.1).split_at_mut(5usize);
    let yy: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let zz: (&mut [u64], &mut [u64]) = (yy.1).split_at_mut(5usize);
    let bzz3: (&mut [u64], &mut [u64]) = (zz.1).split_at_mut(5usize);
    let bzz9: (&mut [u64], &mut [u64]) = (bzz3.1).split_at_mut(5usize);
    let tmp1: (&mut [u64], &mut [u64]) = (bzz9.1).split_at_mut(5usize);
    crate::bignum_k256::fsqr(zz.0, z1.0);
    crate::bignum_k256::fsqr(bzz3.0, z1.1);
    crate::bignum_k256::fmul_small_num(y3.0, y1.0, 2u64);
    let mut f1_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&y3.0[0usize..5usize]);
    crate::bignum_k256::fmul(y3.0, &f1_copy, z1.0);
    crate::bignum_k256::fmul(tmp1.1, zz.0, z1.0);
    crate::bignum_k256::fmul(z3.1, tmp1.1, z1.1);
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&z3.1[0usize..5usize]);
    crate::bignum_k256::fmul_small_num(z3.1, &f_copy, 8u64);
    let mut f_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy1)[0usize..5usize]).copy_from_slice(&z3.1[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(z3.1, &f_copy1);
    crate::bignum_k256::fmul_small_num(bzz9.0, bzz3.0, 21u64);
    let mut f_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy0)[0usize..5usize]).copy_from_slice(&bzz9.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(bzz9.0, &f_copy0);
    crate::bignum_k256::fmul_small_num(tmp1.0, bzz9.0, 3u64);
    let mut f2_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy)[0usize..5usize]).copy_from_slice(&tmp1.0[0usize..5usize]);
    crate::bignum_k256::fsub(tmp1.0, zz.0, &f2_copy, 6u64);
    crate::bignum_k256::fadd(tmp1.1, zz.0, bzz9.0);
    let mut f2_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy0)[0usize..5usize]).copy_from_slice(&tmp1.1[0usize..5usize]);
    crate::bignum_k256::fmul(tmp1.1, tmp1.0, &f2_copy0);
    crate::bignum_k256::fmul(z3.0, zz.0, bzz3.0);
    let mut f1_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy0)[0usize..5usize]).copy_from_slice(&y3.0[0usize..5usize]);
    crate::bignum_k256::fmul(y3.0, &f1_copy0, tmp1.0);
    let mut f_copy2: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy2)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fmul_small_num(z3.0, &f_copy2, 168u64);
    let mut f2_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy1)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fadd(z3.0, tmp1.1, &f2_copy1);
    let mut f_copy3: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy3)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(z3.0, &f_copy3)
}

pub(crate) fn point_add(out: &mut [u64], p: &[u64], q: &[u64])
{
    let mut tmp: [u64; 45] = [0u64; 45usize];
    let x1: (&[u64], &[u64]) = p.split_at(0usize);
    let y1: (&[u64], &[u64]) = (x1.1).split_at(5usize);
    let z1: (&[u64], &[u64]) = (y1.1).split_at(5usize);
    let x2: (&[u64], &[u64]) = q.split_at(0usize);
    let y2: (&[u64], &[u64]) = (x2.1).split_at(5usize);
    let z2: (&[u64], &[u64]) = (y2.1).split_at(5usize);
    let x3: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = (x3.1).split_at_mut(5usize);
    let z3: (&mut [u64], &mut [u64]) = (y3.1).split_at_mut(5usize);
    let xx: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let yy: (&mut [u64], &mut [u64]) = (xx.1).split_at_mut(5usize);
    let zz: (&mut [u64], &mut [u64]) = (yy.1).split_at_mut(5usize);
    let xy_pairs: (&mut [u64], &mut [u64]) = (zz.1).split_at_mut(5usize);
    let yz_pairs: (&mut [u64], &mut [u64]) = (xy_pairs.1).split_at_mut(5usize);
    let xz_pairs: (&mut [u64], &mut [u64]) = (yz_pairs.1).split_at_mut(5usize);
    let yy_m_bzz3: (&mut [u64], &mut [u64]) = (xz_pairs.1).split_at_mut(5usize);
    let yy_p_bzz3: (&mut [u64], &mut [u64]) = (yy_m_bzz3.1).split_at_mut(5usize);
    let tmp1: (&mut [u64], &mut [u64]) = (yy_p_bzz3.1).split_at_mut(5usize);
    crate::bignum_k256::fmul(yy.0, y1.0, y2.0);
    crate::bignum_k256::fmul(zz.0, z1.0, z2.0);
    crate::bignum_k256::fmul(xy_pairs.0, z1.1, z2.1);
    crate::bignum_k256::fadd(yz_pairs.0, y1.0, z1.0);
    crate::bignum_k256::fadd(tmp1.1, y2.0, z2.0);
    let mut f1_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&yz_pairs.0[0usize..5usize]);
    crate::bignum_k256::fmul(yz_pairs.0, &f1_copy, tmp1.1);
    crate::bignum_k256::fadd(tmp1.1, yy.0, zz.0);
    let mut f1_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy0)[0usize..5usize]).copy_from_slice(&yz_pairs.0[0usize..5usize]);
    crate::bignum_k256::fsub(yz_pairs.0, &f1_copy0, tmp1.1, 4u64);
    crate::bignum_k256::fadd(xz_pairs.0, z1.0, z1.1);
    crate::bignum_k256::fadd(tmp1.1, z2.0, z2.1);
    let mut f1_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy1)[0usize..5usize]).copy_from_slice(&xz_pairs.0[0usize..5usize]);
    crate::bignum_k256::fmul(xz_pairs.0, &f1_copy1, tmp1.1);
    crate::bignum_k256::fadd(tmp1.1, zz.0, xy_pairs.0);
    let mut f1_copy2: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy2)[0usize..5usize]).copy_from_slice(&xz_pairs.0[0usize..5usize]);
    crate::bignum_k256::fsub(xz_pairs.0, &f1_copy2, tmp1.1, 4u64);
    crate::bignum_k256::fadd(yy_m_bzz3.0, y1.0, z1.1);
    crate::bignum_k256::fadd(tmp1.1, y2.0, z2.1);
    let mut f1_copy3: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy3)[0usize..5usize]).copy_from_slice(&yy_m_bzz3.0[0usize..5usize]);
    crate::bignum_k256::fmul(yy_m_bzz3.0, &f1_copy3, tmp1.1);
    crate::bignum_k256::fadd(tmp1.1, yy.0, xy_pairs.0);
    let mut f1_copy4: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy4)[0usize..5usize]).copy_from_slice(&yy_m_bzz3.0[0usize..5usize]);
    crate::bignum_k256::fsub(yy_m_bzz3.0, &f1_copy4, tmp1.1, 4u64);
    crate::bignum_k256::fmul_small_num(tmp1.1, xy_pairs.0, 21u64);
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&tmp1.1[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(tmp1.1, &f_copy);
    crate::bignum_k256::fsub(yy_p_bzz3.0, zz.0, tmp1.1, 2u64);
    crate::bignum_k256::fadd(tmp1.0, zz.0, tmp1.1);
    crate::bignum_k256::fmul_small_num(y3.0, xz_pairs.0, 21u64);
    let mut f_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy0)[0usize..5usize]).copy_from_slice(&y3.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(y3.0, &f_copy0);
    crate::bignum_k256::fmul_small_num(z3.1, yy.0, 3u64);
    crate::bignum_k256::fmul_small_num(z3.0, z3.1, 21u64);
    let mut f_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy1)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(z3.0, &f_copy1);
    crate::bignum_k256::fmul(tmp1.1, yz_pairs.0, yy_p_bzz3.0);
    let mut f1_copy5: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy5)[0usize..5usize]).copy_from_slice(&y3.0[0usize..5usize]);
    crate::bignum_k256::fmul(y3.0, &f1_copy5, yy_m_bzz3.0);
    let mut f2_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy)[0usize..5usize]).copy_from_slice(&y3.0[0usize..5usize]);
    crate::bignum_k256::fsub(y3.0, tmp1.1, &f2_copy, 2u64);
    let mut f_copy2: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy2)[0usize..5usize]).copy_from_slice(&y3.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(y3.0, &f_copy2);
    crate::bignum_k256::fmul(tmp1.1, tmp1.0, yy_p_bzz3.0);
    let mut f1_copy6: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy6)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fmul(z3.0, &f1_copy6, yy_m_bzz3.0);
    let mut f2_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy0)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fadd(z3.0, tmp1.1, &f2_copy0);
    let mut f_copy3: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy3)[0usize..5usize]).copy_from_slice(&z3.0[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(z3.0, &f_copy3);
    crate::bignum_k256::fmul(tmp1.1, xz_pairs.0, tmp1.0);
    let mut f1_copy7: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy7)[0usize..5usize]).copy_from_slice(&z3.1[0usize..5usize]);
    crate::bignum_k256::fmul(z3.1, &f1_copy7, yz_pairs.0);
    let mut f2_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy1)[0usize..5usize]).copy_from_slice(&z3.1[0usize..5usize]);
    crate::bignum_k256::fadd(z3.1, tmp1.1, &f2_copy1);
    let mut f_copy4: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy4)[0usize..5usize]).copy_from_slice(&z3.1[0usize..5usize]);
    crate::bignum_k256::fnormalize_weak(z3.1, &f_copy4)
}

#[inline] fn scalar_split_lambda(r1: &mut [u64], r2: &mut [u64], k: &[u64])
{
    let mut tmp1: [u64; 4] = [0u64; 4usize];
    let mut tmp2: [u64; 4] = [0u64; 4usize];
    (&mut tmp1)[0usize] = 0xe893209a45dbb031u64;
    (&mut tmp1)[1usize] = 0x3daa8a1471e8ca7fu64;
    (&mut tmp1)[2usize] = 0xe86c90e49284eb15u64;
    (&mut tmp1)[3usize] = 0x3086d221a7d46bcdu64;
    (&mut tmp2)[0usize] = 0x1571b4ae8ac47f71u64;
    (&mut tmp2)[1usize] = 0x221208ac9df506c6u64;
    (&mut tmp2)[2usize] = 0x6f547fa90abfe4c4u64;
    (&mut tmp2)[3usize] = 0xe4437ed6010e8828u64;
    crate::k256_ecdsa::qmul_shift_384(r1, k, &tmp1);
    crate::k256_ecdsa::qmul_shift_384(r2, k, &tmp2);
    (&mut tmp1)[0usize] = 0x6f547fa90abfe4c3u64;
    (&mut tmp1)[1usize] = 0xe4437ed6010e8828u64;
    (&mut tmp1)[2usize] = 0x0u64;
    (&mut tmp1)[3usize] = 0x0u64;
    (&mut tmp2)[0usize] = 0xd765cda83db1562cu64;
    (&mut tmp2)[1usize] = 0x8a280ac50774346du64;
    (&mut tmp2)[2usize] = 0xfffffffffffffffeu64;
    (&mut tmp2)[3usize] = 0xffffffffffffffffu64;
    let mut f1_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy)[0usize..4usize]).copy_from_slice(&r1[0usize..4usize]);
    crate::k256_ecdsa::qmul(r1, &f1_copy, &tmp1);
    let mut f1_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy0)[0usize..4usize]).copy_from_slice(&r2[0usize..4usize]);
    crate::k256_ecdsa::qmul(r2, &f1_copy0, &tmp2);
    (&mut tmp1)[0usize] = 0xe0cfc810b51283cfu64;
    (&mut tmp1)[1usize] = 0xa880b9fc8ec739c2u64;
    (&mut tmp1)[2usize] = 0x5ad9e3fd77ed9ba4u64;
    (&mut tmp1)[3usize] = 0xac9c52b33fa3cf1fu64;
    let mut f2_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy)[0usize..4usize]).copy_from_slice(&r2[0usize..4usize]);
    crate::k256_ecdsa::qadd(r2, r1, &f2_copy);
    crate::k256_ecdsa::qmul(&mut tmp2, r2, &tmp1);
    crate::k256_ecdsa::qadd(r1, k, &tmp2)
}

#[inline] fn point_mul_lambda(res: &mut [u64], p: &[u64])
{
    let rx: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let ry: (&mut [u64], &mut [u64]) = (rx.1).split_at_mut(5usize);
    let rz: (&mut [u64], &mut [u64]) = (ry.1).split_at_mut(5usize);
    let px: (&[u64], &[u64]) = p.split_at(0usize);
    let py: (&[u64], &[u64]) = (px.1).split_at(5usize);
    let pz: (&[u64], &[u64]) = (py.1).split_at(5usize);
    let mut beta: [u64; 5] = [0u64; 5usize];
    (&mut beta)[0usize] = 0x96c28719501eeu64;
    (&mut beta)[1usize] = 0x7512f58995c13u64;
    (&mut beta)[2usize] = 0xc3434e99cf049u64;
    (&mut beta)[3usize] = 0x7106e64479eau64;
    (&mut beta)[4usize] = 0x7ae96a2b657cu64;
    crate::bignum_k256::fmul(ry.0, &beta, py.0);
    rz.0[0usize] = pz.0[0usize];
    rz.0[1usize] = pz.0[1usize];
    rz.0[2usize] = pz.0[2usize];
    rz.0[3usize] = pz.0[3usize];
    rz.0[4usize] = pz.0[4usize];
    rz.1[0usize] = pz.1[0usize];
    rz.1[1usize] = pz.1[1usize];
    rz.1[2usize] = pz.1[2usize];
    rz.1[3usize] = pz.1[3usize];
    rz.1[4usize] = pz.1[4usize]
}

#[inline] fn point_mul_lambda_inplace(res: &mut [u64])
{
    let rx: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let mut beta: [u64; 5] = [0u64; 5usize];
    (&mut beta)[0usize] = 0x96c28719501eeu64;
    (&mut beta)[1usize] = 0x7512f58995c13u64;
    (&mut beta)[2usize] = 0xc3434e99cf049u64;
    (&mut beta)[3usize] = 0x7106e64479eau64;
    (&mut beta)[4usize] = 0x7ae96a2b657cu64;
    let mut f2_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f2_copy)[0usize..5usize]).copy_from_slice(&rx.1[0usize..5usize]);
    crate::bignum_k256::fmul(rx.1, &beta, &f2_copy)
}

#[derive(PartialEq, Clone, Copy)] struct __bool_bool { pub fst: bool, pub snd: bool }

#[inline] fn ecmult_endo_split(
    r1: &mut [u64],
    r2: &mut [u64],
    q1: &mut [u64],
    q2: &mut [u64],
    scalar: &[u64],
    q: &[u64]
) ->
    crate::k256_ecdsa::__bool_bool
{
    crate::k256_ecdsa::scalar_split_lambda(r1, r2, scalar);
    crate::k256_ecdsa::point_mul_lambda(q2, q);
    (q1[0usize..15usize]).copy_from_slice(&q[0usize..15usize]);
    let b: bool = crate::k256_ecdsa::is_qelem_le_q_halved_vartime(r1);
    crate::k256_ecdsa::qnegate_conditional_vartime(r1, ! b);
    crate::k256_ecdsa::point_negate_conditional_vartime(q1, ! b);
    let is_high1: bool = ! b;
    let b0: bool = crate::k256_ecdsa::is_qelem_le_q_halved_vartime(r2);
    crate::k256_ecdsa::qnegate_conditional_vartime(r2, ! b0);
    crate::k256_ecdsa::point_negate_conditional_vartime(q2, ! b0);
    let is_high2: bool = ! b0;
    crate::k256_ecdsa::__bool_bool { fst: is_high1, snd: is_high2 }
}

pub(crate) fn point_mul(out: &mut [u64], scalar: &[u64], q: &[u64])
{
    let mut table: [u64; 240] = [0u64; 240usize];
    let mut tmp: [u64; 15] = [0u64; 15usize];
    let t0: (&mut [u64], &mut [u64]) = table.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = (t0.1).split_at_mut(15usize);
    crate::k256_ecdsa::make_point_at_inf(t1.0);
    (t1.1[0usize..15usize]).copy_from_slice(&q[0usize..15usize]);
    lowstar::ignore::ignore::<&[u64]>(&table);
    krml::unroll_for!(
        7,
        "i",
        0u32,
        1u32,
        {
            let t11: (&[u64], &[u64]) =
                table.split_at(i.wrapping_add(1u32).wrapping_mul(15u32) as usize);
            let mut p_copy: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy)[0usize..15usize]).copy_from_slice(&t11.1[0usize..15usize]);
            crate::k256_ecdsa::point_double(&mut tmp, &p_copy);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(15u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(15u32)
            as
            usize
            +
            15usize]).copy_from_slice(&(&tmp)[0usize..15usize]);
            let t2: (&[u64], &[u64]) =
                table.split_at(2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(15u32) as usize);
            let mut p_copy0: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&q[0usize..15usize]);
            crate::k256_ecdsa::point_add(&mut tmp, &p_copy0, t2.1);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(15u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(15u32)
            as
            usize
            +
            15usize]).copy_from_slice(&(&tmp)[0usize..15usize])
        }
    );
    crate::k256_ecdsa::make_point_at_inf(out);
    let mut tmp0: [u64; 15] = [0u64; 15usize];
    for i in 0u32..64u32
    {
        krml::unroll_for!(
            4,
            "_i",
            0u32,
            1u32,
            {
                let mut p_copy: [u64; 15] = [0u64; 15usize];
                ((&mut p_copy)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
                crate::k256_ecdsa::point_double(out, &p_copy)
            }
        );
        let k: u32 = 256u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar, k, 4u32);
        lowstar::ignore::ignore::<&[u64]>(&table);
        ((&mut tmp0)[0usize..15usize]).copy_from_slice(&(&(&table)[0usize..])[0usize..15usize]);
        krml::unroll_for!(
            15,
            "i0",
            0u32,
            1u32,
            {
                let c: u64 = fstar::uint64::eq_mask(bits_l, i0.wrapping_add(1u32) as u64);
                let res_j: (&[u64], &[u64]) =
                    table.split_at(i0.wrapping_add(1u32).wrapping_mul(15u32) as usize);
                krml::unroll_for!(
                    15,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let x: u64 = c & res_j.1[i1 as usize] | ! c & (&tmp0)[i1 as usize];
                        let os: (&mut [u64], &mut [u64]) = tmp0.split_at_mut(0usize);
                        os.1[i1 as usize] = x
                    }
                )
            }
        );
        let mut p_copy: [u64; 15] = [0u64; 15usize];
        ((&mut p_copy)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
        crate::k256_ecdsa::point_add(out, &p_copy, &tmp0)
    }
}

#[inline] fn precomp_get_consttime(table: &[u64], bits_l: u64, tmp: &mut [u64])
{
    (tmp[0usize..15usize]).copy_from_slice(&(&table[0usize..])[0usize..15usize]);
    krml::unroll_for!(
        15,
        "i",
        0u32,
        1u32,
        {
            let c: u64 = fstar::uint64::eq_mask(bits_l, i.wrapping_add(1u32) as u64);
            let res_j: (&[u64], &[u64]) =
                table.split_at(i.wrapping_add(1u32).wrapping_mul(15u32) as usize);
            krml::unroll_for!(
                15,
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

#[inline] fn point_mul_g(out: &mut [u64], scalar: &[u64])
{
    let mut q1: [u64; 15] = [0u64; 15usize];
    let gx: (&mut [u64], &mut [u64]) = q1.split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = (gx.1).split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = (gy.1).split_at_mut(5usize);
    gy.0[0usize] = 0x2815b16f81798u64;
    gy.0[1usize] = 0xdb2dce28d959fu64;
    gy.0[2usize] = 0xe870b07029bfcu64;
    gy.0[3usize] = 0xbbac55a06295cu64;
    gy.0[4usize] = 0x79be667ef9dcu64;
    gz.0[0usize] = 0x7d08ffb10d4b8u64;
    gz.0[1usize] = 0x48a68554199c4u64;
    gz.0[2usize] = 0xe1108a8fd17b4u64;
    gz.0[3usize] = 0xc4655da4fbfc0u64;
    gz.0[4usize] = 0x483ada7726a3u64;
    (gz.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    gz.1[0usize] = 1u64;
    let q2: [u64; 15] =
        [4496295042185355u64, 3125448202219451u64, 1239608518490046u64, 2687445637493112u64,
            77979604880139u64, 3360310474215011u64, 1216410458165163u64, 177901593587973u64,
            3209978938104985u64, 118285133003718u64, 434519962075150u64, 1114612377498854u64,
            3488596944003813u64, 450716531072892u64, 66044973203836u64];
    lowstar::ignore::ignore::<&[u64]>(&q2);
    let q3: [u64; 15] =
        [1277614565900951u64, 378671684419493u64, 3176260448102880u64, 1575691435565077u64,
            167304528382180u64, 2600787765776588u64, 7497946149293u64, 2184272641272202u64,
            2200235265236628u64, 265969268774814u64, 1913228635640715u64, 2831959046949342u64,
            888030405442963u64, 1817092932985033u64, 101515844997121u64];
    lowstar::ignore::ignore::<&[u64]>(&q3);
    let q4: [u64; 15] =
        [34056422761564u64, 3315864838337811u64, 3797032336888745u64, 2580641850480806u64,
            208048944042500u64, 1233795288689421u64, 1048795233382631u64, 646545158071530u64,
            1816025742137285u64, 12245672982162u64, 2119364213800870u64, 2034960311715107u64,
            3172697815804487u64, 4185144850224160u64, 2792055915674u64];
    lowstar::ignore::ignore::<&[u64]>(&q4);
    let r1: (&[u64], &[u64]) = scalar.split_at(0usize);
    let r2: (&[u64], &[u64]) = (r1.1).split_at(1usize);
    let r3: (&[u64], &[u64]) = (r2.1).split_at(1usize);
    let r4: (&[u64], &[u64]) = (r3.1).split_at(1usize);
    crate::k256_ecdsa::make_point_at_inf(out);
    let mut tmp: [u64; 15] = [0u64; 15usize];
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
                    let mut p_copy: [u64; 15] = [0u64; 15usize];
                    ((&mut p_copy)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
                    crate::k256_ecdsa::point_double(out, &p_copy)
                }
            );
            let k: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r4.1, k, 4u32);
            lowstar::ignore::ignore::<&[u64]>(
                &crate::k256_precomptable::precomp_g_pow2_192_table_w4
            );
            crate::k256_ecdsa::precomp_get_consttime(
                &crate::k256_precomptable::precomp_g_pow2_192_table_w4,
                bits_l,
                &mut tmp
            );
            let mut p_copy: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy, &tmp);
            let k0: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l0: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r4.0, k0, 4u32);
            lowstar::ignore::ignore::<&[u64]>(
                &crate::k256_precomptable::precomp_g_pow2_128_table_w4
            );
            crate::k256_ecdsa::precomp_get_consttime(
                &crate::k256_precomptable::precomp_g_pow2_128_table_w4,
                bits_l0,
                &mut tmp
            );
            let mut p_copy0: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy0, &tmp);
            let k1: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l1: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r3.0, k1, 4u32);
            lowstar::ignore::ignore::<&[u64]>(&crate::k256_precomptable::precomp_g_pow2_64_table_w4);
            crate::k256_ecdsa::precomp_get_consttime(
                &crate::k256_precomptable::precomp_g_pow2_64_table_w4,
                bits_l1,
                &mut tmp
            );
            let mut p_copy1: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy1)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy1, &tmp);
            let k2: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
            let bits_l2: u64 = bignum::bignum_base::bn_get_bits_u64(1u32, r2.0, k2, 4u32);
            lowstar::ignore::ignore::<&[u64]>(&crate::k256_precomptable::precomp_basepoint_table_w4);
            crate::k256_ecdsa::precomp_get_consttime(
                &crate::k256_precomptable::precomp_basepoint_table_w4,
                bits_l2,
                &mut tmp
            );
            let mut p_copy2: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy2)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy2, &tmp)
        }
    )
}

#[inline] fn point_mul_g_double_vartime(
    out: &mut [u64],
    scalar1: &[u64],
    scalar2: &[u64],
    q2: &[u64]
)
{
    let mut q1: [u64; 15] = [0u64; 15usize];
    let gx: (&mut [u64], &mut [u64]) = q1.split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = (gx.1).split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = (gy.1).split_at_mut(5usize);
    gy.0[0usize] = 0x2815b16f81798u64;
    gy.0[1usize] = 0xdb2dce28d959fu64;
    gy.0[2usize] = 0xe870b07029bfcu64;
    gy.0[3usize] = 0xbbac55a06295cu64;
    gy.0[4usize] = 0x79be667ef9dcu64;
    gz.0[0usize] = 0x7d08ffb10d4b8u64;
    gz.0[1usize] = 0x48a68554199c4u64;
    gz.0[2usize] = 0xe1108a8fd17b4u64;
    gz.0[3usize] = 0xc4655da4fbfc0u64;
    gz.0[4usize] = 0x483ada7726a3u64;
    (gz.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    gz.1[0usize] = 1u64;
    let mut table2: [u64; 480] = [0u64; 480usize];
    let mut tmp: [u64; 15] = [0u64; 15usize];
    let t0: (&mut [u64], &mut [u64]) = table2.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = (t0.1).split_at_mut(15usize);
    crate::k256_ecdsa::make_point_at_inf(t1.0);
    (t1.1[0usize..15usize]).copy_from_slice(&q2[0usize..15usize]);
    lowstar::ignore::ignore::<&[u64]>(&table2);
    krml::unroll_for!(
        15,
        "i",
        0u32,
        1u32,
        {
            let t11: (&[u64], &[u64]) =
                table2.split_at(i.wrapping_add(1u32).wrapping_mul(15u32) as usize);
            let mut p_copy: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy)[0usize..15usize]).copy_from_slice(&t11.1[0usize..15usize]);
            crate::k256_ecdsa::point_double(&mut tmp, &p_copy);
            ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(15u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(15u32)
            as
            usize
            +
            15usize]).copy_from_slice(&(&tmp)[0usize..15usize]);
            let t2: (&[u64], &[u64]) =
                table2.split_at(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(15u32) as usize
                );
            let mut p_copy0: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&q2[0usize..15usize]);
            crate::k256_ecdsa::point_add(&mut tmp, &p_copy0, t2.1);
            ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(15u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(15u32)
            as
            usize
            +
            15usize]).copy_from_slice(&(&tmp)[0usize..15usize])
        }
    );
    let mut tmp0: [u64; 15] = [0u64; 15usize];
    let i: u32 = 255u32;
    let bits_c: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar1, i, 5u32);
    let bits_l32: u32 = bits_c as u32;
    let a_bits_l: &[u64] =
        &(&crate::k256_precomptable::precomp_basepoint_table_w5)[bits_l32.wrapping_mul(15u32)
        as
        usize..];
    (out[0usize..15usize]).copy_from_slice(&a_bits_l[0usize..15usize]);
    let i0: u32 = 255u32;
    let bits_c0: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar2, i0, 5u32);
    let bits_l320: u32 = bits_c0 as u32;
    let a_bits_l0: (&[u64], &[u64]) = table2.split_at(bits_l320.wrapping_mul(15u32) as usize);
    ((&mut tmp0)[0usize..15usize]).copy_from_slice(&a_bits_l0.1[0usize..15usize]);
    let mut p_copy: [u64; 15] = [0u64; 15usize];
    ((&mut p_copy)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
    crate::k256_ecdsa::point_add(out, &p_copy, &tmp0);
    let mut tmp1: [u64; 15] = [0u64; 15usize];
    for i1 in 0u32..51u32
    {
        krml::unroll_for!(
            5,
            "_i",
            0u32,
            1u32,
            {
                let mut p_copy0: [u64; 15] = [0u64; 15usize];
                ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
                crate::k256_ecdsa::point_double(out, &p_copy0)
            }
        );
        let k: u32 = 255u32.wrapping_sub(5u32.wrapping_mul(i1)).wrapping_sub(5u32);
        let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar2, k, 5u32);
        lowstar::ignore::ignore::<&[u64]>(&table2);
        let bits_l321: u32 = bits_l as u32;
        let a_bits_l1: (&[u64], &[u64]) = table2.split_at(bits_l321.wrapping_mul(15u32) as usize);
        ((&mut tmp1)[0usize..15usize]).copy_from_slice(&a_bits_l1.1[0usize..15usize]);
        let mut p_copy0: [u64; 15] = [0u64; 15usize];
        ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
        crate::k256_ecdsa::point_add(out, &p_copy0, &tmp1);
        let k0: u32 = 255u32.wrapping_sub(5u32.wrapping_mul(i1)).wrapping_sub(5u32);
        let bits_l0: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, scalar1, k0, 5u32);
        lowstar::ignore::ignore::<&[u64]>(&crate::k256_precomptable::precomp_basepoint_table_w5);
        let bits_l322: u32 = bits_l0 as u32;
        let a_bits_l2: &[u64] =
            &(&crate::k256_precomptable::precomp_basepoint_table_w5)[bits_l322.wrapping_mul(15u32)
            as
            usize..];
        ((&mut tmp1)[0usize..15usize]).copy_from_slice(&a_bits_l2[0usize..15usize]);
        let mut p_copy1: [u64; 15] = [0u64; 15usize];
        ((&mut p_copy1)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
        crate::k256_ecdsa::point_add(out, &p_copy1, &tmp1)
    }
}

#[inline] fn point_mul_g_double_split_lambda_table(
    out: &mut [u64],
    r1: &[u64],
    r2: &[u64],
    r3: &[u64],
    r4: &[u64],
    p2: &[u64],
    is_negate1: bool,
    is_negate2: bool,
    is_negate3: bool,
    is_negate4: bool
)
{
    let mut table2: [u64; 480] = [0u64; 480usize];
    let mut tmp: [u64; 15] = [0u64; 15usize];
    let t0: (&mut [u64], &mut [u64]) = table2.split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = (t0.1).split_at_mut(15usize);
    crate::k256_ecdsa::make_point_at_inf(t1.0);
    (t1.1[0usize..15usize]).copy_from_slice(&p2[0usize..15usize]);
    lowstar::ignore::ignore::<&[u64]>(&table2);
    krml::unroll_for!(
        15,
        "i",
        0u32,
        1u32,
        {
            let t11: (&[u64], &[u64]) =
                table2.split_at(i.wrapping_add(1u32).wrapping_mul(15u32) as usize);
            let mut p_copy: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy)[0usize..15usize]).copy_from_slice(&t11.1[0usize..15usize]);
            crate::k256_ecdsa::point_double(&mut tmp, &p_copy);
            ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(15u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(15u32)
            as
            usize
            +
            15usize]).copy_from_slice(&(&tmp)[0usize..15usize]);
            let t2: (&[u64], &[u64]) =
                table2.split_at(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(15u32) as usize
                );
            let mut p_copy0: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&p2[0usize..15usize]);
            crate::k256_ecdsa::point_add(&mut tmp, &p_copy0, t2.1);
            ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(15u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(15u32)
            as
            usize
            +
            15usize]).copy_from_slice(&(&tmp)[0usize..15usize])
        }
    );
    let mut tmp0: [u64; 15] = [0u64; 15usize];
    let mut tmp1: [u64; 15] = [0u64; 15usize];
    let i: u32 = 125u32;
    let bits_c: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r1, i, 5u32);
    let bits_l32: u32 = bits_c as u32;
    let a_bits_l: &[u64] =
        &(&crate::k256_precomptable::precomp_basepoint_table_w5)[bits_l32.wrapping_mul(15u32)
        as
        usize..];
    (out[0usize..15usize]).copy_from_slice(&a_bits_l[0usize..15usize]);
    crate::k256_ecdsa::point_negate_conditional_vartime(out, is_negate1);
    let i0: u32 = 125u32;
    let bits_c0: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r2, i0, 5u32);
    let bits_l320: u32 = bits_c0 as u32;
    let a_bits_l0: &[u64] =
        &(&crate::k256_precomptable::precomp_basepoint_table_w5)[bits_l320.wrapping_mul(15u32)
        as
        usize..];
    ((&mut tmp1)[0usize..15usize]).copy_from_slice(&a_bits_l0[0usize..15usize]);
    crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp1, is_negate2);
    crate::k256_ecdsa::point_mul_lambda_inplace(&mut tmp1);
    let mut p_copy: [u64; 15] = [0u64; 15usize];
    ((&mut p_copy)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
    crate::k256_ecdsa::point_add(out, &p_copy, &tmp1);
    let mut tmp10: [u64; 15] = [0u64; 15usize];
    let i1: u32 = 125u32;
    let bits_c1: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r3, i1, 5u32);
    let bits_l321: u32 = bits_c1 as u32;
    let a_bits_l1: (&[u64], &[u64]) = table2.split_at(bits_l321.wrapping_mul(15u32) as usize);
    ((&mut tmp0)[0usize..15usize]).copy_from_slice(&a_bits_l1.1[0usize..15usize]);
    crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp0, is_negate3);
    let i2: u32 = 125u32;
    let bits_c2: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r4, i2, 5u32);
    let bits_l322: u32 = bits_c2 as u32;
    let a_bits_l2: (&[u64], &[u64]) =
        (a_bits_l1.1).split_at(
            bits_l322.wrapping_mul(15u32) as usize - bits_l321.wrapping_mul(15u32) as usize
        );
    ((&mut tmp10)[0usize..15usize]).copy_from_slice(&a_bits_l2.1[0usize..15usize]);
    crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp10, is_negate4);
    crate::k256_ecdsa::point_mul_lambda_inplace(&mut tmp10);
    let mut p_copy0: [u64; 15] = [0u64; 15usize];
    ((&mut p_copy0)[0usize..15usize]).copy_from_slice(&(&tmp0)[0usize..15usize]);
    crate::k256_ecdsa::point_add(&mut tmp0, &p_copy0, &tmp10);
    let mut p_copy1: [u64; 15] = [0u64; 15usize];
    ((&mut p_copy1)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
    crate::k256_ecdsa::point_add(out, &p_copy1, &tmp0);
    let mut tmp2: [u64; 15] = [0u64; 15usize];
    krml::unroll_for!(
        25,
        "i3",
        0u32,
        1u32,
        {
            krml::unroll_for!(
                5,
                "_i",
                0u32,
                1u32,
                {
                    let mut p_copy2: [u64; 15] = [0u64; 15usize];
                    ((&mut p_copy2)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
                    crate::k256_ecdsa::point_double(out, &p_copy2)
                }
            );
            let k: u32 = 125u32.wrapping_sub(5u32.wrapping_mul(i3)).wrapping_sub(5u32);
            let bits_l: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r4, k, 5u32);
            lowstar::ignore::ignore::<&[u64]>(&table2);
            let bits_l323: u32 = bits_l as u32;
            let a_bits_l3: (&[u64], &[u64]) =
                table2.split_at(bits_l323.wrapping_mul(15u32) as usize);
            ((&mut tmp2)[0usize..15usize]).copy_from_slice(&a_bits_l3.1[0usize..15usize]);
            crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp2, is_negate4);
            crate::k256_ecdsa::point_mul_lambda_inplace(&mut tmp2);
            let mut p_copy2: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy2)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy2, &tmp2);
            let k0: u32 = 125u32.wrapping_sub(5u32.wrapping_mul(i3)).wrapping_sub(5u32);
            let bits_l0: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r3, k0, 5u32);
            lowstar::ignore::ignore::<&[u64]>(&table2);
            let bits_l324: u32 = bits_l0 as u32;
            let a_bits_l4: (&[u64], &[u64]) =
                table2.split_at(bits_l324.wrapping_mul(15u32) as usize);
            ((&mut tmp2)[0usize..15usize]).copy_from_slice(&a_bits_l4.1[0usize..15usize]);
            crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp2, is_negate3);
            let mut p_copy3: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy3)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy3, &tmp2);
            let k1: u32 = 125u32.wrapping_sub(5u32.wrapping_mul(i3)).wrapping_sub(5u32);
            let bits_l1: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r2, k1, 5u32);
            lowstar::ignore::ignore::<&[u64]>(&crate::k256_precomptable::precomp_basepoint_table_w5);
            let bits_l325: u32 = bits_l1 as u32;
            let a_bits_l5: &[u64] =
                &(&crate::k256_precomptable::precomp_basepoint_table_w5)[bits_l325.wrapping_mul(
                    15u32
                )
                as
                usize..];
            ((&mut tmp2)[0usize..15usize]).copy_from_slice(&a_bits_l5[0usize..15usize]);
            crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp2, is_negate2);
            crate::k256_ecdsa::point_mul_lambda_inplace(&mut tmp2);
            let mut p_copy4: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy4)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy4, &tmp2);
            let k2: u32 = 125u32.wrapping_sub(5u32.wrapping_mul(i3)).wrapping_sub(5u32);
            let bits_l2: u64 = bignum::bignum_base::bn_get_bits_u64(4u32, r1, k2, 5u32);
            lowstar::ignore::ignore::<&[u64]>(&crate::k256_precomptable::precomp_basepoint_table_w5);
            let bits_l326: u32 = bits_l2 as u32;
            let a_bits_l6: &[u64] =
                &(&crate::k256_precomptable::precomp_basepoint_table_w5)[bits_l326.wrapping_mul(
                    15u32
                )
                as
                usize..];
            ((&mut tmp2)[0usize..15usize]).copy_from_slice(&a_bits_l6[0usize..15usize]);
            crate::k256_ecdsa::point_negate_conditional_vartime(&mut tmp2, is_negate1);
            let mut p_copy5: [u64; 15] = [0u64; 15usize];
            ((&mut p_copy5)[0usize..15usize]).copy_from_slice(&out[0usize..15usize]);
            crate::k256_ecdsa::point_add(out, &p_copy5, &tmp2)
        }
    )
}

#[inline] fn check_ecmult_endo_split(r1: &[u64], r2: &[u64], r3: &[u64], r4: &[u64]) -> bool
{
    let f2: u64 = r1[2usize];
    let f3: u64 = r1[3usize];
    let b1: bool = f2 == 0u64 && f3 == 0u64;
    let f20: u64 = r2[2usize];
    let f30: u64 = r2[3usize];
    let b2: bool = f20 == 0u64 && f30 == 0u64;
    let f21: u64 = r3[2usize];
    let f31: u64 = r3[3usize];
    let b3: bool = f21 == 0u64 && f31 == 0u64;
    let f22: u64 = r4[2usize];
    let f32: u64 = r4[3usize];
    let b4: bool = f22 == 0u64 && f32 == 0u64;
    b1 && b2 && b3 && b4
}

#[derive(PartialEq, Clone, Copy)]
struct __bool_bool_bool_bool
{ pub fst: bool, pub snd: bool, pub thd: bool, pub f3: bool }

#[inline] fn point_mul_g_double_split_lambda_vartime(
    out: &mut [u64],
    scalar1: &[u64],
    scalar2: &[u64],
    p2: &[u64]
)
{
    let mut g: [u64; 15] = [0u64; 15usize];
    let gx: (&mut [u64], &mut [u64]) = g.split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = (gx.1).split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = (gy.1).split_at_mut(5usize);
    gy.0[0usize] = 0x2815b16f81798u64;
    gy.0[1usize] = 0xdb2dce28d959fu64;
    gy.0[2usize] = 0xe870b07029bfcu64;
    gy.0[3usize] = 0xbbac55a06295cu64;
    gy.0[4usize] = 0x79be667ef9dcu64;
    gz.0[0usize] = 0x7d08ffb10d4b8u64;
    gz.0[1usize] = 0x48a68554199c4u64;
    gz.0[2usize] = 0xe1108a8fd17b4u64;
    gz.0[3usize] = 0xc4655da4fbfc0u64;
    gz.0[4usize] = 0x483ada7726a3u64;
    (gz.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    gz.1[0usize] = 1u64;
    let mut r1234: [u64; 16] = [0u64; 16usize];
    let mut q1234: [u64; 60] = [0u64; 60usize];
    let r1: (&mut [u64], &mut [u64]) = r1234.split_at_mut(0usize);
    let r2: (&mut [u64], &mut [u64]) = (r1.1).split_at_mut(4usize);
    let r3: (&mut [u64], &mut [u64]) = (r2.1).split_at_mut(4usize);
    let r4: (&mut [u64], &mut [u64]) = (r3.1).split_at_mut(4usize);
    let q1: (&mut [u64], &mut [u64]) = q1234.split_at_mut(0usize);
    let q2: (&mut [u64], &mut [u64]) = (q1.1).split_at_mut(15usize);
    let q3: (&mut [u64], &mut [u64]) = (q2.1).split_at_mut(15usize);
    let q4: (&mut [u64], &mut [u64]) = (q3.1).split_at_mut(15usize);
    let scrut: crate::k256_ecdsa::__bool_bool =
        crate::k256_ecdsa::ecmult_endo_split(r2.0, r3.0, q2.0, q3.0, scalar1, &g);
    let is_high1: bool = scrut.fst;
    let is_high2: bool = scrut.snd;
    let scrut0: crate::k256_ecdsa::__bool_bool =
        crate::k256_ecdsa::ecmult_endo_split(r4.0, r4.1, q4.0, q4.1, scalar2, p2);
    let is_high3: bool = scrut0.fst;
    let is_high4: bool = scrut0.snd;
    let scrut1: crate::k256_ecdsa::__bool_bool_bool_bool =
        crate::k256_ecdsa::__bool_bool_bool_bool
        { fst: is_high1, snd: is_high2, thd: is_high3, f3: is_high4 };
    let is_high10: bool = scrut1.fst;
    let is_high20: bool = scrut1.snd;
    let is_high30: bool = scrut1.thd;
    let is_high40: bool = scrut1.f3;
    let is_r1234_valid: bool = crate::k256_ecdsa::check_ecmult_endo_split(r2.0, r3.0, r4.0, r4.1);
    if is_r1234_valid
    {
        crate::k256_ecdsa::point_mul_g_double_split_lambda_table(
            out,
            r2.0,
            r3.0,
            r4.0,
            r4.1,
            p2,
            is_high10,
            is_high20,
            is_high30,
            is_high40
        )
    }
    else
    { crate::k256_ecdsa::point_mul_g_double_vartime(out, scalar1, scalar2, p2) }
}

#[inline] fn fmul_eq_vartime(r: &[u64], z: &[u64], x: &[u64]) -> bool
{
    let mut tmp: [u64; 5] = [0u64; 5usize];
    crate::bignum_k256::fmul(&mut tmp, r, z);
    let mut f_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f_copy)[0usize..5usize]).copy_from_slice(&(&tmp)[0usize..5usize]);
    crate::bignum_k256::fnormalize(&mut tmp, &f_copy);
    let b: bool = crate::bignum_k256::is_felem_eq_vartime(&tmp, x);
    b
}

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
pub fn
ecdsa_sign_hashed_msg(signature: &mut [u8], msgHash: &[u8], private_key: &[u8], nonce: &[u8]) ->
    bool
{
    let oneq: [u64; 4] = [0x1u64, 0x0u64, 0x0u64, 0x0u64];
    lowstar::ignore::ignore::<&[u64]>(&oneq);
    let mut rsdk_q: [u64; 16] = [0u64; 16usize];
    let r_q: (&mut [u64], &mut [u64]) = rsdk_q.split_at_mut(0usize);
    let s_q: (&mut [u64], &mut [u64]) = (r_q.1).split_at_mut(4usize);
    let d_a: (&mut [u64], &mut [u64]) = (s_q.1).split_at_mut(4usize);
    let k_q: (&mut [u64], &mut [u64]) = (d_a.1).split_at_mut(4usize);
    let is_b_valid: u64 = crate::k256_ecdsa::load_qelem_check(k_q.0, private_key);
    let oneq1: [u64; 4] = [0x1u64, 0x0u64, 0x0u64, 0x0u64];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = (&oneq1)[i as usize];
            let x: u64 = uu____0 ^ is_b_valid & (k_q.0[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = (k_q.0).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_sk_valid: u64 = is_b_valid;
    let is_b_valid0: u64 = crate::k256_ecdsa::load_qelem_check(k_q.1, nonce);
    let oneq10: [u64; 4] = [0x1u64, 0x0u64, 0x0u64, 0x0u64];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____1: u64 = (&oneq10)[i as usize];
            let x: u64 = uu____1 ^ is_b_valid0 & (k_q.1[i as usize] ^ uu____1);
            let os: (&mut [u64], &mut [u64]) = (k_q.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_nonce_valid: u64 = is_b_valid0;
    let are_sk_nonce_valid: u64 = is_sk_valid & is_nonce_valid;
    let mut tmp: [u64; 5] = [0u64; 5usize];
    let mut x_bytes: [u8; 32] = [0u8; 32usize];
    let mut p: [u64; 15] = [0u64; 15usize];
    crate::k256_ecdsa::point_mul_g(&mut p, k_q.1);
    crate::k256_ecdsa::to_aff_point_x(&mut tmp, &p);
    crate::bignum_k256::store_felem(&mut x_bytes, &tmp);
    crate::k256_ecdsa::load_qelem_modq(s_q.0, &x_bytes);
    let mut z: [u64; 4] = [0u64; 4usize];
    let mut kinv: [u64; 4] = [0u64; 4usize];
    crate::k256_ecdsa::load_qelem_modq(&mut z, msgHash);
    crate::k256_ecdsa::qinv(&mut kinv, k_q.1);
    crate::k256_ecdsa::qmul(d_a.0, s_q.0, k_q.0);
    let mut f2_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy)[0usize..4usize]).copy_from_slice(&d_a.0[0usize..4usize]);
    crate::k256_ecdsa::qadd(d_a.0, &z, &f2_copy);
    let mut f2_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy0)[0usize..4usize]).copy_from_slice(&d_a.0[0usize..4usize]);
    crate::k256_ecdsa::qmul(d_a.0, &kinv, &f2_copy0);
    crate::k256_ecdsa::store_qelem(&mut signature[0usize..], s_q.0);
    crate::k256_ecdsa::store_qelem(&mut signature[32usize..], d_a.0);
    let is_r_zero: u64 = crate::k256_ecdsa::is_qelem_zero(s_q.0);
    let is_s_zero: u64 = crate::k256_ecdsa::is_qelem_zero(d_a.0);
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

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_sign_hashed_msg`.

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_sha256` if needed.
*/
pub fn
ecdsa_sign_sha256(
    signature: &mut [u8],
    msg_len: u32,
    msg: &[u8],
    private_key: &[u8],
    nonce: &[u8]
) ->
    bool
{
    let mut msgHash: [u8; 32] = [0u8; 32usize];
    crate::hash_sha2::hash_256(&mut msgHash, msg, msg_len);
    let b: bool =
        crate::k256_ecdsa::ecdsa_sign_hashed_msg(signature, &msgHash, private_key, nonce);
    b
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether `public key` is valid.
*/
pub fn
ecdsa_verify_hashed_msg(m: &[u8], public_key: &[u8], signature: &[u8]) ->
    bool
{
    let mut tmp: [u64; 35] = [0u64; 35usize];
    let pk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let r_q: (&mut [u64], &mut [u64]) = (pk.1).split_at_mut(15usize);
    let s_q: (&mut [u64], &mut [u64]) = (r_q.1).split_at_mut(4usize);
    let u1: (&mut [u64], &mut [u64]) = (s_q.1).split_at_mut(4usize);
    let u2: (&mut [u64], &mut [u64]) = (u1.1).split_at_mut(4usize);
    let m_q: (&mut [u64], &mut [u64]) = (u2.1).split_at_mut(4usize);
    let is_pk_valid: bool = crate::k256_ecdsa::load_point_vartime(r_q.0, public_key);
    let is_r_valid: bool = crate::k256_ecdsa::load_qelem_vartime(s_q.0, &signature[0usize..]);
    let is_s_valid: bool = crate::k256_ecdsa::load_qelem_vartime(u1.0, &signature[32usize..]);
    let is_rs_valid: bool = is_r_valid && is_s_valid;
    crate::k256_ecdsa::load_qelem_modq(m_q.1, m);
    if ! (is_pk_valid && is_rs_valid)
    { false }
    else
    {
        let mut sinv: [u64; 4] = [0u64; 4usize];
        crate::k256_ecdsa::qinv(&mut sinv, u1.0);
        crate::k256_ecdsa::qmul(u2.0, m_q.1, &sinv);
        crate::k256_ecdsa::qmul(m_q.0, s_q.0, &sinv);
        let mut res: [u64; 15] = [0u64; 15usize];
        crate::k256_ecdsa::point_mul_g_double_split_lambda_vartime(&mut res, u2.0, m_q.0, r_q.0);
        let mut tmp1: [u64; 5] = [0u64; 5usize];
        let pz: (&[u64], &[u64]) = res.split_at(10usize);
        crate::bignum_k256::fnormalize(&mut tmp1, pz.1);
        let b: bool = crate::bignum_k256::is_felem_zero_vartime(&tmp1);
        if b
        { false }
        else
        {
            let x: (&[u64], &[u64]) = (pz.0).split_at(0usize);
            let z: (&[u64], &[u64]) = (pz.1).split_at(0usize);
            let mut r_bytes: [u8; 32] = [0u8; 32usize];
            let mut r_fe: [u64; 5] = [0u64; 5usize];
            let mut tmp_q: [u64; 5] = [0u64; 5usize];
            let mut tmp_x: [u64; 5] = [0u64; 5usize];
            crate::k256_ecdsa::store_qelem(&mut r_bytes, s_q.0);
            crate::bignum_k256::load_felem(&mut r_fe, &r_bytes);
            crate::bignum_k256::fnormalize(&mut tmp_x, x.1);
            let is_rz_x: bool = crate::k256_ecdsa::fmul_eq_vartime(&r_fe, z.1, &tmp_x);
            if ! is_rz_x
            {
                let is_r_lt_p_m_q: bool =
                    crate::bignum_k256::is_felem_lt_prime_minus_order_vartime(&r_fe);
                if is_r_lt_p_m_q
                {
                    (&mut tmp_q)[0usize] = 0x25e8cd0364141u64;
                    (&mut tmp_q)[1usize] = 0xe6af48a03bbfdu64;
                    (&mut tmp_q)[2usize] = 0xffffffebaaedcu64;
                    (&mut tmp_q)[3usize] = 0xfffffffffffffu64;
                    (&mut tmp_q)[4usize] = 0xffffffffffffu64;
                    let mut f2_copy: [u64; 5] = [0u64; 5usize];
                    ((&mut f2_copy)[0usize..5usize]).copy_from_slice(&(&tmp_q)[0usize..5usize]);
                    crate::bignum_k256::fadd(&mut tmp_q, &r_fe, &f2_copy);
                    crate::k256_ecdsa::fmul_eq_vartime(&tmp_q, z.1, &tmp_x)
                }
                else
                { false }
            }
            else
            { true }
        }
    }
}

/**
Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_verify_hashed_msg`.

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_sha256` if needed.
*/
pub fn
ecdsa_verify_sha256(msg_len: u32, msg: &[u8], public_key: &[u8], signature: &[u8]) ->
    bool
{
    let mut mHash: [u8; 32] = [0u8; 32usize];
    crate::hash_sha2::hash_256(&mut mHash, msg, msg_len);
    let b: bool = crate::k256_ecdsa::ecdsa_verify_hashed_msg(&mHash, public_key, signature);
    b
}

/**
Compute canonical lowest S value for `signature` (R || S).

  The function returns `true` for successful normalization of S and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
pub fn
secp256k1_ecdsa_signature_normalize(signature: &mut [u8]) ->
    bool
{
    let mut s_q: [u64; 4] = [0u64; 4usize];
    let s: (&[u8], &[u8]) = signature.split_at(32usize);
    let is_sk_valid: bool = crate::k256_ecdsa::load_qelem_vartime(&mut s_q, s.1);
    if ! is_sk_valid
    { false }
    else
    {
        let is_sk_lt_q_halved: bool = crate::k256_ecdsa::is_qelem_le_q_halved_vartime(&s_q);
        crate::k256_ecdsa::qnegate_conditional_vartime(&mut s_q, ! is_sk_lt_q_halved);
        crate::k256_ecdsa::store_qelem(&mut signature[32usize..], &s_q);
        true
    }
}

/**
Check whether `signature` (R || S) is in canonical form.

  The function returns `true` if S is low-S normalized and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
pub fn
secp256k1_ecdsa_is_signature_normalized(signature: &[u8]) ->
    bool
{
    let mut s_q: [u64; 4] = [0u64; 4usize];
    let s: (&[u8], &[u8]) = signature.split_at(32usize);
    let is_s_valid: bool = crate::k256_ecdsa::load_qelem_vartime(&mut s_q, s.1);
    let is_s_lt_q_halved: bool = crate::k256_ecdsa::is_qelem_le_q_halved_vartime(&s_q);
    is_s_valid && is_s_lt_q_halved
}

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
pub fn
secp256k1_ecdsa_sign_hashed_msg(
    signature: &mut [u8],
    msgHash: &[u8],
    private_key: &[u8],
    nonce: &[u8]
) ->
    bool
{
    let b: bool = crate::k256_ecdsa::ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
    if b { crate::k256_ecdsa::secp256k1_ecdsa_signature_normalize(signature) } else { false }
}

/**
Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_sign_hashed_msg`.

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.
*/
pub fn
secp256k1_ecdsa_sign_sha256(
    signature: &mut [u8],
    msg_len: u32,
    msg: &[u8],
    private_key: &[u8],
    nonce: &[u8]
) ->
    bool
{
    let mut msgHash: [u8; 32] = [0u8; 32usize];
    crate::hash_sha2::hash_256(&mut msgHash, msg, msg_len);
    let b: bool =
        crate::k256_ecdsa::secp256k1_ecdsa_sign_hashed_msg(signature, &msgHash, private_key, nonce);
    b
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_hashed_msg` if needed.

  The function also checks whether `public_key` is valid
*/
pub fn
secp256k1_ecdsa_verify_hashed_msg(msgHash: &[u8], public_key: &[u8], signature: &[u8]) ->
    bool
{
    let is_s_normalized: bool =
        crate::k256_ecdsa::secp256k1_ecdsa_is_signature_normalized(signature);
    if ! is_s_normalized
    { false }
    else
    { crate::k256_ecdsa::ecdsa_verify_hashed_msg(msgHash, public_key, signature) }
}

/**
Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_verify_hashed_msg`.

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_sha256` if needed.
*/
pub fn
secp256k1_ecdsa_verify_sha256(msg_len: u32, msg: &[u8], public_key: &[u8], signature: &[u8]) ->
    bool
{
    let mut mHash: [u8; 32] = [0u8; 32usize];
    crate::hash_sha2::hash_256(&mut mHash, msg, msg_len);
    let b: bool =
        crate::k256_ecdsa::secp256k1_ecdsa_verify_hashed_msg(&mHash, public_key, signature);
    b
}

/**
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is valid point.
*/
pub fn
public_key_uncompressed_to_raw(pk_raw: &mut [u8], pk: &[u8]) ->
    bool
{
    let pk0: u8 = pk[0usize];
    if pk0 != 0x04u8
    { false }
    else
    {
        (pk_raw[0usize..64usize]).copy_from_slice(&(&pk[1usize..])[0usize..64usize]);
        true
    }
}

/**
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
pub fn
public_key_uncompressed_from_raw(pk: &mut [u8], pk_raw: &[u8])
{
    pk[0usize] = 0x04u8;
    (pk[1usize..1usize + 64usize]).copy_from_slice(&pk_raw[0usize..64usize])
}

/**
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is valid point.
*/
pub fn
public_key_compressed_to_raw(pk_raw: &mut [u8], pk: &[u8]) ->
    bool
{
    let mut xa: [u64; 5] = [0u64; 5usize];
    let mut ya: [u64; 5] = [0u64; 5usize];
    let b: bool = crate::k256_ecdsa::aff_point_decompress_vartime(&mut xa, &mut ya, pk);
    let pk_xb: (&[u8], &[u8]) = pk.split_at(1usize);
    if b
    {
        (pk_raw[0usize..32usize]).copy_from_slice(&pk_xb.1[0usize..32usize]);
        crate::bignum_k256::store_felem(&mut pk_raw[32usize..], &ya)
    };
    b
}

/**
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
pub fn
public_key_compressed_from_raw(pk: &mut [u8], pk_raw: &[u8])
{
    let pk_x: (&[u8], &[u8]) = pk_raw.split_at(0usize);
    let pk_y: (&[u8], &[u8]) = (pk_x.1).split_at(32usize);
    let x0: u8 = pk_y.1[31usize];
    let is_pk_y_odd: bool = x0 & 1u8 == 1u8;
    let ite: u8 = if is_pk_y_odd { 0x03u8 } else { 0x02u8 };
    pk[0usize] = ite;
    (pk[1usize..1usize + 32usize]).copy_from_slice(&pk_y.0[0usize..32usize])
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
is_public_key_valid(public_key: &[u8]) ->
    bool
{
    let mut p: [u64; 15] = [0u64; 15usize];
    let is_pk_valid: bool = crate::k256_ecdsa::load_point_vartime(&mut p, public_key);
    is_pk_valid
}

/**
Private key validation.

  The function returns `true` if a private key is valid and `false` otherwise.

  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve
*/
pub fn
is_private_key_valid(private_key: &[u8]) ->
    bool
{
    let mut s_q: [u64; 4] = [0u64; 4usize];
    let res: u64 = crate::k256_ecdsa::load_qelem_check(&mut s_q, private_key);
    res == 0xFFFFFFFFFFFFFFFFu64
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
secret_to_public(public_key: &mut [u8], private_key: &[u8]) ->
    bool
{
    let mut tmp: [u64; 19] = [0u64; 19usize];
    let pk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let sk: (&mut [u64], &mut [u64]) = (pk.1).split_at_mut(15usize);
    let is_b_valid: u64 = crate::k256_ecdsa::load_qelem_check(sk.1, private_key);
    let oneq: [u64; 4] = [0x1u64, 0x0u64, 0x0u64, 0x0u64];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = (&oneq)[i as usize];
            let x: u64 = uu____0 ^ is_b_valid & (sk.1[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = (sk.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_sk_valid: u64 = is_b_valid;
    crate::k256_ecdsa::point_mul_g(sk.0, sk.1);
    crate::k256_ecdsa::point_store(public_key, sk.0);
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64
}

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
ecdh(shared_secret: &mut [u8], their_pubkey: &[u8], private_key: &[u8]) ->
    bool
{
    let mut tmp: [u64; 34] = [0u64; 34usize];
    let pk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let ss: (&mut [u64], &mut [u64]) = (pk.1).split_at_mut(15usize);
    let sk: (&mut [u64], &mut [u64]) = (ss.1).split_at_mut(15usize);
    let is_pk_valid: bool = crate::k256_ecdsa::load_point_vartime(ss.0, their_pubkey);
    let is_b_valid: u64 = crate::k256_ecdsa::load_qelem_check(sk.1, private_key);
    let oneq: [u64; 4] = [0x1u64, 0x0u64, 0x0u64, 0x0u64];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u64 = (&oneq)[i as usize];
            let x: u64 = uu____0 ^ is_b_valid & (sk.1[i as usize] ^ uu____0);
            let os: (&mut [u64], &mut [u64]) = (sk.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let is_sk_valid: u64 = is_b_valid;
    if is_pk_valid
    {
        crate::k256_ecdsa::point_mul(sk.0, sk.1, ss.0);
        crate::k256_ecdsa::point_store(shared_secret, sk.0)
    };
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64 && is_pk_valid
}
