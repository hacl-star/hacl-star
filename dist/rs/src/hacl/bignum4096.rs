#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn add(a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{
    let mut c: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t1, t2, res_i.1)
    };
    (&mut c)[0usize]
}

pub fn sub(a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{
    let mut c: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1)
    };
    (&mut c)[0usize]
}

pub fn add_mod(n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c)[0usize], t1, t2, res_i.1)
    };
    let c0: u64 = (&mut c)[0usize];
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t1, t2, res_i.1)
    };
    let c10: u64 = (&mut c1)[0usize];
    let c2: u64 = c0.wrapping_sub(c10);
    for i in 0u32..64u32
    {
        let x: u64 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn sub_mod(n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, t2, res_i.1)
    };
    let c0: u64 = (&mut c)[0usize];
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c1)[0usize], t1, t2, res_i.1)
    };
    let c10: u64 = (&mut c1)[0usize];
    crate::lowstar::ignore::ignore::<u64>(c10);
    let c2: u64 = 0u64.wrapping_sub(c0);
    for i in 0u32..64u32
    {
        let x: u64 = c2 & (&mut tmp)[i as usize] | ! c2 & res[i as usize];
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn mul(a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: [u64; 256] = [0u64; 256usize];
    crate::hacl::bignum::bn_karatsuba_mul_uint64(64u32, a, b, &mut tmp, res)
}

pub fn sqr(a: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: [u64; 256] = [0u64; 256usize];
    crate::hacl::bignum::bn_karatsuba_sqr_uint64(64u32, a, &mut tmp, res)
}

#[inline] fn precompr2(nBits: u32, n: &mut [u64], res: &mut [u64]) -> ()
{
    (res[0usize..64usize]).copy_from_slice(&[0u64; 64usize]);
    let i: u32 = nBits.wrapping_div(64u32);
    let j: u32 = nBits.wrapping_rem(64u32);
    res[i as usize] = res[i as usize] | 1u64.wrapping_shl(j);
    for _i in 0u32..8192u32.wrapping_sub(nBits)
    {
        let mut a_copy: [u64; 64] = [0u64; 64usize];
        let mut b_copy: [u64; 64] = [0u64; 64usize];
        ((&mut a_copy)[0usize..64usize]).copy_from_slice(&res[0usize..64usize]);
        ((&mut b_copy)[0usize..64usize]).copy_from_slice(&res[0usize..64usize]);
        add_mod(n, &mut a_copy, &mut b_copy, res)
    }
}

#[inline] fn reduction(n: &mut [u64], nInv: u64, c: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c0: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let qj: u64 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = c.split_at_mut(i as usize);
        let mut c1: [u64; 1] = [0u64; 1usize];
        for i0 in 0u32..16u32
        {
            let a_i: u64 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, (&mut c1)[0usize], res_i.1);
            let a_i0: u64 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, (&mut c1)[0usize], res_i0.1);
            let a_i1: u64 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, (&mut c1)[0usize], res_i1.1);
            let a_i2: u64 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, (&mut c1)[0usize], res_i2.1)
        };
        for i0 in 64u32..64u32
        {
            let a_i: u64 = n[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(i0 as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, (&mut c1)[0usize], res_i.1)
        };
        let r: u64 = (&mut c1)[0usize];
        let c10: u64 = r;
        let res_j0: u64 = c[64u32.wrapping_add(i) as usize];
        let resb: (&mut [u64], &mut [u64]) = c.split_at_mut(i as usize + 64usize);
        (&mut c0)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c0)[0usize], c10, res_j0, resb.1)
    };
    (res[0usize..64usize]).copy_from_slice(&(&mut c[64usize..])[0usize..64usize]);
    let c00: u64 = (&mut c0)[0usize];
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let mut c1: [u64; 1] = [0u64; 1usize];
    for i in 0u32..16u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c1)[0usize], t1, t2, res_i.1)
    };
    let c10: u64 = (&mut c1)[0usize];
    let c2: u64 = c00.wrapping_sub(c10);
    for i in 0u32..64u32
    {
        let x: u64 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn to(n: &mut [u64], nInv: u64, r2: &mut [u64], a: &mut [u64], aM: &mut [u64]) -> ()
{
    let mut c: [u64; 128] = [0u64; 128usize];
    mul(a, r2, &mut c);
    reduction(n, nInv, &mut c, aM)
}

#[inline] fn from(n: &mut [u64], nInv_u64: u64, aM: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [u64; 128] = [0u64; 128usize];
    ((&mut tmp)[0usize..64usize]).copy_from_slice(&aM[0usize..64usize]);
    reduction(n, nInv_u64, &mut tmp, a)
}

#[inline] fn areduction(n: &mut [u64], nInv: u64, c: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c0: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let qj: u64 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = c.split_at_mut(i as usize);
        let mut c1: [u64; 1] = [0u64; 1usize];
        for i0 in 0u32..16u32
        {
            let a_i: u64 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, (&mut c1)[0usize], res_i.1);
            let a_i0: u64 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, (&mut c1)[0usize], res_i0.1);
            let a_i1: u64 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, (&mut c1)[0usize], res_i1.1);
            let a_i2: u64 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, (&mut c1)[0usize], res_i2.1)
        };
        for i0 in 64u32..64u32
        {
            let a_i: u64 = n[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(i0 as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, (&mut c1)[0usize], res_i.1)
        };
        let r: u64 = (&mut c1)[0usize];
        let c10: u64 = r;
        let res_j0: u64 = c[64u32.wrapping_add(i) as usize];
        let resb: (&mut [u64], &mut [u64]) = c.split_at_mut(i as usize + 64usize);
        (&mut c0)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u64((&mut c0)[0usize], c10, res_j0, resb.1)
    };
    (res[0usize..64usize]).copy_from_slice(&(&mut c[64usize..])[0usize..64usize]);
    let c00: u64 = (&mut c0)[0usize];
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let c1: u64 = sub(res, n, &mut tmp);
    crate::lowstar::ignore::ignore::<u64>(c1);
    let m: u64 = 0u64.wrapping_sub(c00);
    for i in 0u32..64u32
    {
        let x: u64 = m & (&mut tmp)[i as usize] | ! m & res[i as usize];
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn amont_mul(
    n: &mut [u64],
    nInv_u64: u64,
    aM: &mut [u64],
    bM: &mut [u64],
    resM: &mut [u64]
) ->
    ()
{
    let mut c: [u64; 128] = [0u64; 128usize];
    mul(aM, bM, &mut c);
    areduction(n, nInv_u64, &mut c, resM)
}

#[inline] fn amont_sqr(n: &mut [u64], nInv_u64: u64, aM: &mut [u64], resM: &mut [u64]) -> ()
{
    let mut c: [u64; 128] = [0u64; 128usize];
    sqr(aM, &mut c);
    areduction(n, nInv_u64, &mut c, resM)
}

#[inline] fn bn_slow_precomp(
    n: &mut [u64],
    mu: u64,
    r2: &mut [u64],
    a: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut a_mod: [u64; 64] = [0u64; 64usize];
    let mut a1: [u64; 128] = [0u64; 128usize];
    ((&mut a1)[0usize..128usize]).copy_from_slice(&a[0usize..128usize]);
    areduction(n, mu, &mut a1, &mut a_mod);
    to(n, mu, r2, &mut a_mod, res)
}

pub fn r#mod(n: &mut [u64], a: &mut [u64], res: &mut [u64]) -> bool
{
    let mut one: [u64; 64] = [0u64; 64usize];
    ((&mut one)[0usize..64usize]).copy_from_slice(&[0u64; 64usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = (&mut acc)[0usize];
    let is_valid_m: u64 = m0 & m1;
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(64u32, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    {
        let mut r2: [u64; 64] = [0u64; 64usize];
        precompr2(nBits, n, &mut r2);
        let mu: u64 = crate::hacl::bignum::mod_inv_uint64(n[0usize]);
        bn_slow_precomp(n, mu, &mut r2, a, res)
    }
    else
    { (res[0usize..64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

fn exp_check(n: &mut [u64], a: &mut [u64], bBits: u32, b: &mut [u64]) -> u64
{
    let mut one: [u64; 64] = [0u64; 64usize];
    ((&mut one)[0usize..64usize]).copy_from_slice(&[0u64; 64usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = (&mut acc)[0usize];
    let m00: u64 = m0 & m1;
    let bLen: u32 =
        if bBits == 0u32
        { 1u32 }
        else
        { bBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32) };
    let m10: u64 =
        if bBits < 64u32.wrapping_mul(bLen)
        {
            let mut b2: Vec<u64> = vec![0u64; bLen as usize];
            let i: u32 = bBits.wrapping_div(64u32);
            let j: u32 = bBits.wrapping_rem(64u32);
            (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u64.wrapping_shl(j);
            ();
            let mut acc0: [u64; 1] = [0u64; 1usize];
            for i0 in 0u32..bLen
            {
                let beq: u64 =
                    crate::fstar::uint64::eq_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                let blt: u64 =
                    ! crate::fstar::uint64::gte_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                (&mut acc0)[0usize] =
                    beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64);
                ()
            };
            let res: u64 = (&mut acc0)[0usize];
            res
        }
        else
        { 0xFFFFFFFFFFFFFFFFu64 };
    let mut acc0: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] =
            beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m2: u64 = (&mut acc0)[0usize];
    let m: u64 = m10 & m2;
    m00 & m
}

#[inline] fn exp_vartime_precomp(
    n: &mut [u64],
    mu: u64,
    r2: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    if bBits < 200u32
    {
        let mut aM: [u64; 64] = [0u64; 64usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u64; 64] = [0u64; 64usize];
        let mut ctx: [u64; 128] = [0u64; 128usize];
        ((&mut ctx)[0usize..64usize]).copy_from_slice(&n[0usize..64usize]);
        ((&mut ctx)[64usize..64usize + 64usize]).copy_from_slice(&r2[0usize..64usize]);
        let ctx_n: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u64], &mut [u64]) = ctx_n.1.split_at_mut(64usize);
        from(ctx_r2.0, mu, ctx_r2.1, &mut resM);
        crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
        for i in 0u32..bBits
        {
            let i1: u32 = i.wrapping_div(64u32);
            let j: u32 = i.wrapping_rem(64u32);
            let tmp: u64 = b[i1 as usize];
            let bit: u64 = tmp.wrapping_shr(j) & 1u64;
            if ! (bit == 0u64)
            {
                let mut aM_copy: [u64; 64] = [0u64; 64usize];
                ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut resM)[0usize..64usize]);
                let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
                amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut aM, &mut resM);
                crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
            };
            let mut aM_copy: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut aM)[0usize..64usize]);
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut aM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
        };
        from(n, mu, &mut resM, res)
    }
    else
    {
        let mut aM: [u64; 64] = [0u64; 64usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u64; 64] = [0u64; 64usize];
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32) };
        let mut ctx: [u64; 128] = [0u64; 128usize];
        ((&mut ctx)[0usize..64usize]).copy_from_slice(&n[0usize..64usize]);
        ((&mut ctx)[64usize..64usize + 64usize]).copy_from_slice(&r2[0usize..64usize]);
        let mut table: [u64; 1024] = [0u64; 1024usize];
        let mut tmp: [u64; 64] = [0u64; 64usize];
        let t0: (&mut [u64], &mut [u64]) = (&mut table).split_at_mut(0usize);
        let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(64usize);
        let ctx_n: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u64], &mut [u64]) = ctx_n.1.split_at_mut(64usize);
        from(ctx_r2.0, mu, ctx_r2.1, t1.0);
        crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
        (t1.1[0usize..64usize]).copy_from_slice(&(&mut aM)[0usize..64usize]);
        crate::lowstar::ignore::ignore::<&mut [u64]>(&mut table);
        for i in 0u32..7u32
        {
            let t11: (&mut [u64], &mut [u64]) =
                (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(64u32) as usize);
            let mut aM_copy: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&t11.1[0usize..64usize]);
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(64u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(64u32)
            as
            usize
            +
            64usize]).copy_from_slice(&(&mut tmp)[0usize..64usize]);
            let t2: (&mut [u64], &mut [u64]) =
                (&mut table).split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(64u32) as usize
                );
            let mut aM_copy0: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy0)[0usize..64usize]).copy_from_slice(&(&mut aM)[0usize..64usize]);
            let ctx_n1: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n1.1, mu, &mut aM_copy0, t2.1, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(64u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(64u32)
            as
            usize
            +
            64usize]).copy_from_slice(&(&mut tmp)[0usize..64usize])
        };
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u64 = crate::hacl::bignum_base::bn_get_bits_u64(bLen, b, i, 4u32);
            let bits_l32: u32 = bits_c as u32;
            let a_bits_l: (&[u64], &[u64]) =
                (&mut table).split_at(bits_l32.wrapping_mul(64u32) as usize);
            ((&mut resM)[0usize..64usize]).copy_from_slice(&a_bits_l.1[0usize..64usize])
        }
        else
        {
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            let ctx_r20: (&mut [u64], &mut [u64]) = ctx_n0.1.split_at_mut(64usize);
            from(ctx_r20.0, mu, ctx_r20.1, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
        };
        let mut tmp0: [u64; 64] = [0u64; 64usize];
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            for _i in 0u32..4u32
            {
                let mut aM_copy: [u64; 64] = [0u64; 64usize];
                ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut resM)[0usize..64usize]);
                let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
                amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut resM);
                crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
            };
            let k: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u64 = crate::hacl::bignum_base::bn_get_bits_u64(bLen, b, k, 4u32);
            crate::lowstar::ignore::ignore::<&[u64]>(&mut table);
            let bits_l32: u32 = bits_l as u32;
            let a_bits_l: (&[u64], &[u64]) =
                (&mut table).split_at(bits_l32.wrapping_mul(64u32) as usize);
            ((&mut tmp0)[0usize..64usize]).copy_from_slice(&a_bits_l.1[0usize..64usize]);
            let mut aM_copy: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut resM)[0usize..64usize]);
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut tmp0, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
        };
        from(n, mu, &mut resM, res)
    }
}

#[inline] fn exp_consttime_precomp(
    n: &mut [u64],
    mu: u64,
    r2: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    if bBits < 200u32
    {
        let mut aM: [u64; 64] = [0u64; 64usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u64; 64] = [0u64; 64usize];
        let mut ctx: [u64; 128] = [0u64; 128usize];
        ((&mut ctx)[0usize..64usize]).copy_from_slice(&n[0usize..64usize]);
        ((&mut ctx)[64usize..64usize + 64usize]).copy_from_slice(&r2[0usize..64usize]);
        let mut sw: [u64; 1] = [0u64; 1usize];
        let ctx_n: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u64], &mut [u64]) = ctx_n.1.split_at_mut(64usize);
        from(ctx_r2.0, mu, ctx_r2.1, &mut resM);
        crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
        for i in 0u32..bBits
        {
            let i1: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_div(64u32);
            let j: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_rem(64u32);
            let tmp: u64 = b[i1 as usize];
            let bit: u64 = tmp.wrapping_shr(j) & 1u64;
            let sw1: u64 = bit ^ (&mut sw)[0usize];
            for i0 in 0u32..64u32
            {
                let dummy: u64 =
                    0u64.wrapping_sub(sw1) & ((&mut resM)[i0 as usize] ^ (&mut aM)[i0 as usize]);
                (&mut resM)[i0 as usize] = (&mut resM)[i0 as usize] ^ dummy;
                (&mut aM)[i0 as usize] = (&mut aM)[i0 as usize] ^ dummy
            };
            let mut aM_copy: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut aM)[0usize..64usize]);
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut resM, &mut aM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
            let mut aM_copy0: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy0)[0usize..64usize]).copy_from_slice(&(&mut resM)[0usize..64usize]);
            let ctx_n1: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n1.1, mu, &mut aM_copy0, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
            (&mut sw)[0usize] = bit
        };
        let sw0: u64 = (&mut sw)[0usize];
        for i in 0u32..64u32
        {
            let dummy: u64 =
                0u64.wrapping_sub(sw0) & ((&mut resM)[i as usize] ^ (&mut aM)[i as usize]);
            (&mut resM)[i as usize] = (&mut resM)[i as usize] ^ dummy;
            (&mut aM)[i as usize] = (&mut aM)[i as usize] ^ dummy
        };
        from(n, mu, &mut resM, res)
    }
    else
    {
        let mut aM: [u64; 64] = [0u64; 64usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u64; 64] = [0u64; 64usize];
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32) };
        let mut ctx: [u64; 128] = [0u64; 128usize];
        ((&mut ctx)[0usize..64usize]).copy_from_slice(&n[0usize..64usize]);
        ((&mut ctx)[64usize..64usize + 64usize]).copy_from_slice(&r2[0usize..64usize]);
        let mut table: [u64; 1024] = [0u64; 1024usize];
        let mut tmp: [u64; 64] = [0u64; 64usize];
        let t0: (&mut [u64], &mut [u64]) = (&mut table).split_at_mut(0usize);
        let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(64usize);
        let ctx_n: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u64], &mut [u64]) = ctx_n.1.split_at_mut(64usize);
        from(ctx_r2.0, mu, ctx_r2.1, t1.0);
        crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
        (t1.1[0usize..64usize]).copy_from_slice(&(&mut aM)[0usize..64usize]);
        crate::lowstar::ignore::ignore::<&mut [u64]>(&mut table);
        for i in 0u32..7u32
        {
            let t11: (&mut [u64], &mut [u64]) =
                (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(64u32) as usize);
            let mut aM_copy: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&t11.1[0usize..64usize]);
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(64u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(64u32)
            as
            usize
            +
            64usize]).copy_from_slice(&(&mut tmp)[0usize..64usize]);
            let t2: (&mut [u64], &mut [u64]) =
                (&mut table).split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(64u32) as usize
                );
            let mut aM_copy0: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy0)[0usize..64usize]).copy_from_slice(&(&mut aM)[0usize..64usize]);
            let ctx_n1: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n1.1, mu, &mut aM_copy0, t2.1, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(64u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(64u32)
            as
            usize
            +
            64usize]).copy_from_slice(&(&mut tmp)[0usize..64usize])
        };
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u64 = crate::hacl::bignum_base::bn_get_bits_u64(bLen, b, i, 4u32);
            ((&mut resM)[0usize..64usize]).copy_from_slice(
                &(&mut (&mut table)[0usize..] as &mut [u64])[0usize..64usize]
            );
            for i0 in 0u32..15u32
            {
                let c: u64 = crate::fstar::uint64::eq_mask(bits_c, i0.wrapping_add(1u32) as u64);
                let res_j: (&[u64], &[u64]) =
                    (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(64u32) as usize);
                for i1 in 0u32..64u32
                {
                    let x: u64 = c & res_j.1[i1 as usize] | ! c & (&mut resM)[i1 as usize];
                    let os: (&mut [u64], &mut [u64]) = (&mut resM).split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            }
        }
        else
        {
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            let ctx_r20: (&mut [u64], &mut [u64]) = ctx_n0.1.split_at_mut(64usize);
            from(ctx_r20.0, mu, ctx_r20.1, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
        };
        let mut tmp0: [u64; 64] = [0u64; 64usize];
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            for _i in 0u32..4u32
            {
                let mut aM_copy: [u64; 64] = [0u64; 64usize];
                ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut resM)[0usize..64usize]);
                let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
                amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut resM);
                crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
            };
            let k: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u64 = crate::hacl::bignum_base::bn_get_bits_u64(bLen, b, k, 4u32);
            crate::lowstar::ignore::ignore::<&[u64]>(&mut table);
            ((&mut tmp0)[0usize..64usize]).copy_from_slice(
                &(&mut (&mut table)[0usize..] as &mut [u64])[0usize..64usize]
            );
            for i0 in 0u32..15u32
            {
                let c: u64 = crate::fstar::uint64::eq_mask(bits_l, i0.wrapping_add(1u32) as u64);
                let res_j: (&[u64], &[u64]) =
                    (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(64u32) as usize);
                for i1 in 0u32..64u32
                {
                    let x: u64 = c & res_j.1[i1 as usize] | ! c & (&mut tmp0)[i1 as usize];
                    let os: (&mut [u64], &mut [u64]) = (&mut tmp0).split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            };
            let mut aM_copy: [u64; 64] = [0u64; 64usize];
            ((&mut aM_copy)[0usize..64usize]).copy_from_slice(&(&mut resM)[0usize..64usize]);
            let ctx_n0: (&mut [u64], &mut [u64]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut tmp0, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u64]>(&mut ctx)
        };
        from(n, mu, &mut resM, res)
    }
}

#[inline] fn exp_vartime(
    nBits: u32,
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut r2: [u64; 64] = [0u64; 64usize];
    precompr2(nBits, n, &mut r2);
    let mu: u64 = crate::hacl::bignum::mod_inv_uint64(n[0usize]);
    exp_vartime_precomp(n, mu, &mut r2, a, bBits, b, res)
}

#[inline] fn exp_consttime(
    nBits: u32,
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut r2: [u64; 64] = [0u64; 64usize];
    precompr2(nBits, n, &mut r2);
    let mu: u64 = crate::hacl::bignum::mod_inv_uint64(n[0usize]);
    exp_consttime_precomp(n, mu, &mut r2, a, bBits, b, res)
}

pub fn mod_exp_vartime(
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    bool
{
    let is_valid_m: u64 = exp_check(n, a, bBits, b);
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(64u32, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    { exp_vartime(nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mod_exp_consttime(
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    bool
{
    let is_valid_m: u64 = exp_check(n, a, bBits, b);
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(64u32, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    { exp_consttime(nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mod_inv_prime_vartime(n: &mut [u64], a: &mut [u64], res: &mut [u64]) -> bool
{
    let mut one: [u64; 64] = [0u64; 64usize];
    ((&mut one)[0usize..64usize]).copy_from_slice(&[0u64; 64usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = (&mut acc)[0usize];
    let m00: u64 = m0 & m1;
    let mut bn_zero: [u64; 64] = [0u64; 64usize];
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    for i in 0u32..64u32
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], (&mut bn_zero)[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
    };
    let mask1: u64 = (&mut mask)[0usize];
    let res1: u64 = mask1;
    let m10: u64 = res1;
    let mut acc0: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] =
            beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m2: u64 = (&mut acc0)[0usize];
    let is_valid_m: u64 = m00 & ! m10 & m2;
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(64u32, n) as u32);
    if is_valid_m == 0xFFFFFFFFFFFFFFFFu64
    {
        let mut n2: [u64; 64] = [0u64; 64usize];
        let c0: u64 =
            crate::lib::inttypes_intrinsics::sub_borrow_u64(
                0u64,
                n[0usize],
                2u64,
                &mut (&mut n2)[0usize..]
            );
        let a1: (&mut [u64], &mut [u64]) = n.split_at_mut(1usize);
        let res10: (&mut [u64], &mut [u64]) = (&mut n2).split_at_mut(1usize);
        let mut c: [u64; 1] = [c0; 1usize];
        for i in 0u32..15u32
        {
            let t1: u64 = a1.1[4u32.wrapping_mul(i) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, 0u64, res_i.1);
            let t10: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64(
                    (&mut c)[0usize],
                    t10,
                    0u64,
                    res_i0.1
                );
            let t11: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64(
                    (&mut c)[0usize],
                    t11,
                    0u64,
                    res_i1.1
                );
            let t12: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64(
                    (&mut c)[0usize],
                    t12,
                    0u64,
                    res_i2.1
                )
        };
        for i in 60u32..63u32
        {
            let t1: u64 = a1.1[i as usize];
            let res_i: (&mut [u64], &mut [u64]) = res10.1.split_at_mut(i as usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, 0u64, res_i.1)
        };
        let c1: u64 = (&mut c)[0usize];
        let c2: u64 = c1;
        crate::lowstar::ignore::ignore::<u64>(c2);
        exp_vartime(nBits, n, a, 4096u32, &mut n2, res)
    }
    else
    { (res[0usize..64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mont_ctx_init(n: &mut [u64]) -> Vec<crate::hacl::bignum::bn_mont_ctx_u64>
{
    let mut r2: Vec<u64> = vec![0u64; 64usize];
    let mut n1: Vec<u64> = vec![0u64; 64usize];
    let r21: &mut [u64] = &mut r2;
    let n11: &mut [u64] = &mut n1;
    (n11[0usize..64usize]).copy_from_slice(&n[0usize..64usize]);
    let nBits: u32 =
        64u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u64(64u32, n) as u32);
    precompr2(nBits, n, r21);
    let mu: u64 = crate::hacl::bignum::mod_inv_uint64(n[0usize]);
    let mut res: crate::hacl::bignum::bn_mont_ctx_u64 =
        crate::hacl::bignum::bn_mont_ctx_u64
        { len: 64u32, n: n11.to_vec(), mu: mu, r2: r21.to_vec() };
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
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    bn_slow_precomp(n, mu, r2, a, res)
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
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    exp_vartime_precomp(n, mu, r2, a, bBits, b, res)
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
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    exp_consttime_precomp(n, mu, r2, a, bBits, b, res)
}

pub fn mod_inv_prime_vartime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u64],
    a: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let n: &mut [u64] = &mut (k[0usize]).n;
    let mu: u64 = (k[0usize]).mu;
    let r2: &mut [u64] = &mut (k[0usize]).r2;
    let mut n2: [u64; 64] = [0u64; 64usize];
    let c0: u64 =
        crate::lib::inttypes_intrinsics::sub_borrow_u64(
            0u64,
            n[0usize],
            2u64,
            &mut (&mut n2)[0usize..]
        );
    let a1: (&mut [u64], &mut [u64]) = n.split_at_mut(1usize);
    let res1: (&mut [u64], &mut [u64]) = (&mut n2).split_at_mut(1usize);
    let mut c: [u64; 1] = [c0; 1usize];
    for i in 0u32..15u32
    {
        let t1: u64 = a1.1[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, 0u64, res_i.1);
        let t10: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t10, 0u64, res_i0.1);
        let t11: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t11, 0u64, res_i1.1);
        let t12: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t12, 0u64, res_i2.1)
    };
    for i in 60u32..63u32
    {
        let t1: u64 = a1.1[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res1.1.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, 0u64, res_i.1)
    };
    let c1: u64 = (&mut c)[0usize];
    let c2: u64 = c1;
    crate::lowstar::ignore::ignore::<u64>(c2);
    exp_vartime_precomp(n, mu, r2, a, 4096u32, &mut n2, res)
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

pub fn bn_to_bytes_be(b: &mut [u64], res: &mut [u8]) -> ()
{
    let mut tmp: [u8; 512] = [0u8; 512usize];
    crate::lowstar::ignore::ignore::<&mut [u8]>(&mut tmp);
    for i in 0u32..64u32
    {
        crate::lowstar::endianness::store64_be(
            &mut res[i.wrapping_mul(8u32) as usize..],
            b[64u32.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    }
}

pub fn bn_to_bytes_le(b: &mut [u64], res: &mut [u8]) -> ()
{
    let mut tmp: [u8; 512] = [0u8; 512usize];
    crate::lowstar::ignore::ignore::<&mut [u8]>(&mut tmp);
    for i in 0u32..64u32
    {
        crate::lowstar::endianness::store64_le(
            &mut res[i.wrapping_mul(8u32) as usize..],
            b[i as usize]
        )
    }
}

pub fn lt_mask(a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], b[i as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    (&mut acc)[0usize]
}

pub fn eq_mask(a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    for i in 0u32..64u32
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
    };
    let mask1: u64 = (&mut mask)[0usize];
    mask1
}
