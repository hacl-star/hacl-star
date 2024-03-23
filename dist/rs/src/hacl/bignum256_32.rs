#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn add(a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{
    let mut c: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t1, t2, res_i.1)
    };
    (&mut c)[0usize]
}

pub fn sub(a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{
    let mut c: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, t2, res_i.1)
    };
    (&mut c)[0usize]
}

pub fn add_mod(n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{
    let mut c: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c)[0usize], t1, t2, res_i.1)
    };
    let c0: u32 = (&mut c)[0usize];
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let mut c1: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = res[i as usize];
        let t2: u32 = n[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = (&mut tmp).split_at_mut(i as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t1, t2, res_i.1)
    };
    let c10: u32 = (&mut c1)[0usize];
    let c2: u32 = c0.wrapping_sub(c10);
    for i in 0u32..8u32
    {
        let x: u32 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn sub_mod(n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{
    let mut c: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, t2, res_i.1)
    };
    let c0: u32 = (&mut c)[0usize];
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let mut c1: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = res[i as usize];
        let t2: u32 = n[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = (&mut tmp).split_at_mut(i as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c1)[0usize], t1, t2, res_i.1)
    };
    let c10: u32 = (&mut c1)[0usize];
    crate::lowstar::ignore::ignore::<u32>(c10);
    let c2: u32 = 0u32.wrapping_sub(c0);
    for i in 0u32..8u32
    {
        let x: u32 = c2 & (&mut tmp)[i as usize] | ! c2 & res[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn mul(a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{
    (res[0usize..16usize]).copy_from_slice(&[0u32; 16usize]);
    for i in 0u32..8u32
    {
        let bj: u32 = b[i as usize];
        let res_j: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        let mut c: [u32; 1] = [0u32; 1usize];
        for i0 in 0u32..2u32
        {
            let a_i: u32 = a[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, bj, (&mut c)[0usize], res_i.1);
            let a_i0: u32 = a[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i0, bj, (&mut c)[0usize], res_i0.1);
            let a_i1: u32 = a[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i1, bj, (&mut c)[0usize], res_i1.1);
            let a_i2: u32 = a[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i2, bj, (&mut c)[0usize], res_i2.1)
        };
        for i0 in 8u32..8u32
        {
            let a_i: u32 = a[i0 as usize];
            let res_i: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut(i0 as usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, bj, (&mut c)[0usize], res_i.1)
        };
        let r: u32 = (&mut c)[0usize];
        res[8u32.wrapping_add(i) as usize] = r
    }
}

pub fn sqr(a: &mut [u32], res: &mut [u32]) -> ()
{
    (res[0usize..16usize]).copy_from_slice(&[0u32; 16usize]);
    for i in 0u32..8u32
    {
        let a_j: u32 = a[i as usize];
        let ab: (&mut [u32], &mut [u32]) = a.split_at_mut(0usize);
        let res_j: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        let mut c: [u32; 1] = [0u32; 1usize];
        for i0 in 0u32..i.wrapping_div(4u32)
        {
            let a_i: u32 = ab.1[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, a_j, (&mut c)[0usize], res_i.1);
            let a_i0: u32 = ab.1[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i0, a_j, (&mut c)[0usize], res_i0.1);
            let a_i1: u32 = ab.1[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i1, a_j, (&mut c)[0usize], res_i1.1);
            let a_i2: u32 = ab.1[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i2, a_j, (&mut c)[0usize], res_i2.1)
        };
        for i0 in i.wrapping_div(4u32).wrapping_mul(4u32)..i
        {
            let a_i: u32 = ab.1[i0 as usize];
            let res_i: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut(i0 as usize);
            (&mut c)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, a_j, (&mut c)[0usize], res_i.1)
        };
        let r: u32 = (&mut c)[0usize];
        res[i.wrapping_add(i) as usize] = r
    };
    let mut a_copy: [u32; 16] = [0u32; 16usize];
    let mut b_copy: [u32; 16] = [0u32; 16usize];
    ((&mut a_copy)[0usize..16usize]).copy_from_slice(&res[0usize..16usize]);
    ((&mut b_copy)[0usize..16usize]).copy_from_slice(&res[0usize..16usize]);
    let r: u32 = crate::hacl::bignum_base::bn_add_eq_len_u32(16u32, &mut a_copy, &mut b_copy, res);
    let c0: u32 = r;
    crate::lowstar::ignore::ignore::<u32>(c0);
    let mut tmp: [u32; 16] = [0u32; 16usize];
    for i in 0u32..8u32
    {
        let res1: u64 = (a[i as usize] as u64).wrapping_mul(a[i as usize] as u64);
        let hi: u32 = res1.wrapping_shr(32u32) as u32;
        let lo: u32 = res1 as u32;
        (&mut tmp)[2u32.wrapping_mul(i) as usize] = lo;
        (&mut tmp)[2u32.wrapping_mul(i).wrapping_add(1u32) as usize] = hi
    };
    let mut a_copy0: [u32; 16] = [0u32; 16usize];
    let mut b_copy0: [u32; 16] = [0u32; 16usize];
    ((&mut a_copy0)[0usize..16usize]).copy_from_slice(&res[0usize..16usize]);
    ((&mut b_copy0)[0usize..16usize]).copy_from_slice(&(&mut tmp)[0usize..16usize]);
    let r0: u32 =
        crate::hacl::bignum_base::bn_add_eq_len_u32(16u32, &mut a_copy0, &mut b_copy0, res);
    let c1: u32 = r0;
    crate::lowstar::ignore::ignore::<u32>(c1)
}

#[inline] fn precompr2(nBits: u32, n: &mut [u32], res: &mut [u32]) -> ()
{
    (res[0usize..8usize]).copy_from_slice(&[0u32; 8usize]);
    let i: u32 = nBits.wrapping_div(32u32);
    let j: u32 = nBits.wrapping_rem(32u32);
    res[i as usize] = res[i as usize] | 1u32.wrapping_shl(j);
    for _i in 0u32..512u32.wrapping_sub(nBits)
    {
        let mut a_copy: [u32; 8] = [0u32; 8usize];
        let mut b_copy: [u32; 8] = [0u32; 8usize];
        ((&mut a_copy)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
        ((&mut b_copy)[0usize..8usize]).copy_from_slice(&res[0usize..8usize]);
        add_mod(n, &mut a_copy, &mut b_copy, res)
    }
}

#[inline] fn reduction(n: &mut [u32], nInv: u32, c: &mut [u32], res: &mut [u32]) -> ()
{
    let mut c0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let qj: u32 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize);
        let mut c1: [u32; 1] = [0u32; 1usize];
        for i0 in 0u32..2u32
        {
            let a_i: u32 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, (&mut c1)[0usize], res_i.1);
            let a_i0: u32 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i0, qj, (&mut c1)[0usize], res_i0.1);
            let a_i1: u32 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i1, qj, (&mut c1)[0usize], res_i1.1);
            let a_i2: u32 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i2, qj, (&mut c1)[0usize], res_i2.1)
        };
        for i0 in 8u32..8u32
        {
            let a_i: u32 = n[i0 as usize];
            let res_i: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut(i0 as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, (&mut c1)[0usize], res_i.1)
        };
        let r: u32 = (&mut c1)[0usize];
        let c10: u32 = r;
        let res_j0: u32 = c[8u32.wrapping_add(i) as usize];
        let resb: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize + 8usize);
        (&mut c0)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c0)[0usize], c10, res_j0, resb.1)
    };
    (res[0usize..8usize]).copy_from_slice(&(&mut c[8usize..])[0usize..8usize]);
    let c00: u32 = (&mut c0)[0usize];
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let mut c1: [u32; 1] = [0u32; 1usize];
    for i in 0u32..2u32
    {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t12, t22, res_i2.1)
    };
    for i in 8u32..8u32
    {
        let t1: u32 = res[i as usize];
        let t2: u32 = n[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = (&mut tmp).split_at_mut(i as usize);
        (&mut c1)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c1)[0usize], t1, t2, res_i.1)
    };
    let c10: u32 = (&mut c1)[0usize];
    let c2: u32 = c00.wrapping_sub(c10);
    for i in 0u32..8u32
    {
        let x: u32 = c2 & res[i as usize] | ! c2 & (&mut tmp)[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn to(n: &mut [u32], nInv: u32, r2: &mut [u32], a: &mut [u32], aM: &mut [u32]) -> ()
{
    let mut c: [u32; 16] = [0u32; 16usize];
    mul(a, r2, &mut c);
    reduction(n, nInv, &mut c, aM)
}

#[inline] fn from(n: &mut [u32], nInv_u64: u32, aM: &mut [u32], a: &mut [u32]) -> ()
{
    let mut tmp: [u32; 16] = [0u32; 16usize];
    ((&mut tmp)[0usize..8usize]).copy_from_slice(&aM[0usize..8usize]);
    reduction(n, nInv_u64, &mut tmp, a)
}

#[inline] fn areduction(n: &mut [u32], nInv: u32, c: &mut [u32], res: &mut [u32]) -> ()
{
    let mut c0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let qj: u32 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize);
        let mut c1: [u32; 1] = [0u32; 1usize];
        for i0 in 0u32..2u32
        {
            let a_i: u32 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, (&mut c1)[0usize], res_i.1);
            let a_i0: u32 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i0, qj, (&mut c1)[0usize], res_i0.1);
            let a_i1: u32 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i1, qj, (&mut c1)[0usize], res_i1.1);
            let a_i2: u32 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i2, qj, (&mut c1)[0usize], res_i2.1)
        };
        for i0 in 8u32..8u32
        {
            let a_i: u32 = n[i0 as usize];
            let res_i: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut(i0 as usize);
            (&mut c1)[0usize] =
                crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, (&mut c1)[0usize], res_i.1)
        };
        let r: u32 = (&mut c1)[0usize];
        let c10: u32 = r;
        let res_j0: u32 = c[8u32.wrapping_add(i) as usize];
        let resb: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize + 8usize);
        (&mut c0)[0usize] =
            crate::lib::inttypes_intrinsics::add_carry_u32((&mut c0)[0usize], c10, res_j0, resb.1)
    };
    (res[0usize..8usize]).copy_from_slice(&(&mut c[8usize..])[0usize..8usize]);
    let c00: u32 = (&mut c0)[0usize];
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let c1: u32 = sub(res, n, &mut tmp);
    crate::lowstar::ignore::ignore::<u32>(c1);
    let m: u32 = 0u32.wrapping_sub(c00);
    for i in 0u32..8u32
    {
        let x: u32 = m & (&mut tmp)[i as usize] | ! m & res[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn amont_mul(
    n: &mut [u32],
    nInv_u64: u32,
    aM: &mut [u32],
    bM: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let mut c: [u32; 16] = [0u32; 16usize];
    mul(aM, bM, &mut c);
    areduction(n, nInv_u64, &mut c, resM)
}

#[inline] fn amont_sqr(n: &mut [u32], nInv_u64: u32, aM: &mut [u32], resM: &mut [u32]) -> ()
{
    let mut c: [u32; 16] = [0u32; 16usize];
    sqr(aM, &mut c);
    areduction(n, nInv_u64, &mut c, resM)
}

#[inline] fn bn_slow_precomp(
    n: &mut [u32],
    mu: u32,
    r2: &mut [u32],
    a: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut a_mod: [u32; 8] = [0u32; 8usize];
    let mut a1: [u32; 16] = [0u32; 16usize];
    ((&mut a1)[0usize..16usize]).copy_from_slice(&a[0usize..16usize]);
    areduction(n, mu, &mut a1, &mut a_mod);
    to(n, mu, r2, &mut a_mod, res)
}

pub fn r#mod(n: &mut [u32], a: &mut [u32], res: &mut [u32]) -> bool
{
    let mut one: [u32; 8] = [0u32; 8usize];
    ((&mut one)[0usize..8usize]).copy_from_slice(&[0u32; 8usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = (&mut acc)[0usize];
    let is_valid_m: u32 = m0 & m1;
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(8u32, n));
    if is_valid_m == 0xFFFFFFFFu32
    {
        let mut r2: [u32; 8] = [0u32; 8usize];
        precompr2(nBits, n, &mut r2);
        let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
        bn_slow_precomp(n, mu, &mut r2, a, res)
    }
    else
    { (res[0usize..8usize]).copy_from_slice(&[0u32; 8usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

fn exp_check(n: &mut [u32], a: &mut [u32], bBits: u32, b: &mut [u32]) -> u32
{
    let mut one: [u32; 8] = [0u32; 8usize];
    ((&mut one)[0usize..8usize]).copy_from_slice(&[0u32; 8usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = (&mut acc)[0usize];
    let m00: u32 = m0 & m1;
    let bLen: u32 =
        if bBits == 0u32
        { 1u32 }
        else
        { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
    let m10: u32 =
        if bBits < 32u32.wrapping_mul(bLen)
        {
            let mut b2: Vec<u32> = vec![0u32; bLen as usize];
            let i: u32 = bBits.wrapping_div(32u32);
            let j: u32 = bBits.wrapping_rem(32u32);
            (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u32.wrapping_shl(j);
            ();
            let mut acc0: [u32; 1] = [0u32; 1usize];
            for i0 in 0u32..bLen
            {
                let beq: u32 =
                    crate::fstar::uint32::eq_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                let blt: u32 =
                    ! crate::fstar::uint32::gte_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                (&mut acc0)[0usize] =
                    beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32);
                ()
            };
            let res: u32 = (&mut acc0)[0usize];
            res
        }
        else
        { 0xFFFFFFFFu32 };
    let mut acc0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] =
            beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m2: u32 = (&mut acc0)[0usize];
    let m: u32 = m10 & m2;
    m00 & m
}

#[inline] fn exp_vartime_precomp(
    n: &mut [u32],
    mu: u32,
    r2: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    if bBits < 200u32
    {
        let mut aM: [u32; 8] = [0u32; 8usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 8] = [0u32; 8usize];
        let mut ctx: [u32; 16] = [0u32; 16usize];
        ((&mut ctx)[0usize..8usize]).copy_from_slice(&n[0usize..8usize]);
        ((&mut ctx)[8usize..8usize + 8usize]).copy_from_slice(&r2[0usize..8usize]);
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(8usize);
        from(ctx_r2.0, mu, ctx_r2.1, &mut resM);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
        for i in 0u32..bBits
        {
            let i1: u32 = i.wrapping_div(32u32);
            let j: u32 = i.wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            if ! (bit == 0u32)
            {
                let mut aM_copy: [u32; 8] = [0u32; 8usize];
                ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut resM)[0usize..8usize]);
                let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
                amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut aM, &mut resM);
                crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
            };
            let mut aM_copy: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut aM)[0usize..8usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut aM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
        };
        from(n, mu, &mut resM, res)
    }
    else
    {
        let mut aM: [u32; 8] = [0u32; 8usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 8] = [0u32; 8usize];
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
        let mut ctx: [u32; 16] = [0u32; 16usize];
        ((&mut ctx)[0usize..8usize]).copy_from_slice(&n[0usize..8usize]);
        ((&mut ctx)[8usize..8usize + 8usize]).copy_from_slice(&r2[0usize..8usize]);
        let mut table: [u32; 128] = [0u32; 128usize];
        let mut tmp: [u32; 8] = [0u32; 8usize];
        let t0: (&mut [u32], &mut [u32]) = (&mut table).split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(8usize);
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(8usize);
        from(ctx_r2.0, mu, ctx_r2.1, t1.0);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
        (t1.1[0usize..8usize]).copy_from_slice(&(&mut aM)[0usize..8usize]);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut table);
        for i in 0u32..7u32
        {
            let t11: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(8u32) as usize);
            let mut aM_copy: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&t11.1[0usize..8usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(8u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(8u32)
            as
            usize
            +
            8usize]).copy_from_slice(&(&mut tmp)[0usize..8usize]);
            let t2: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(8u32) as usize
                );
            let mut aM_copy0: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy0)[0usize..8usize]).copy_from_slice(&(&mut aM)[0usize..8usize]);
            let ctx_n1: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n1.1, mu, &mut aM_copy0, t2.1, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(8u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(8u32)
            as
            usize
            +
            8usize]).copy_from_slice(&(&mut tmp)[0usize..8usize])
        };
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            let bits_l32: u32 = bits_c;
            let a_bits_l: (&[u32], &[u32]) =
                (&mut table).split_at(bits_l32.wrapping_mul(8u32) as usize);
            ((&mut resM)[0usize..8usize]).copy_from_slice(&a_bits_l.1[0usize..8usize])
        }
        else
        {
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            let ctx_r20: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(8usize);
            from(ctx_r20.0, mu, ctx_r20.1, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
        };
        let mut tmp0: [u32; 8] = [0u32; 8usize];
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            for _i in 0u32..4u32
            {
                let mut aM_copy: [u32; 8] = [0u32; 8usize];
                ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut resM)[0usize..8usize]);
                let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
                amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut resM);
                crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
            };
            let k: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, k, 4u32);
            crate::lowstar::ignore::ignore::<&[u32]>(&mut table);
            let bits_l32: u32 = bits_l;
            let a_bits_l: (&[u32], &[u32]) =
                (&mut table).split_at(bits_l32.wrapping_mul(8u32) as usize);
            ((&mut tmp0)[0usize..8usize]).copy_from_slice(&a_bits_l.1[0usize..8usize]);
            let mut aM_copy: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut resM)[0usize..8usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut tmp0, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
        };
        from(n, mu, &mut resM, res)
    }
}

#[inline] fn exp_consttime_precomp(
    n: &mut [u32],
    mu: u32,
    r2: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    if bBits < 200u32
    {
        let mut aM: [u32; 8] = [0u32; 8usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 8] = [0u32; 8usize];
        let mut ctx: [u32; 16] = [0u32; 16usize];
        ((&mut ctx)[0usize..8usize]).copy_from_slice(&n[0usize..8usize]);
        ((&mut ctx)[8usize..8usize + 8usize]).copy_from_slice(&r2[0usize..8usize]);
        let mut sw: [u32; 1] = [0u32; 1usize];
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(8usize);
        from(ctx_r2.0, mu, ctx_r2.1, &mut resM);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
        for i in 0u32..bBits
        {
            let i1: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_div(32u32);
            let j: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            let sw1: u32 = bit ^ (&mut sw)[0usize];
            for i0 in 0u32..8u32
            {
                let dummy: u32 =
                    0u32.wrapping_sub(sw1) & ((&mut resM)[i0 as usize] ^ (&mut aM)[i0 as usize]);
                (&mut resM)[i0 as usize] = (&mut resM)[i0 as usize] ^ dummy;
                (&mut aM)[i0 as usize] = (&mut aM)[i0 as usize] ^ dummy
            };
            let mut aM_copy: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut aM)[0usize..8usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut resM, &mut aM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
            let mut aM_copy0: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy0)[0usize..8usize]).copy_from_slice(&(&mut resM)[0usize..8usize]);
            let ctx_n1: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n1.1, mu, &mut aM_copy0, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
            (&mut sw)[0usize] = bit
        };
        let sw0: u32 = (&mut sw)[0usize];
        for i in 0u32..8u32
        {
            let dummy: u32 =
                0u32.wrapping_sub(sw0) & ((&mut resM)[i as usize] ^ (&mut aM)[i as usize]);
            (&mut resM)[i as usize] = (&mut resM)[i as usize] ^ dummy;
            (&mut aM)[i as usize] = (&mut aM)[i as usize] ^ dummy
        };
        from(n, mu, &mut resM, res)
    }
    else
    {
        let mut aM: [u32; 8] = [0u32; 8usize];
        to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 8] = [0u32; 8usize];
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
        let mut ctx: [u32; 16] = [0u32; 16usize];
        ((&mut ctx)[0usize..8usize]).copy_from_slice(&n[0usize..8usize]);
        ((&mut ctx)[8usize..8usize + 8usize]).copy_from_slice(&r2[0usize..8usize]);
        let mut table: [u32; 128] = [0u32; 128usize];
        let mut tmp: [u32; 8] = [0u32; 8usize];
        let t0: (&mut [u32], &mut [u32]) = (&mut table).split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(8usize);
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(8usize);
        from(ctx_r2.0, mu, ctx_r2.1, t1.0);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
        (t1.1[0usize..8usize]).copy_from_slice(&(&mut aM)[0usize..8usize]);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut table);
        for i in 0u32..7u32
        {
            let t11: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(8u32) as usize);
            let mut aM_copy: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&t11.1[0usize..8usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(8u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(8u32)
            as
            usize
            +
            8usize]).copy_from_slice(&(&mut tmp)[0usize..8usize]);
            let t2: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(8u32) as usize
                );
            let mut aM_copy0: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy0)[0usize..8usize]).copy_from_slice(&(&mut aM)[0usize..8usize]);
            let ctx_n1: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n1.1, mu, &mut aM_copy0, t2.1, &mut tmp);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(8u32) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(8u32)
            as
            usize
            +
            8usize]).copy_from_slice(&(&mut tmp)[0usize..8usize])
        };
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            ((&mut resM)[0usize..8usize]).copy_from_slice(
                &(&mut (&mut table)[0usize..] as &mut [u32])[0usize..8usize]
            );
            for i0 in 0u32..15u32
            {
                let c: u32 = crate::fstar::uint32::eq_mask(bits_c, i0.wrapping_add(1u32));
                let res_j: (&[u32], &[u32]) =
                    (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(8u32) as usize);
                for i1 in 0u32..8u32
                {
                    let x: u32 = c & res_j.1[i1 as usize] | ! c & (&mut resM)[i1 as usize];
                    let os: (&mut [u32], &mut [u32]) = (&mut resM).split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            }
        }
        else
        {
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            let ctx_r20: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(8usize);
            from(ctx_r20.0, mu, ctx_r20.1, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
        };
        let mut tmp0: [u32; 8] = [0u32; 8usize];
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            for _i in 0u32..4u32
            {
                let mut aM_copy: [u32; 8] = [0u32; 8usize];
                ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut resM)[0usize..8usize]);
                let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
                amont_sqr(ctx_n0.1, mu, &mut aM_copy, &mut resM);
                crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
            };
            let k: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, k, 4u32);
            crate::lowstar::ignore::ignore::<&[u32]>(&mut table);
            ((&mut tmp0)[0usize..8usize]).copy_from_slice(
                &(&mut (&mut table)[0usize..] as &mut [u32])[0usize..8usize]
            );
            for i0 in 0u32..15u32
            {
                let c: u32 = crate::fstar::uint32::eq_mask(bits_l, i0.wrapping_add(1u32));
                let res_j: (&[u32], &[u32]) =
                    (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(8u32) as usize);
                for i1 in 0u32..8u32
                {
                    let x: u32 = c & res_j.1[i1 as usize] | ! c & (&mut tmp0)[i1 as usize];
                    let os: (&mut [u32], &mut [u32]) = (&mut tmp0).split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            };
            let mut aM_copy: [u32; 8] = [0u32; 8usize];
            ((&mut aM_copy)[0usize..8usize]).copy_from_slice(&(&mut resM)[0usize..8usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
            amont_mul(ctx_n0.1, mu, &mut aM_copy, &mut tmp0, &mut resM);
            crate::lowstar::ignore::ignore::<&mut [u32]>(&mut ctx)
        };
        from(n, mu, &mut resM, res)
    }
}

#[inline] fn exp_vartime(
    nBits: u32,
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut r2: [u32; 8] = [0u32; 8usize];
    precompr2(nBits, n, &mut r2);
    let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
    exp_vartime_precomp(n, mu, &mut r2, a, bBits, b, res)
}

#[inline] fn exp_consttime(
    nBits: u32,
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut r2: [u32; 8] = [0u32; 8usize];
    precompr2(nBits, n, &mut r2);
    let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
    exp_consttime_precomp(n, mu, &mut r2, a, bBits, b, res)
}

pub fn mod_exp_vartime(
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    bool
{
    let is_valid_m: u32 = exp_check(n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(8u32, n));
    if is_valid_m == 0xFFFFFFFFu32
    { exp_vartime(nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..8usize]).copy_from_slice(&[0u32; 8usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn mod_exp_consttime(
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    bool
{
    let is_valid_m: u32 = exp_check(n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(8u32, n));
    if is_valid_m == 0xFFFFFFFFu32
    { exp_consttime(nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..8usize]).copy_from_slice(&[0u32; 8usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn mod_inv_prime_vartime(n: &mut [u32], a: &mut [u32], res: &mut [u32]) -> bool
{
    let mut one: [u32; 8] = [0u32; 8usize];
    ((&mut one)[0usize..8usize]).copy_from_slice(&[0u32; 8usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&mut one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = (&mut acc)[0usize];
    let m00: u32 = m0 & m1;
    let mut bn_zero: [u32; 8] = [0u32; 8usize];
    let mut mask: [u32; 1] = [0xFFFFFFFFu32; 1usize];
    for i in 0u32..8u32
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], (&mut bn_zero)[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
    };
    let mask1: u32 = (&mut mask)[0usize];
    let res1: u32 = mask1;
    let m10: u32 = res1;
    let mut acc0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] =
            beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m2: u32 = (&mut acc0)[0usize];
    let is_valid_m: u32 = m00 & ! m10 & m2;
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(8u32, n));
    if is_valid_m == 0xFFFFFFFFu32
    {
        let mut n2: [u32; 8] = [0u32; 8usize];
        let c0: u32 =
            crate::lib::inttypes_intrinsics::sub_borrow_u32(
                0u32,
                n[0usize],
                2u32,
                &mut (&mut n2)[0usize..]
            );
        let a1: (&mut [u32], &mut [u32]) = n.split_at_mut(1usize);
        let res10: (&mut [u32], &mut [u32]) = (&mut n2).split_at_mut(1usize);
        let mut c: [u32; 1] = [c0; 1usize];
        for i in 0u32..1u32
        {
            let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, 0u32, res_i.1);
            let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u32(
                    (&mut c)[0usize],
                    t10,
                    0u32,
                    res_i0.1
                );
            let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u32(
                    (&mut c)[0usize],
                    t11,
                    0u32,
                    res_i1.1
                );
            let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u32(
                    (&mut c)[0usize],
                    t12,
                    0u32,
                    res_i2.1
                )
        };
        for i in 4u32..7u32
        {
            let t1: u32 = a1.1[i as usize];
            let res_i: (&mut [u32], &mut [u32]) = res10.1.split_at_mut(i as usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, 0u32, res_i.1)
        };
        let c1: u32 = (&mut c)[0usize];
        let c2: u32 = c1;
        crate::lowstar::ignore::ignore::<u32>(c2);
        exp_vartime(nBits, n, a, 256u32, &mut n2, res)
    }
    else
    { (res[0usize..8usize]).copy_from_slice(&[0u32; 8usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn mont_ctx_init(n: &mut [u32]) -> Vec<crate::hacl::bignum::bn_mont_ctx_u32>
{
    let mut r2: Vec<u32> = vec![0u32; 8usize];
    let mut n1: Vec<u32> = vec![0u32; 8usize];
    let r21: &mut [u32] = &mut r2;
    let n11: &mut [u32] = &mut n1;
    (n11[0usize..8usize]).copy_from_slice(&n[0usize..8usize]);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(8u32, n));
    precompr2(nBits, n, r21);
    let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
    let mut res: crate::hacl::bignum::bn_mont_ctx_u32 =
        crate::hacl::bignum::bn_mont_ctx_u32
        { len: 8u32, n: n11.to_vec(), mu: mu, r2: r21.to_vec() };
    let mut buf: Vec<crate::hacl::bignum::bn_mont_ctx_u32> =
        {
            let mut tmp: Vec<crate::hacl::bignum::bn_mont_ctx_u32> = Vec::new();
            tmp.push(res);
            tmp
        };
    buf
}

pub fn mod_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    a: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let n: &mut [u32] = &mut (k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &mut [u32] = &mut (k[0usize]).r2;
    bn_slow_precomp(n, mu, r2, a, res)
}

pub fn mod_exp_vartime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let n: &mut [u32] = &mut (k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &mut [u32] = &mut (k[0usize]).r2;
    exp_vartime_precomp(n, mu, r2, a, bBits, b, res)
}

pub fn mod_exp_consttime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let n: &mut [u32] = &mut (k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &mut [u32] = &mut (k[0usize]).r2;
    exp_consttime_precomp(n, mu, r2, a, bBits, b, res)
}

pub fn mod_inv_prime_vartime_precomp(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    a: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let n: &mut [u32] = &mut (k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &mut [u32] = &mut (k[0usize]).r2;
    let mut n2: [u32; 8] = [0u32; 8usize];
    let c0: u32 =
        crate::lib::inttypes_intrinsics::sub_borrow_u32(
            0u32,
            n[0usize],
            2u32,
            &mut (&mut n2)[0usize..]
        );
    let a1: (&mut [u32], &mut [u32]) = n.split_at_mut(1usize);
    let res1: (&mut [u32], &mut [u32]) = (&mut n2).split_at_mut(1usize);
    let mut c: [u32; 1] = [c0; 1usize];
    for i in 0u32..1u32
    {
        let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, 0u32, res_i.1);
        let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t10, 0u32, res_i0.1);
        let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t11, 0u32, res_i1.1);
        let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t12, 0u32, res_i2.1)
    };
    for i in 4u32..7u32
    {
        let t1: u32 = a1.1[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(i as usize);
        (&mut c)[0usize] =
            crate::lib::inttypes_intrinsics::sub_borrow_u32((&mut c)[0usize], t1, 0u32, res_i.1)
    };
    let c1: u32 = (&mut c)[0usize];
    let c2: u32 = c1;
    crate::lowstar::ignore::ignore::<u32>(c2);
    exp_vartime_precomp(n, mu, r2, a, 256u32, &mut n2, res)
}

pub fn new_bn_from_bytes_be(len: u32, b: &mut [u8]) -> Vec<u32>
{
    if
    len == 0u32
    ||
    ! (len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) <= 1073741823u32)
    { (&mut []).to_vec() }
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
                        &mut
                        (&mut tmp)[bnLen.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(4u32)
                        as
                        usize..]
                    );
                let x: u32 = u;
                let os: (&mut [u32], &mut [u32]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            };
            res2.to_vec()
        }
    }
}

pub fn new_bn_from_bytes_le(len: u32, b: &mut [u8]) -> Vec<u32>
{
    if
    len == 0u32
    ||
    ! (len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) <= 1073741823u32)
    { (&mut []).to_vec() }
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
                let bj: (&mut [u8], &mut [u8]) =
                    (&mut tmp).split_at_mut(i.wrapping_mul(4u32) as usize);
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

pub fn bn_to_bytes_be(b: &mut [u32], res: &mut [u8]) -> ()
{
    let mut tmp: [u8; 32] = [0u8; 32usize];
    crate::lowstar::ignore::ignore::<&mut [u8]>(&mut tmp);
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store32_be(
            &mut res[i.wrapping_mul(4u32) as usize..],
            b[8u32.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    }
}

pub fn bn_to_bytes_le(b: &mut [u32], res: &mut [u8]) -> ()
{
    let mut tmp: [u8; 32] = [0u8; 32usize];
    crate::lowstar::ignore::ignore::<&mut [u8]>(&mut tmp);
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store32_le(
            &mut res[i.wrapping_mul(4u32) as usize..],
            b[i as usize]
        )
    }
}

pub fn lt_mask(a: &mut [u32], b: &mut [u32]) -> u32
{
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..8u32
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], b[i as usize]);
        (&mut acc)[0usize] = beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    (&mut acc)[0usize]
}

pub fn eq_mask(a: &mut [u32], b: &mut [u32]) -> u32
{
    let mut mask: [u32; 1] = [0xFFFFFFFFu32; 1usize];
    for i in 0u32..8u32
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mut mask)[0usize]
    };
    let mask1: u32 = (&mut mask)[0usize];
    mask1
}
