pub fn add(a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{
    let mut c: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1)
    };
    c
}

pub fn sub(a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{
    let mut c: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    c
}

pub fn add_mod(n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1)
    };
    let c0: u64 = c;
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let mut c1: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1)
    };
    let c10: u64 = c1;
    let c2: u64 = c0.wrapping_sub(c10);
    for i in 0u32..64u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x: u64 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x
    }
}

pub fn sub_mod(n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    let c0: u64 = c;
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let mut c1: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t1, t2, res_i.1)
    };
    let c10: u64 = c1;
    crate::lowstar::ignore::ignore::<u64>(c10);
    let c2: u64 = 0u64.wrapping_sub(c0);
    for i in 0u32..64u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x: u64 = c2 & (&mut tmp)[i as usize] | ! c2 & os.1[i as usize];
        os.1[i as usize] = x
    }
}

pub fn mul(a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: [u64; 256] = [0u64; 256usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint64(64u32, a, b, &mut tmp, res)
}

pub fn sqr(a: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: [u64; 256] = [0u64; 256usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_sqr_uint64(64u32, a, &mut tmp, res)
}

#[inline] fn precompr2(nBits: u32, n: &mut [u64], res: &mut [u64]) -> ()
{
    (res[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]);
    let i: u32 = nBits.wrapping_div(64u32);
    let j: u32 = nBits.wrapping_rem(64u32);
    res[i as usize] = res[i as usize] | 1u64.wrapping_shl(j);
    for i0 in 0u32..8192u32.wrapping_sub(nBits) { add_mod(n, res, res, res) }
}

#[inline] fn reduction(n: &mut [u64], nInv: u64, c: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c0: u64 = 0u64;
    for i in 0u32..64u32
    {
        let qj: u64 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = c.split_at_mut(i as usize);
        let mut c1: u64 = 0u64;
        for i0 in 0u32..16u32
        {
            let a_i: u64 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c1, res_i.1);
            let a_i0: u64 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, c1, res_i0.1);
            let a_i1: u64 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, c1, res_i1.1);
            let a_i2: u64 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, c1, res_i2.1)
        };
        for i0 in 64u32..64u32
        {
            let a_i: u64 = n[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(i0 as usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c1, res_i.1)
        };
        let r: u64 = c1;
        let c10: u64 = r;
        let resb: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(64usize);
        let res_j0: u64 = res_j.0[64u32.wrapping_add(i) as usize];
        c0 = crate::lib::inttypes_intrinsics::add_carry_u64(c0, c10, res_j0, resb.1)
    };
    (res[0usize..0usize + 64usize]).copy_from_slice(&(&mut c[64usize..])[0usize..0usize + 64usize]);
    let c00: u64 = c0;
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let mut c1: u64 = 0u64;
    for i in 0u32..16u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t12, t22, res_i2.1)
    };
    for i in 64u32..64u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1)
    };
    let c10: u64 = c1;
    let c2: u64 = c00.wrapping_sub(c10);
    for i in 0u32..64u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x: u64 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x
    }
}

#[inline] fn from(n: &mut [u64], nInv_u64: u64, aM: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [u64; 128] = [0u64; 128usize];
    ((&mut tmp)[0usize..0usize + 64usize]).copy_from_slice(&aM[0usize..0usize + 64usize]);
    reduction(n, nInv_u64, &mut tmp, a)
}

#[inline] fn areduction(n: &mut [u64], nInv: u64, c: &mut [u64], res: &mut [u64]) -> ()
{
    let mut c0: u64 = 0u64;
    for i in 0u32..64u32
    {
        let qj: u64 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = c.split_at_mut(i as usize);
        let mut c1: u64 = 0u64;
        for i0 in 0u32..16u32
        {
            let a_i: u64 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c1, res_i.1);
            let a_i0: u64 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, c1, res_i0.1);
            let a_i1: u64 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, c1, res_i1.1);
            let a_i2: u64 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, c1, res_i2.1)
        };
        for i0 in 64u32..64u32
        {
            let a_i: u64 = n[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(i0 as usize);
            c1 = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c1, res_i.1)
        };
        let r: u64 = c1;
        let c10: u64 = r;
        let resb: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(64usize);
        let res_j0: u64 = res_j.0[64u32.wrapping_add(i) as usize];
        c0 = crate::lib::inttypes_intrinsics::add_carry_u64(c0, c10, res_j0, resb.1)
    };
    (res[0usize..0usize + 64usize]).copy_from_slice(&(&mut c[64usize..])[0usize..0usize + 64usize]);
    let c00: u64 = c0;
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let c1: u64 = sub(res, n, &mut tmp);
    crate::lowstar::ignore::ignore::<u64>(c1);
    let m: u64 = 0u64.wrapping_sub(c00);
    for i in 0u32..64u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x: u64 = m & (&mut tmp)[i as usize] | ! m & os.1[i as usize];
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
    let mut tmp: [u64; 256] = [0u64; 256usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint64(64u32, aM, bM, &mut tmp, &mut c);
    areduction(n, nInv_u64, &mut c, resM)
}

#[inline] fn amont_sqr(n: &mut [u64], nInv_u64: u64, aM: &mut [u64], resM: &mut [u64]) -> ()
{
    let mut c: [u64; 128] = [0u64; 128usize];
    let mut tmp: [u64; 256] = [0u64; 256usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_sqr_uint64(64u32, aM, &mut tmp, &mut c);
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
    ((&mut a1)[0usize..0usize + 128usize]).copy_from_slice(&a[0usize..0usize + 128usize]);
    let mut c0: u64 = 0u64;
    for i in 0u32..64u32
    {
        let qj: u64 = mu.wrapping_mul((&mut a1)[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = (&mut a1).split_at_mut(i as usize);
        let mut c: u64 = 0u64;
        for i0 in 0u32..16u32
        {
            let a_i: u64 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c, res_i.1);
            let a_i0: u64 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, c, res_i0.1);
            let a_i1: u64 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, c, res_i1.1);
            let a_i2: u64 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, c, res_i2.1)
        };
        for i0 in 64u32..64u32
        {
            let a_i: u64 = n[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(i0 as usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c, res_i.1)
        };
        let r: u64 = c;
        let c1: u64 = r;
        let resb: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(64usize);
        let res_j0: u64 = res_j.0[64u32.wrapping_add(i) as usize];
        c0 = crate::lib::inttypes_intrinsics::add_carry_u64(c0, c1, res_j0, resb.1)
    };
    ((&mut a_mod)[0usize..0usize + 64usize]).copy_from_slice(
        &(&mut (&mut a1)[64usize..])[0usize..0usize + 64usize]
    );
    let c00: u64 = c0;
    let mut tmp: [u64; 64] = [0u64; 64usize];
    let c1: u64 = sub(&mut a_mod, n, &mut tmp);
    crate::lowstar::ignore::ignore::<u64>(c1);
    let m: u64 = 0u64.wrapping_sub(c00);
    for i in 0u32..64u32
    {
        let os: (&mut [u64], &mut [u64]) = (&mut a_mod).split_at_mut(0usize);
        let x: u64 = m & (&mut tmp)[i as usize] | ! m & os.1[i as usize];
        os.1[i as usize] = x
    };
    let mut c: [u64; 128] = [0u64; 128usize];
    mul(&mut a_mod, r2, &mut c);
    reduction(n, mu, &mut c, res)
}

pub fn mod(n: &mut [u64], a: &mut [u64], res: &mut [u64]) -> bool
{
    let mut one: [u64; 64] = [0u64; 64usize];
    ((&mut one)[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: u64 = 0u64;
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = acc;
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
    { (res[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

fn exp_check(n: &mut [u64], a: &mut [u64], bBits: u32, b: &mut [u64]) -> u64
{
    let mut one: [u64; 64] = [0u64; 64usize];
    ((&mut one)[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: u64 = 0u64;
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = acc;
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
            let mut acc0: u64 = 0u64;
            for i0 in 0u32..bLen
            {
                let beq: u64 =
                    crate::fstar::uint64::eq_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                let blt: u64 =
                    ! crate::fstar::uint64::gte_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64);
                ()
            };
            let res: u64 = acc0;
            res
        }
        else
        { 0xFFFFFFFFFFFFFFFFu64 };
    let mut acc0: u64 = 0u64;
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], n[i as usize]);
        acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m2: u64 = acc0;
    let m: u64 = m10 & m2;
    m00 & m
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
    { (res[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]) };
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
    { (res[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mod_inv_prime_vartime(n: &mut [u64], a: &mut [u64], res: &mut [u64]) -> bool
{
    let mut one: [u64; 64] = [0u64; 64usize];
    ((&mut one)[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: u64 = 0u64;
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = acc;
    let m00: u64 = m0 & m1;
    let mut bn_zero: [u64; 64] = [0u64; 64usize];
    let mut mask: u64 = 0xFFFFFFFFFFFFFFFFu64;
    for i in 0u32..64u32
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], (&mut bn_zero)[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u64 = mask;
    let res1: u64 = mask1;
    let m10: u64 = res1;
    let mut acc0: u64 = 0u64;
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], n[i as usize]);
        acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m2: u64 = acc0;
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
        let mut c: u64 = c0;
        for i in 0u32..15u32
        {
            let t1: u64 = a1.1[4u32.wrapping_mul(i) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
            c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, 0u64, res_i.1);
            let t10: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, 0u64, res_i0.1);
            let t11: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, 0u64, res_i1.1);
            let t12: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, 0u64, res_i2.1)
        };
        for i in 60u32..63u32
        {
            let t1: u64 = a1.1[i as usize];
            let res_i: (&mut [u64], &mut [u64]) = res10.1.split_at_mut(i as usize);
            c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, 0u64, res_i.1)
        };
        let c1: u64 = c;
        let c2: u64 = c1;
        crate::lowstar::ignore::ignore::<u64>(c2);
        exp_vartime(nBits, a1.0, a, 4096u32, res10.0, res)
    }
    else
    { (res[0usize..0usize + 64usize]).copy_from_slice(&[0u64; 64usize]) };
    is_valid_m == 0xFFFFFFFFFFFFFFFFu64
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
    let mut acc: u64 = 0u64;
    for i in 0u32..64u32
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], b[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    acc
}

pub fn eq_mask(a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut mask: u64 = 0xFFFFFFFFFFFFFFFFu64;
    for i in 0u32..64u32
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u64 = mask;
    mask1
}
