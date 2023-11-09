pub fn mul_wide_add2_u32(a: u32, b: u32, c_in: u32, out: &mut [u32]) -> u32
{
    let out0: u32 = out[0u32 as usize];
    let res: u64 =
        (a as u64).wrapping_mul(b as u64).wrapping_add(c_in as u64).wrapping_add(out0 as u64);
    out[0u32 as usize] = res as u32;
    res.wrapping_shr(32u32) as u32
}

pub fn mul_wide_add2_u64(a: u64, b: u64, c_in: u64, out: &mut [u64]) -> u64
{
    let out0: u64 = out[0u32 as usize];
    let res: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(a, b),
                crate::fstar::uint128::uint64_to_uint128(c_in)
            ),
            crate::fstar::uint128::uint64_to_uint128(out0)
        );
    out[0u32 as usize] = crate::fstar::uint128::uint128_to_uint64(res);
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(res, 64u32))
}

pub fn bn_get_top_index_u32(len: u32, b: &mut [u32]) -> u32
{
    let mut priv: u32 = 0u32;
    for i in 0u32..len
    {
        let mask: u32 = crate::fstar::uint32::eq_mask(b[i as usize], 0u32);
        priv = mask & priv | ! mask & i
    };
    priv
}

pub fn bn_get_top_index_u64(len: u32, b: &mut [u64]) -> u64
{
    let mut priv: u64 = 0u64;
    for i in 0u32..len
    {
        let mask: u64 = crate::fstar::uint64::eq_mask(b[i as usize], 0u64);
        priv = mask & priv | ! mask & i as u64
    };
    priv
}

pub fn bn_get_bits_u32(len: u32, b: &mut [u32], i: u32, l: u32) -> u32
{
    let i1: u32 = i.wrapping_div(32u32);
    let j: u32 = i.wrapping_rem(32u32);
    let p1: u32 = (b[i1 as usize]).wrapping_shr(j);
    let ite: u32 =
        if i1.wrapping_add(1u32) < len && 0u32 < j
        { p1 | (b[i1.wrapping_add(1u32) as usize]).wrapping_shl(32u32.wrapping_sub(j)) }
        else
        { p1 };
    ite & 1u32.wrapping_shl(l).wrapping_sub(1u32)
}

pub fn bn_get_bits_u64(len: u32, b: &mut [u64], i: u32, l: u32) -> u64
{
    let i1: u32 = i.wrapping_div(64u32);
    let j: u32 = i.wrapping_rem(64u32);
    let p1: u64 = (b[i1 as usize]).wrapping_shr(j);
    let ite: u64 =
        if i1.wrapping_add(1u32) < len && 0u32 < j
        { p1 | (b[i1.wrapping_add(1u32) as usize]).wrapping_shl(64u32.wrapping_sub(j)) }
        else
        { p1 };
    ite & 1u64.wrapping_shl(l).wrapping_sub(1u64)
}

pub fn bn_sub_eq_len_u32(aLen: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{
    let mut c: u32 = 0u32;
    for i in 0u32..aLen.wrapping_div(4u32)
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t12, t22, res_i2.1)
    };
    for i in aLen.wrapping_div(4u32).wrapping_mul(4u32)..aLen
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1)
    };
    c
}

pub fn bn_sub_eq_len_u64(aLen: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{
    let mut c: u64 = 0u64;
    for i in 0u32..aLen.wrapping_div(4u32)
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in aLen.wrapping_div(4u32).wrapping_mul(4u32)..aLen
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    c
}

pub fn bn_add_eq_len_u32(aLen: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{
    let mut c: u32 = 0u32;
    for i in 0u32..aLen.wrapping_div(4u32)
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t12, t22, res_i2.1)
    };
    for i in aLen.wrapping_div(4u32).wrapping_mul(4u32)..aLen
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1)
    };
    c
}

pub fn bn_add_eq_len_u64(aLen: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{
    let mut c: u64 = 0u64;
    for i in 0u32..aLen.wrapping_div(4u32)
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::add_carry_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::add_carry_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::add_carry_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes::intrinsics::add_carry_u64(c, t12, t22, res_i2.1)
    };
    for i in aLen.wrapping_div(4u32).wrapping_mul(4u32)..aLen
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes::intrinsics::add_carry_u64(c, t1, t2, res_i.1)
    };
    c
}