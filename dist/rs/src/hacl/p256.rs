fn bn_is_zero_mask4(f: &mut [u64]) -> u64
{
    let mut bn_zero: [u64; 4] = [0u64; 4usize];
    let mut mask: u64 = 0xFFFFFFFFFFFFFFFFu64;
    for i in 0u32..4u32
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(f[i as usize], (&mut bn_zero)[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u64 = mask;
    let res: u64 = mask1;
    res
}

fn bn_is_zero_vartime4(f: &mut [u64]) -> bool
{
    let m: u64 = bn_is_zero_mask4(f);
    m == 0xFFFFFFFFFFFFFFFFu64
}

fn bn_is_eq_mask4(a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut mask: u64 = 0xFFFFFFFFFFFFFFFFu64;
    for i in 0u32..4u32
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u64 = mask;
    mask1
}

fn bn_is_eq_vartime4(a: &mut [u64], b: &mut [u64]) -> bool
{
    let m: u64 = bn_is_eq_mask4(a, b);
    m == 0xFFFFFFFFFFFFFFFFu64
}

fn bn_cmovznz4(res: &mut [u64], cin: u64, x: &mut [u64], y: &mut [u64]) -> ()
{
    let mask: u64 = ! crate::fstar::uint64::eq_mask(cin, 0u64);
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let uu____0: u64 = x[i as usize];
        let x1: u64 = uu____0 ^ mask & (y[i as usize] ^ uu____0);
        os.1[i as usize] = x1
    }
}

fn bn_add_mod4(res: &mut [u64], n: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut c: u64 = 0u64;
    for i in 0u32..1u32
    {
        let t1: u64 = x[4u32.wrapping_mul(i) as usize];
        let t2: u64 = y[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1);
        let t10: u64 = x[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = y[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t10, t20, res_i0.1);
        let t11: u64 = x[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = y[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t11, t21, res_i1.1);
        let t12: u64 = x[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = y[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t12, t22, res_i2.1)
    };
    for i in 4u32..4u32
    {
        let t1: u64 = x[i as usize];
        let t2: u64 = y[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1)
    };
    let c0: u64 = c;
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c1: u64 = 0u64;
    for i in 0u32..1u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
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
    for i in 4u32..4u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut((i as usize).wrapping_add(0usize));
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1)
    };
    let c10: u64 = c1;
    let c2: u64 = c0.wrapping_sub(c10);
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x1: u64 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x1
    }
}

fn bn_sub4(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> u64
{
    let mut c: u64 = 0u64;
    for i in 0u32..1u32
    {
        let t1: u64 = x[4u32.wrapping_mul(i) as usize];
        let t2: u64 = y[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = x[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = y[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = x[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = y[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = x[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = y[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in 4u32..4u32
    {
        let t1: u64 = x[i as usize];
        let t2: u64 = y[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    let c0: u64 = c;
    c0
}

fn bn_from_bytes_be4(res: &mut [u64], b: &mut [u8]) -> ()
for i in 0u32..4u32
{
    let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let u: u64 =
        crate::lowstar::endianness::load64_be(
            &mut b[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
        );
    let x: u64 = u;
    os.1[i as usize] = x
}

fn bn2_to_bytes_be4(res: &mut [u8], x: &mut [u64], y: &mut [u64]) -> ()
{
    crate::hacl::impl_p256_bignum::bn_to_bytes_be4(&mut res[0usize..], x);
    crate::hacl::impl_p256_bignum::bn_to_bytes_be4(&mut res[32usize..], y)
}

fn make_prime(n: &mut [u64]) -> ()
{
    n[0usize] = 0xffffffffffffffffu64;
    n[1usize] = 0xffffffffu64;
    n[2usize] = 0x0u64;
    n[3usize] = 0xffffffff00000001u64
}

fn make_order(n: &mut [u64]) -> ()
{
    n[0usize] = 0xf3b9cac2fc632551u64;
    n[1usize] = 0xbce6faada7179e84u64;
    n[2usize] = 0xffffffffffffffffu64;
    n[3usize] = 0xffffffff00000000u64
}

fn make_a_coeff(a: &mut [u64]) -> ()
{
    a[0usize] = 0xfffffffffffffffcu64;
    a[1usize] = 0x3ffffffffu64;
    a[2usize] = 0x0u64;
    a[3usize] = 0xfffffffc00000004u64
}

fn make_b_coeff(b: &mut [u64]) -> ()
{
    b[0usize] = 0xd89cdf6229c4bddfu64;
    b[1usize] = 0xacf005cd78843090u64;
    b[2usize] = 0xe5a220abf7212ed6u64;
    b[3usize] = 0xdc30061d04874834u64
}

fn make_g_x(n: &mut [u64]) -> ()
{
    n[0usize] = 0x79e730d418a9143cu64;
    n[1usize] = 0x75ba95fc5fedb601u64;
    n[2usize] = 0x79fb732b77622510u64;
    n[3usize] = 0x18905f76a53755c6u64
}

fn make_g_y(n: &mut [u64]) -> ()
{
    n[0usize] = 0xddf25357ce95560au64;
    n[1usize] = 0x8b4ab8e4ba19e45cu64;
    n[2usize] = 0xd2e88688dd21f325u64;
    n[3usize] = 0x8571ff1825885d85u64
}

fn make_fmont_R2(n: &mut [u64]) -> ()
{
    n[0usize] = 0x3u64;
    n[1usize] = 0xfffffffbffffffffu64;
    n[2usize] = 0xfffffffffffffffeu64;
    n[3usize] = 0x4fffffffdu64
}

fn make_fzero(n: &mut [u64]) -> ()
{
    n[0usize] = 0u64;
    n[1usize] = 0u64;
    n[2usize] = 0u64;
    n[3usize] = 0u64
}

fn make_fone(n: &mut [u64]) -> ()
{
    n[0usize] = 0x1u64;
    n[1usize] = 0xffffffff00000000u64;
    n[2usize] = 0xffffffffffffffffu64;
    n[3usize] = 0xfffffffeu64
}

fn bn_is_lt_prime_mask4(f: &mut [u64]) -> u64
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    make_prime(&mut tmp);
    let c: u64 = bn_sub4(&mut tmp, f, &mut tmp);
    0u64.wrapping_sub(c)
}

fn feq_mask(a: &mut [u64], b: &mut [u64]) -> u64
{
    let r: u64 = bn_is_eq_mask4(a, b);
    r
}

fn fadd(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut n: [u64; 4] = [0u64; 4usize];
    make_prime(&mut n);
    bn_add_mod4(res, &mut n, x, y)
}

fn fsub(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut n: [u64; 4] = [0u64; 4usize];
    make_prime(&mut n);
    crate::hacl::impl_p256_bignum::bn_sub_mod4(res, &mut n, x, y)
}

fn fnegate_conditional_vartime(f: &mut [u64], is_negate: bool) -> ()
{
    let mut zero: [u64; 4] = [0u64; 4usize];
    if is_negate { fsub(f, &mut zero, f) }
}

fn mont_reduction(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut n: [u64; 4] = [0u64; 4usize];
    make_prime(&mut n);
    let mut c0: u64 = 0u64;
    for i in 0u32..4u32
    {
        let qj: u64 = 1u64.wrapping_mul(x[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = x.split_at_mut((i as usize).wrapping_add(0usize));
        let mut c: u64 = 0u64;
        for i0 in 0u32..1u32
        {
            let a_i: u64 = (&mut n)[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut((4u32.wrapping_mul(i0) as usize).wrapping_add(0usize));
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c, res_i.1);
            let a_i0: u64 = (&mut n)[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, c, res_i0.1);
            let a_i1: u64 = (&mut n)[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, c, res_i1.1);
            let a_i2: u64 = (&mut n)[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, c, res_i2.1)
        };
        for i0 in 4u32..4u32
        {
            let a_i: u64 = (&mut n)[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut((i0 as usize).wrapping_add(0usize));
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c, res_i.1)
        };
        let r: u64 = c;
        let c1: u64 = r;
        let resb: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(4usize);
        let res_j0: u64 = res_j.0[4u32.wrapping_add(i) as usize];
        c0 = crate::lib::inttypes_intrinsics::add_carry_u64(c0, c1, res_j0, resb.1)
    };
    (res[0usize..0usize + 4usize]).copy_from_slice(&(&mut x[4usize..])[0usize..0usize + 4usize]);
    let c00: u64 = c0;
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c: u64 = 0u64;
    for i in 0u32..1u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = (&mut n)[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = (&mut n)[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = (&mut n)[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = (&mut n)[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in 4u32..4u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = (&mut n)[i as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    let c1: u64 = c;
    let c2: u64 = c00.wrapping_sub(c1);
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x1: u64 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x1
    }
}

fn fmul(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::hacl::impl_p256_bignum::bn_mul4(&mut tmp, x, y);
    mont_reduction(res, &mut tmp)
}

fn fsqr(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::hacl::impl_p256_bignum::bn_sqr4(&mut tmp, x);
    mont_reduction(res, &mut tmp)
}

fn from_mont(res: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    ((&mut tmp)[0usize..0usize + 4usize]).copy_from_slice(&a[0usize..0usize + 4usize]);
    mont_reduction(res, &mut tmp)
}

fn to_mont(res: &mut [u64], a: &mut [u64]) -> ()
{
    let mut r2modn: [u64; 4] = [0u64; 4usize];
    make_fmont_R2(&mut r2modn);
    fmul(res, a, &mut r2modn)
}

fn fmul_by_b_coeff(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut b_coeff: [u64; 4] = [0u64; 4usize];
    make_b_coeff(&mut b_coeff);
    fmul(res, &mut b_coeff, x)
}

fn fcube(res: &mut [u64], x: &mut [u64]) -> ()
{
    fsqr(res, x);
    fmul(res, res, x)
}

fn finv(res: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [u64; 16] = [0u64; 16usize];
    let x30: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let x2: (&mut [u64], &mut [u64]) = x30.1.split_at_mut(4usize);
    let tmp1: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(4usize);
    (tmp1.0[0usize..0usize + 4usize]).copy_from_slice(&a[0usize..0usize + 4usize]);
    for i in 0u32..1u32 { fsqr(tmp1.0, tmp1.0) };
    fmul(tmp1.0, tmp1.0, a);
    (x2.0[0usize..0usize + 4usize]).copy_from_slice(&tmp1.0[0usize..0usize + 4usize]);
    for i in 0u32..1u32 { fsqr(x2.0, x2.0) };
    fmul(x2.0, x2.0, a);
    (tmp2.0[0usize..0usize + 4usize]).copy_from_slice(&x2.0[0usize..0usize + 4usize]);
    for i in 0u32..3u32 { fsqr(tmp2.0, tmp2.0) };
    fmul(tmp2.0, tmp2.0, x2.0);
    (tmp2.1[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize]);
    for i in 0u32..6u32 { fsqr(tmp2.1, tmp2.1) };
    fmul(tmp2.1, tmp2.1, tmp2.0);
    (tmp2.0[0usize..0usize + 4usize]).copy_from_slice(&tmp2.1[0usize..0usize + 4usize]);
    for i in 0u32..3u32 { fsqr(tmp2.0, tmp2.0) };
    fmul(tmp2.0, tmp2.0, x2.0);
    (x2.0[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize]);
    for i in 0u32..15u32 { fsqr(x2.0, x2.0) };
    fmul(x2.0, x2.0, tmp2.0);
    (tmp2.0[0usize..0usize + 4usize]).copy_from_slice(&x2.0[0usize..0usize + 4usize]);
    for i in 0u32..2u32 { fsqr(tmp2.0, tmp2.0) };
    fmul(tmp2.0, tmp2.0, tmp1.0);
    (tmp1.0[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize]);
    for i in 0u32..32u32 { fsqr(tmp1.0, tmp1.0) };
    fmul(tmp1.0, tmp1.0, a);
    for i in 0u32..128u32 { fsqr(tmp1.0, tmp1.0) };
    fmul(tmp1.0, tmp1.0, tmp2.0);
    for i in 0u32..32u32 { fsqr(tmp1.0, tmp1.0) };
    fmul(tmp1.0, tmp1.0, tmp2.0);
    for i in 0u32..30u32 { fsqr(tmp1.0, tmp1.0) };
    fmul(tmp1.0, tmp1.0, x2.0);
    for i in 0u32..2u32 { fsqr(tmp1.0, tmp1.0) };
    fmul(tmp2.0, tmp1.0, a);
    (res[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize])
}

fn fsqrt(res: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    let tmp1: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(4usize);
    (tmp2.0[0usize..0usize + 4usize]).copy_from_slice(&a[0usize..0usize + 4usize]);
    for i in 0u32..1u32 { fsqr(tmp2.0, tmp2.0) };
    fmul(tmp2.0, tmp2.0, a);
    (tmp2.1[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize]);
    for i in 0u32..2u32 { fsqr(tmp2.1, tmp2.1) };
    fmul(tmp2.1, tmp2.1, tmp2.0);
    (tmp2.0[0usize..0usize + 4usize]).copy_from_slice(&tmp2.1[0usize..0usize + 4usize]);
    for i in 0u32..4u32 { fsqr(tmp2.0, tmp2.0) };
    fmul(tmp2.0, tmp2.0, tmp2.1);
    (tmp2.1[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize]);
    for i in 0u32..8u32 { fsqr(tmp2.1, tmp2.1) };
    fmul(tmp2.1, tmp2.1, tmp2.0);
    (tmp2.0[0usize..0usize + 4usize]).copy_from_slice(&tmp2.1[0usize..0usize + 4usize]);
    for i in 0u32..16u32 { fsqr(tmp2.0, tmp2.0) };
    fmul(tmp2.0, tmp2.0, tmp2.1);
    (tmp2.1[0usize..0usize + 4usize]).copy_from_slice(&tmp2.0[0usize..0usize + 4usize]);
    for i in 0u32..32u32 { fsqr(tmp2.1, tmp2.1) };
    fmul(tmp2.1, tmp2.1, a);
    for i in 0u32..96u32 { fsqr(tmp2.1, tmp2.1) };
    fmul(tmp2.1, tmp2.1, a);
    for i in 0u32..94u32 { fsqr(tmp2.1, tmp2.1) };
    (res[0usize..0usize + 4usize]).copy_from_slice(&tmp2.1[0usize..0usize + 4usize])
}

fn make_base_point(p: &mut [u64]) -> ()
{
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(4usize);
    make_g_x(y.0);
    make_g_y(z.0);
    make_fone(z.1)
}

fn make_point_at_inf(p: &mut [u64]) -> ()
{
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(4usize);
    make_fzero(y.0);
    make_fone(z.0);
    make_fzero(z.1)
}

fn is_point_at_inf_vartime(p: &mut [u64]) -> bool
{
    let pz: (&mut [u64], &mut [u64]) = p.split_at_mut(8usize);
    bn_is_zero_vartime4(pz.1)
}

fn to_aff_point(res: &mut [u64], p: &mut [u64]) -> ()
{
    let mut zinv: [u64; 4] = [0u64; 4usize];
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    let pz: (&mut [u64], &mut [u64]) = py.1.split_at_mut(4usize);
    let x: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    finv(&mut zinv, pz.1);
    fmul(y.0, py.0, &mut zinv);
    fmul(y.1, pz.0, &mut zinv);
    from_mont(y.0, y.0);
    from_mont(y.1, y.1)
}

fn to_aff_point_x(res: &mut [u64], p: &mut [u64]) -> ()
{
    let mut zinv: [u64; 4] = [0u64; 4usize];
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let pz: (&mut [u64], &mut [u64]) = px.1.split_at_mut(8usize);
    finv(&mut zinv, pz.1);
    fmul(res, pz.0, &mut zinv);
    from_mont(res, res)
}

fn to_proj_point(res: &mut [u64], p: &mut [u64]) -> ()
{
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    let rx: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let ry: (&mut [u64], &mut [u64]) = rx.1.split_at_mut(4usize);
    let rz: (&mut [u64], &mut [u64]) = ry.1.split_at_mut(4usize);
    to_mont(ry.0, py.0);
    to_mont(rz.0, py.1);
    make_fone(rz.1)
}

fn is_on_curve_vartime(p: &mut [u64]) -> bool
{
    let mut rp: [u64; 4] = [0u64; 4usize];
    let mut tx: [u64; 4] = [0u64; 4usize];
    let mut ty: [u64; 4] = [0u64; 4usize];
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    to_mont(&mut tx, py.0);
    to_mont(&mut ty, py.1);
    let mut tmp: [u64; 4] = [0u64; 4usize];
    fcube(&mut rp, &mut tx);
    make_a_coeff(&mut tmp);
    fmul(&mut tmp, &mut tmp, &mut tx);
    fadd(&mut rp, &mut tmp, &mut rp);
    make_b_coeff(&mut tmp);
    fadd(&mut rp, &mut tmp, &mut rp);
    fsqr(&mut ty, &mut ty);
    let r: u64 = feq_mask(&mut ty, &mut rp);
    let r0: bool = r == 0xFFFFFFFFFFFFFFFFu64;
    r0
}

fn aff_point_store(res: &mut [u8], p: &mut [u64]) -> ()
{
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(4usize);
    bn2_to_bytes_be4(res, py.0, py.1)
}

fn point_store(res: &mut [u8], p: &mut [u64]) -> ()
{
    let mut aff_p: [u64; 8] = [0u64; 8usize];
    to_aff_point(&mut aff_p, p);
    aff_point_store(res, &mut aff_p)
}

fn aff_point_load_vartime(p: &mut [u64], b: &mut [u8]) -> bool
{
    let p_x: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    let p_y: (&mut [u8], &mut [u8]) = p_x.1.split_at_mut(32usize);
    let bn_p_x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let bn_p_y: (&mut [u64], &mut [u64]) = bn_p_x.1.split_at_mut(4usize);
    bn_from_bytes_be4(bn_p_y.0, p_y.0);
    bn_from_bytes_be4(bn_p_y.1, p_y.1);
    let px: (&mut [u64], &mut [u64]) = bn_p_y.0.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = bn_p_y.1.split_at_mut(0usize);
    let lessX: u64 = bn_is_lt_prime_mask4(px.1);
    let lessY: u64 = bn_is_lt_prime_mask4(py.1);
    let res: u64 = lessX & lessY;
    let is_xy_valid: bool = res == 0xFFFFFFFFFFFFFFFFu64;
    if ! is_xy_valid { falsebool } else { is_on_curve_vartime(px.0) }
}

fn load_point_vartime(p: &mut [u64], b: &mut [u8]) -> bool
{
    let mut p_aff: [u64; 8] = [0u64; 8usize];
    let res: bool = aff_point_load_vartime(&mut p_aff, b);
    if res { to_proj_point(p, &mut p_aff) };
    res
}

fn aff_point_decompress_vartime(x: &mut [u64], y: &mut [u64], s: &mut [u8]) -> bool
{
    let s0: u8 = s[0usize];
    let s01: u8 = s0;
    if ! (s01 == 0x02u8 || s01 == 0x03u8)
    { falsebool }
    else
    {
        let xb: (&mut [u8], &mut [u8]) = s.split_at_mut(1usize);
        bn_from_bytes_be4(x, xb.1);
        let is_x_valid: u64 = bn_is_lt_prime_mask4(x);
        let is_x_valid1: bool = is_x_valid == 0xFFFFFFFFFFFFFFFFu64;
        let is_y_odd: bool = s01 == 0x03u8;
        if ! is_x_valid1
        { falsebool }
        else
        {
            let mut y2M: [u64; 4] = [0u64; 4usize];
            let mut xM: [u64; 4] = [0u64; 4usize];
            let mut yM: [u64; 4] = [0u64; 4usize];
            to_mont(&mut xM, x);
            let mut tmp: [u64; 4] = [0u64; 4usize];
            fcube(&mut y2M, &mut xM);
            make_a_coeff(&mut tmp);
            fmul(&mut tmp, &mut tmp, &mut xM);
            fadd(&mut y2M, &mut tmp, &mut y2M);
            make_b_coeff(&mut tmp);
            fadd(&mut y2M, &mut tmp, &mut y2M);
            fsqrt(&mut yM, &mut y2M);
            from_mont(y, &mut yM);
            fsqr(&mut yM, &mut yM);
            let r: u64 = feq_mask(&mut yM, &mut y2M);
            let is_y_valid: bool = r == 0xFFFFFFFFFFFFFFFFu64;
            let is_y_valid0: bool = is_y_valid;
            if ! is_y_valid0
            { falsebool }
            else
            {
                let is_y_odd1: u64 = y[0usize] & 1u64;
                let is_y_odd2: bool = is_y_odd1 == 1u64;
                fnegate_conditional_vartime(y, is_y_odd2 != is_y_odd);
                truebool
            }
        }
    }
}

fn point_double(res: &mut [u64], p: &mut [u64]) -> ()
{
    let mut tmp: [u64; 20] = [0u64; 20usize];
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let z: (&mut [u64], &mut [u64]) = x.1.split_at_mut(8usize);
    let x3: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(4usize);
    let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(4usize);
    let t0: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(4usize);
    let t2: (&mut [u64], &mut [u64]) = t1.1.split_at_mut(4usize);
    let t3: (&mut [u64], &mut [u64]) = t2.1.split_at_mut(4usize);
    let t4: (&mut [u64], &mut [u64]) = t3.1.split_at_mut(4usize);
    let x1: (&mut [u64], &mut [u64]) = z.0.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(4usize);
    let z1: (&mut [u64], &mut [u64]) = z.1.split_at_mut(0usize);
    fsqr(t1.0, y.0);
    fsqr(t2.0, y.1);
    fsqr(t3.0, z1.1);
    fmul(t4.0, y.0, y.1);
    fadd(t4.0, t4.0, t4.0);
    fmul(t4.1, y.1, z1.1);
    fmul(z3.1, x1.0, z1.0);
    fadd(z3.1, z3.1, z3.1);
    fmul_by_b_coeff(z3.0, t3.0);
    fsub(z3.0, z3.0, z3.1);
    fadd(y3.0, z3.0, z3.0);
    fadd(z3.0, y3.0, z3.0);
    fsub(y3.0, t2.0, z3.0);
    fadd(z3.0, t2.0, z3.0);
    fmul(z3.0, y3.0, z3.0);
    fmul(y3.0, y3.0, t4.0);
    fadd(t4.0, t3.0, t3.0);
    fadd(t3.0, t3.0, t4.0);
    fmul_by_b_coeff(z3.1, z3.1);
    fsub(z3.1, z3.1, t3.0);
    fsub(z3.1, z3.1, t1.0);
    fadd(t4.0, z3.1, z3.1);
    fadd(z3.1, z3.1, t4.0);
    fadd(t4.0, t1.0, t1.0);
    fadd(t1.0, t4.0, t1.0);
    fsub(t1.0, t1.0, t3.0);
    fmul(t1.0, t1.0, z3.1);
    fadd(z3.0, z3.0, t1.0);
    fadd(t1.0, t4.1, t4.1);
    fmul(z3.1, t1.0, z3.1);
    fsub(y3.0, y3.0, z3.1);
    fmul(z3.1, t1.0, t2.0);
    fadd(z3.1, z3.1, z3.1);
    fadd(z3.1, z3.1, z3.1)
}

fn point_add(res: &mut [u64], p: &mut [u64], q: &mut [u64]) -> ()
{
    let mut tmp: [u64; 36] = [0u64; 36usize];
    let t0: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
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
    fmul(t11.0, y1.0, y2.0);
    fmul(t2.0, z1.0, z2.0);
    fmul(t3.0, z1.1, z2.1);
    fadd(t4.0, y1.0, z1.0);
    fadd(t5.0, y2.0, z2.0);
    fmul(t4.0, t4.0, t5.0);
    fadd(t5.0, t11.0, t2.0);
    let y10: (&mut [u64], &mut [u64]) = z1.0.split_at_mut(0usize);
    let z10: (&mut [u64], &mut [u64]) = z1.1.split_at_mut(0usize);
    let y20: (&mut [u64], &mut [u64]) = z2.0.split_at_mut(0usize);
    let z20: (&mut [u64], &mut [u64]) = z2.1.split_at_mut(0usize);
    fsub(t4.0, t4.0, t5.0);
    fadd(t5.0, y10.1, z10.1);
    fadd(t5.1, y20.1, z20.1);
    fmul(t5.0, t5.0, t5.1);
    fadd(t5.1, t2.0, t3.0);
    fsub(t5.0, t5.0, t5.1);
    let x10: (&mut [u64], &mut [u64]) = y1.0.split_at_mut(0usize);
    let z11: (&mut [u64], &mut [u64]) = z10.1.split_at_mut(0usize);
    let x20: (&mut [u64], &mut [u64]) = y2.0.split_at_mut(0usize);
    let z21: (&mut [u64], &mut [u64]) = z20.1.split_at_mut(0usize);
    fadd(y3.0, x10.1, z11.1);
    fadd(z3.0, x20.1, z21.1);
    fmul(y3.0, y3.0, z3.0);
    fadd(z3.0, t11.0, t3.0);
    fsub(z3.0, y3.0, z3.0);
    fmul_by_b_coeff(z3.1, t3.0);
    fsub(y3.0, z3.0, z3.1);
    fadd(z3.1, y3.0, y3.0);
    fadd(y3.0, y3.0, z3.1);
    fsub(z3.1, t2.0, y3.0);
    fadd(y3.0, t2.0, y3.0);
    fmul_by_b_coeff(z3.0, z3.0);
    fadd(t2.0, t3.0, t3.0);
    fadd(t3.0, t2.0, t3.0);
    fsub(z3.0, z3.0, t3.0);
    fsub(z3.0, z3.0, t11.0);
    fadd(t2.0, z3.0, z3.0);
    fadd(z3.0, t2.0, z3.0);
    fadd(t2.0, t11.0, t11.0);
    fadd(t11.0, t2.0, t11.0);
    fsub(t11.0, t11.0, t3.0);
    fmul(t2.0, t5.0, z3.0);
    fmul(t3.0, t11.0, z3.0);
    fmul(z3.0, y3.0, z3.1);
    fadd(z3.0, z3.0, t3.0);
    fmul(y3.0, t4.0, y3.0);
    fsub(y3.0, y3.0, t2.0);
    fmul(z3.1, t5.0, z3.1);
    fmul(t2.0, t4.0, t11.0);
    fadd(z3.1, z3.1, t2.0);
    (res[0usize..0usize + 12usize]).copy_from_slice(&y3.0[0usize..0usize + 12usize])
}

fn precomp_get_consttime(table: &[u64], bits_l: u64, tmp: &mut [u64]) -> ()
{
    (tmp[0usize..0usize + 12usize]).copy_from_slice(
        &(&mut table[0usize..] as &mut [u64])[0usize..0usize + 12usize]
    );
    for i in 0u32..15u32
    {
        let c: u64 = crate::fstar::uint64::eq_mask(bits_l, i.wrapping_add(1u32) as u64);
        let res_j: (&[u64], &[u64]) =
            table.split_at_mut(
                (i.wrapping_add(1u32).wrapping_mul(12u32) as usize).wrapping_add(0usize)
            );
        for i0 in 0u32..12u32
        {
            let os: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
            let x: u64 = c & res_j.1[i0 as usize] | ! c & os.1[i0 as usize];
            os.1[i0 as usize] = x
        }
    }
}

fn bn_is_lt_order_mask4(f: &mut [u64]) -> u64
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    make_order(&mut tmp);
    let c: u64 = bn_sub4(&mut tmp, f, &mut tmp);
    0u64.wrapping_sub(c)
}

fn bn_is_lt_order_and_gt_zero_mask4(f: &mut [u64]) -> u64
{
    let is_lt_order: u64 = bn_is_lt_order_mask4(f);
    let is_eq_zero: u64 = bn_is_zero_mask4(f);
    is_lt_order & ! is_eq_zero
}

fn qmod_short(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    make_order(&mut tmp);
    let c: u64 = bn_sub4(&mut tmp, x, &mut tmp);
    bn_cmovznz4(res, c, &mut tmp, x)
}

fn qadd(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut n: [u64; 4] = [0u64; 4usize];
    make_order(&mut n);
    bn_add_mod4(res, &mut n, x, y)
}

fn qmont_reduction(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut n: [u64; 4] = [0u64; 4usize];
    make_order(&mut n);
    let mut c0: u64 = 0u64;
    for i in 0u32..4u32
    {
        let qj: u64 = 0xccd1c8aaee00bc4fu64.wrapping_mul(x[i as usize]);
        let res_j: (&mut [u64], &mut [u64]) = x.split_at_mut((i as usize).wrapping_add(0usize));
        let mut c: u64 = 0u64;
        for i0 in 0u32..1u32
        {
            let a_i: u64 = (&mut n)[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut((4u32.wrapping_mul(i0) as usize).wrapping_add(0usize));
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c, res_i.1);
            let a_i0: u64 = (&mut n)[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i0, qj, c, res_i0.1);
            let a_i1: u64 = (&mut n)[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i1, qj, c, res_i1.1);
            let a_i2: u64 = (&mut n)[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i2, qj, c, res_i2.1)
        };
        for i0 in 4u32..4u32
        {
            let a_i: u64 = (&mut n)[i0 as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res_j.1.split_at_mut((i0 as usize).wrapping_add(0usize));
            c = crate::hacl::bignum_base::mul_wide_add2_u64(a_i, qj, c, res_i.1)
        };
        let r: u64 = c;
        let c1: u64 = r;
        let resb: (&mut [u64], &mut [u64]) = res_j.1.split_at_mut(4usize);
        let res_j0: u64 = res_j.0[4u32.wrapping_add(i) as usize];
        c0 = crate::lib::inttypes_intrinsics::add_carry_u64(c0, c1, res_j0, resb.1)
    };
    (res[0usize..0usize + 4usize]).copy_from_slice(&(&mut x[4usize..])[0usize..0usize + 4usize]);
    let c00: u64 = c0;
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut c: u64 = 0u64;
    for i in 0u32..1u32
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = (&mut n)[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = (&mut n)[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = (&mut n)[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = (&mut n)[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in 4u32..4u32
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = (&mut n)[i as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut((i as usize).wrapping_add(0usize));
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    let c1: u64 = c;
    let c2: u64 = c00.wrapping_sub(c1);
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x1: u64 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x1
    }
}

fn from_qmont(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    ((&mut tmp)[0usize..0usize + 4usize]).copy_from_slice(&x[0usize..0usize + 4usize]);
    qmont_reduction(res, &mut tmp)
}

fn qmul(res: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::hacl::impl_p256_bignum::bn_mul4(&mut tmp, x, y);
    qmont_reduction(res, &mut tmp)
}

fn qsqr(res: &mut [u64], x: &mut [u64]) -> ()
{
    let mut tmp: [u64; 8] = [0u64; 8usize];
    crate::hacl::impl_p256_bignum::bn_sqr4(&mut tmp, x);
    qmont_reduction(res, &mut tmp)
}

pub fn ecp256dh_i(public_key: &mut [u8], private_key: &mut [u8]) -> bool
{
    let mut tmp: [u64; 16] = [0u64; 16usize];
    let sk: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let pk: (&mut [u64], &mut [u64]) = sk.1.split_at_mut(4usize);
    bn_from_bytes_be4(pk.0, private_key);
    let is_b_valid: u64 = bn_is_lt_order_and_gt_zero_mask4(pk.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = pk.0.split_at_mut(0usize);
        let uu____0: u64 = (&mut oneq)[i as usize];
        let x: u64 = uu____0 ^ is_b_valid & (os.1[i as usize] ^ uu____0);
        os.1[i as usize] = x
    };
    let is_sk_valid: u64 = is_b_valid;
    crate::hacl::impl_p256_pointmul::point_mul_g(pk.1, pk.0);
    point_store(public_key, pk.1);
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64
}

pub fn ecp256dh_r(shared_secret: &mut [u8], their_pubkey: &mut [u8], private_key: &mut [u8]) ->
    bool
{
    let mut tmp: [u64; 16] = [0u64; 16usize];
    let sk: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let pk: (&mut [u64], &mut [u64]) = sk.1.split_at_mut(4usize);
    let is_pk_valid: bool = load_point_vartime(pk.1, their_pubkey);
    bn_from_bytes_be4(pk.0, private_key);
    let is_b_valid: u64 = bn_is_lt_order_and_gt_zero_mask4(pk.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = pk.0.split_at_mut(0usize);
        let uu____0: u64 = (&mut oneq)[i as usize];
        let x: u64 = uu____0 ^ is_b_valid & (os.1[i as usize] ^ uu____0);
        os.1[i as usize] = x
    };
    let is_sk_valid: u64 = is_b_valid;
    let mut ss_proj: [u64; 12] = [0u64; 12usize];
    if is_pk_valid
    {
        crate::hacl::impl_p256_pointmul::point_mul(&mut ss_proj, pk.0, pk.1);
        point_store(shared_secret, &mut ss_proj)
    };
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64 && is_pk_valid
}

fn qinv(res: &mut [u64], r: &mut [u64]) -> ()
{
    let mut tmp: [u64; 28] = [0u64; 28usize];
    let x6: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let x_11: (&mut [u64], &mut [u64]) = x6.1.split_at_mut(4usize);
    let x_101: (&mut [u64], &mut [u64]) = x_11.1.split_at_mut(4usize);
    let x_111: (&mut [u64], &mut [u64]) = x_101.1.split_at_mut(4usize);
    let x_1111: (&mut [u64], &mut [u64]) = x_111.1.split_at_mut(4usize);
    let x_10101: (&mut [u64], &mut [u64]) = x_1111.1.split_at_mut(4usize);
    let x_101111: (&mut [u64], &mut [u64]) = x_10101.1.split_at_mut(4usize);
    (x_11.0[0usize..0usize + 4usize]).copy_from_slice(&r[0usize..0usize + 4usize]);
    for i in 0u32..1u32 { qsqr(x_11.0, x_11.0) };
    qmul(x_101.0, x_11.0, r);
    qmul(x_111.0, x_11.0, x_101.0);
    qmul(x_1111.0, x_11.0, x_111.0);
    (x_11.0[0usize..0usize + 4usize]).copy_from_slice(&x_111.0[0usize..0usize + 4usize]);
    for i in 0u32..1u32 { qsqr(x_11.0, x_11.0) };
    qmul(x_10101.0, x_111.0, x_11.0);
    for i in 0u32..1u32 { qsqr(x_11.0, x_11.0) };
    qmul(x_101111.0, x_11.0, r);
    (x_11.0[0usize..0usize + 4usize]).copy_from_slice(&x_101111.0[0usize..0usize + 4usize]);
    for i in 0u32..1u32 { qsqr(x_11.0, x_11.0) };
    qmul(x_101111.1, x_111.0, x_11.0);
    qmul(x_11.0, x_101111.0, x_11.0);
    let mut tmp1: [u64; 4] = [0u64; 4usize];
    for i in 0u32..2u32 { qsqr(x_11.0, x_11.0) };
    qmul(x_11.0, x_11.0, x_101.0);
    ((&mut tmp1)[0usize..0usize + 4usize]).copy_from_slice(&x_11.0[0usize..0usize + 4usize]);
    for i in 0u32..8u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_11.0);
    (x_11.0[0usize..0usize + 4usize]).copy_from_slice(&(&mut tmp1)[0usize..0usize + 4usize]);
    for i in 0u32..16u32 { qsqr(x_11.0, x_11.0) };
    qmul(x_11.0, x_11.0, &mut tmp1);
    ((&mut tmp1)[0usize..0usize + 4usize]).copy_from_slice(&x_11.0[0usize..0usize + 4usize]);
    for i in 0u32..64u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_11.0);
    for i in 0u32..32u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_11.0);
    for i in 0u32..6u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101111.1);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_1111.0);
    for i in 0u32..4u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_10101.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101111.0);
    for i in 0u32..4u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_111.0);
    for i in 0u32..3u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_111.0);
    for i in 0u32..3u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_111.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_1111.0);
    for i in 0u32..9u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101111.1);
    for i in 0u32..6u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_10101.0);
    for i in 0u32..2u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, r);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, r);
    for i in 0u32..6u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_10101.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_1111.0);
    for i in 0u32..4u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_1111.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_1111.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_111.0);
    for i in 0u32..3u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101.0);
    for i in 0u32..10u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101111.1);
    for i in 0u32..2u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101.0);
    for i in 0u32..5u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101.0);
    for i in 0u32..3u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, r);
    for i in 0u32..7u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_101111.0);
    for i in 0u32..6u32 { qsqr(&mut tmp1, &mut tmp1) };
    qmul(&mut tmp1, &mut tmp1, x_10101.0);
    (x_11.0[0usize..0usize + 4usize]).copy_from_slice(&(&mut tmp1)[0usize..0usize + 4usize]);
    (res[0usize..0usize + 4usize]).copy_from_slice(&x_11.0[0usize..0usize + 4usize])
}

fn qmul_mont(sinv: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    from_qmont(&mut tmp, b);
    qmul(res, sinv, &mut tmp)
}

fn ecdsa_verify_msg_as_qelem(
    m_q: &mut [u64],
    public_key: &mut [u8],
    signature_r: &mut [u8],
    signature_s: &mut [u8]
) ->
    bool
{
    let mut tmp: [u64; 28] = [0u64; 28usize];
    let pk: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let r_q: (&mut [u64], &mut [u64]) = pk.1.split_at_mut(12usize);
    let s_q: (&mut [u64], &mut [u64]) = r_q.1.split_at_mut(4usize);
    let u1: (&mut [u64], &mut [u64]) = s_q.1.split_at_mut(4usize);
    let u2: (&mut [u64], &mut [u64]) = u1.1.split_at_mut(4usize);
    let is_pk_valid: bool = load_point_vartime(r_q.0, public_key);
    bn_from_bytes_be4(s_q.0, signature_r);
    bn_from_bytes_be4(u1.0, signature_s);
    let is_r_valid: u64 = bn_is_lt_order_and_gt_zero_mask4(s_q.0);
    let is_s_valid: u64 = bn_is_lt_order_and_gt_zero_mask4(u1.0);
    let is_rs_valid: bool =
        is_r_valid == 0xFFFFFFFFFFFFFFFFu64 && is_s_valid == 0xFFFFFFFFFFFFFFFFu64;
    if ! (is_pk_valid && is_rs_valid)
    { falsebool }
    else
    {
        let mut sinv: [u64; 4] = [0u64; 4usize];
        qinv(&mut sinv, u1.0);
        qmul_mont(&mut sinv, m_q, u2.0);
        qmul_mont(&mut sinv, s_q.0, u2.1);
        let mut res: [u64; 12] = [0u64; 12usize];
        crate::hacl::impl_p256_pointmul::point_mul_double_g(&mut res, u2.0, u2.1, r_q.0);
        if is_point_at_inf_vartime(&mut res)
        { falsebool }
        else
        {
            let mut x: [u64; 4] = [0u64; 4usize];
            to_aff_point_x(&mut x, &mut res);
            qmod_short(&mut x, &mut x);
            let res1: bool = bn_is_eq_vartime4(&mut x, s_q.0);
            res1
        }
    }
}

fn ecdsa_sign_msg_as_qelem(
    signature: &mut [u8],
    m_q: &mut [u64],
    private_key: &mut [u8],
    nonce: &mut [u8]
) ->
    bool
{
    let mut rsdk_q: [u64; 16] = [0u64; 16usize];
    let r_q: (&mut [u64], &mut [u64]) = (&mut rsdk_q).split_at_mut(0usize);
    let s_q: (&mut [u64], &mut [u64]) = r_q.1.split_at_mut(4usize);
    let d_a: (&mut [u64], &mut [u64]) = s_q.1.split_at_mut(4usize);
    let k_q: (&mut [u64], &mut [u64]) = d_a.1.split_at_mut(4usize);
    bn_from_bytes_be4(k_q.0, private_key);
    let is_b_valid: u64 = bn_is_lt_order_and_gt_zero_mask4(k_q.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = k_q.0.split_at_mut(0usize);
        let uu____0: u64 = (&mut oneq)[i as usize];
        let x: u64 = uu____0 ^ is_b_valid & (os.1[i as usize] ^ uu____0);
        os.1[i as usize] = x
    };
    let is_sk_valid: u64 = is_b_valid;
    bn_from_bytes_be4(k_q.1, nonce);
    let is_b_valid0: u64 = bn_is_lt_order_and_gt_zero_mask4(k_q.1);
    let mut oneq0: [u64; 4] = [0u64; 4usize];
    (&mut oneq0)[0usize] = 1u64;
    (&mut oneq0)[1usize] = 0u64;
    (&mut oneq0)[2usize] = 0u64;
    (&mut oneq0)[3usize] = 0u64;
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = k_q.1.split_at_mut(0usize);
        let uu____1: u64 = (&mut oneq0)[i as usize];
        let x: u64 = uu____1 ^ is_b_valid0 & (os.1[i as usize] ^ uu____1);
        os.1[i as usize] = x
    };
    let is_nonce_valid: u64 = is_b_valid0;
    let are_sk_nonce_valid: u64 = is_sk_valid & is_nonce_valid;
    let mut p: [u64; 12] = [0u64; 12usize];
    crate::hacl::impl_p256_pointmul::point_mul_g(&mut p, k_q.1);
    to_aff_point_x(s_q.0, &mut p);
    qmod_short(s_q.0, s_q.0);
    let mut kinv: [u64; 4] = [0u64; 4usize];
    qinv(&mut kinv, k_q.1);
    qmul(d_a.0, s_q.0, k_q.0);
    from_qmont(m_q, m_q);
    qadd(d_a.0, m_q, d_a.0);
    qmul(d_a.0, &mut kinv, d_a.0);
    bn2_to_bytes_be4(signature, s_q.0, d_a.0);
    let is_r_zero: u64 = bn_is_zero_mask4(s_q.0);
    let is_s_zero: u64 = bn_is_zero_mask4(d_a.0);
    let m: u64 = are_sk_nonce_valid & (! is_r_zero & ! is_s_zero);
    let res: bool = m == 0xFFFFFFFFFFFFFFFFu64;
    res
}

pub fn validate_public_key(public_key: &mut [u8]) -> bool
{
    let mut point_jac: [u64; 12] = [0u64; 12usize];
    let res: bool = load_point_vartime(&mut point_jac, public_key);
    res
}

pub fn validate_private_key(private_key: &mut [u8]) -> bool
{
    let mut bn_sk: [u64; 4] = [0u64; 4usize];
    bn_from_bytes_be4(&mut bn_sk, private_key);
    let res: u64 = bn_is_lt_order_and_gt_zero_mask4(&mut bn_sk);
    res == 0xFFFFFFFFFFFFFFFFu64
}

pub fn uncompressed_to_raw(pk: &mut [u8], pk_raw: &mut [u8]) -> bool
{
    let pk0: u8 = pk[0usize];
    if pk0 != 0x04u8
    { falsebool }
    else
    {
        (pk_raw[0usize..0usize + 64usize]).copy_from_slice(
            &(&mut pk[1usize..])[0usize..0usize + 64usize]
        );
        truebool
    }
}

pub fn compressed_to_raw(pk: &mut [u8], pk_raw: &mut [u8]) -> bool
{
    let mut xa: [u64; 4] = [0u64; 4usize];
    let mut ya: [u64; 4] = [0u64; 4usize];
    let pk_xb: (&mut [u8], &mut [u8]) = pk.split_at_mut(1usize);
    let b: bool = aff_point_decompress_vartime(&mut xa, &mut ya, pk_xb.0);
    if b
    {
        (pk_raw[0usize..0usize + 32usize]).copy_from_slice(&pk_xb.1[0usize..0usize + 32usize]);
        crate::hacl::impl_p256_bignum::bn_to_bytes_be4(&mut pk_raw[32usize..], &mut ya)
    };
    b
}

pub fn raw_to_uncompressed(pk_raw: &mut [u8], pk: &mut [u8]) -> ()
{
    pk[0usize] = 0x04u8;
    (pk[1usize..1usize + 64usize]).copy_from_slice(&pk_raw[0usize..0usize + 64usize])
}

pub fn raw_to_compressed(pk_raw: &mut [u8], pk: &mut [u8]) -> ()
{
    let pk_x: (&mut [u8], &mut [u8]) = pk_raw.split_at_mut(0usize);
    let pk_y: (&mut [u8], &mut [u8]) = pk_x.1.split_at_mut(32usize);
    let mut bn_f: [u64; 4] = [0u64; 4usize];
    bn_from_bytes_be4(&mut bn_f, pk_y.1);
    let is_odd_f: u64 = (&mut bn_f)[0usize] & 1u64;
    pk[0usize] = (is_odd_f as u8).wrapping_add(0x02u8);
    (pk[1usize..1usize + 32usize]).copy_from_slice(&pk_y.0[0usize..0usize + 32usize])
}

pub fn dh_initiator(public_key: &mut [u8], private_key: &mut [u8]) -> bool
{ ecp256dh_i(public_key, private_key) }

pub fn dh_responder(shared_secret: &mut [u8], their_pubkey: &mut [u8], private_key: &mut [u8]) ->
    bool
{ ecp256dh_r(shared_secret, their_pubkey, private_key) }
