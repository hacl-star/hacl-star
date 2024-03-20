#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn fsum(out: &mut [u64], a: &mut [u64], b: &mut [u64]) -> ()
{ crate::hacl::bignum25519_51::fadd(out, a, b) }

#[inline] fn fdifference(out: &mut [u64], a: &mut [u64], b: &mut [u64]) -> ()
{ crate::hacl::bignum25519_51::fsub(out, a, b) }

pub fn reduce_513(a: &mut [u64]) -> ()
{
    let f0: u64 = a[0usize];
    let f1: u64 = a[1usize];
    let f2: u64 = a[2usize];
    let f3: u64 = a[3usize];
    let f4: u64 = a[4usize];
    let l·: u64 = f0.wrapping_add(0u64);
    let tmp0: u64 = l· & 0x7ffffffffffffu64;
    let c0: u64 = l·.wrapping_shr(51u32);
    let l·0: u64 = f1.wrapping_add(c0);
    let tmp1: u64 = l·0 & 0x7ffffffffffffu64;
    let c1: u64 = l·0.wrapping_shr(51u32);
    let l·1: u64 = f2.wrapping_add(c1);
    let tmp2: u64 = l·1 & 0x7ffffffffffffu64;
    let c2: u64 = l·1.wrapping_shr(51u32);
    let l·2: u64 = f3.wrapping_add(c2);
    let tmp3: u64 = l·2 & 0x7ffffffffffffu64;
    let c3: u64 = l·2.wrapping_shr(51u32);
    let l·3: u64 = f4.wrapping_add(c3);
    let tmp4: u64 = l·3 & 0x7ffffffffffffu64;
    let c4: u64 = l·3.wrapping_shr(51u32);
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    a[0usize] = tmp0·;
    a[1usize] = tmp1.wrapping_add(c5);
    a[2usize] = tmp2;
    a[3usize] = tmp3;
    a[4usize] = tmp4
}

#[inline] fn fmul(output: &mut [u64], input: &mut [u64], input2: &mut [u64]) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 10] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 10usize];
    crate::hacl::bignum25519_51::fmul(output, input, input2, &mut tmp)
}

#[inline] fn times_2(out: &mut [u64], a: &mut [u64]) -> ()
{
    let a0: u64 = a[0usize];
    let a1: u64 = a[1usize];
    let a2: u64 = a[2usize];
    let a3: u64 = a[3usize];
    let a4: u64 = a[4usize];
    let o0: u64 = 2u64.wrapping_mul(a0);
    let o1: u64 = 2u64.wrapping_mul(a1);
    let o2: u64 = 2u64.wrapping_mul(a2);
    let o3: u64 = 2u64.wrapping_mul(a3);
    let o4: u64 = 2u64.wrapping_mul(a4);
    out[0usize] = o0;
    out[1usize] = o1;
    out[2usize] = o2;
    out[3usize] = o3;
    out[4usize] = o4
}

#[inline] fn times_d(out: &mut [u64], a: &mut [u64]) -> ()
{
    let mut d: [u64; 5] = [0u64; 5usize];
    (&mut d)[0usize] = 0x00034dca135978a3u64;
    (&mut d)[1usize] = 0x0001a8283b156ebdu64;
    (&mut d)[2usize] = 0x0005e7a26001c029u64;
    (&mut d)[3usize] = 0x000739c663a03cbbu64;
    (&mut d)[4usize] = 0x00052036cee2b6ffu64;
    fmul(out, &mut d, a)
}

#[inline] fn times_2d(out: &mut [u64], a: &mut [u64]) -> ()
{
    let mut d2: [u64; 5] = [0u64; 5usize];
    (&mut d2)[0usize] = 0x00069b9426b2f159u64;
    (&mut d2)[1usize] = 0x00035050762add7au64;
    (&mut d2)[2usize] = 0x0003cf44c0038052u64;
    (&mut d2)[3usize] = 0x0006738cc7407977u64;
    (&mut d2)[4usize] = 0x0002406d9dc56dffu64;
    fmul(out, &mut d2, a)
}

#[inline] fn fsquare(out: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 5] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 5usize];
    crate::hacl::bignum25519_51::fsqr(out, a, &mut tmp)
}

#[inline] fn fsquare_times(output: &mut [u64], input: &mut [u64], count: u32) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 5] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 5usize];
    crate::hacl::curve25519_51::fsquare_times(output, input, &mut tmp, count)
}

#[inline] fn fsquare_times_inplace(output: &mut [u64], count: u32) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 5] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 5usize];
    let mut input: [u64; 5] = [0u64; 5usize];
    ((&mut input)[0usize..5usize]).copy_from_slice(&output[0usize..5usize]);
    crate::hacl::curve25519_51::fsquare_times(output, &mut input, &mut tmp, count)
}

pub fn inverse(out: &mut [u64], a: &mut [u64]) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 10] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 10usize];
    crate::hacl::curve25519_51::finv(out, a, &mut tmp)
}

#[inline] fn reduce(out: &mut [u64]) -> ()
{
    let o0: u64 = out[0usize];
    let o1: u64 = out[1usize];
    let o2: u64 = out[2usize];
    let o3: u64 = out[3usize];
    let o4: u64 = out[4usize];
    let l·: u64 = o0.wrapping_add(0u64);
    let tmp0: u64 = l· & 0x7ffffffffffffu64;
    let c0: u64 = l·.wrapping_shr(51u32);
    let l·0: u64 = o1.wrapping_add(c0);
    let tmp1: u64 = l·0 & 0x7ffffffffffffu64;
    let c1: u64 = l·0.wrapping_shr(51u32);
    let l·1: u64 = o2.wrapping_add(c1);
    let tmp2: u64 = l·1 & 0x7ffffffffffffu64;
    let c2: u64 = l·1.wrapping_shr(51u32);
    let l·2: u64 = o3.wrapping_add(c2);
    let tmp3: u64 = l·2 & 0x7ffffffffffffu64;
    let c3: u64 = l·2.wrapping_shr(51u32);
    let l·3: u64 = o4.wrapping_add(c3);
    let tmp4: u64 = l·3 & 0x7ffffffffffffu64;
    let c4: u64 = l·3.wrapping_shr(51u32);
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let f0: u64 = tmp0·;
    let f1: u64 = tmp1.wrapping_add(c5);
    let f2: u64 = tmp2;
    let f3: u64 = tmp3;
    let f4: u64 = tmp4;
    let m0: u64 = crate::fstar::uint64::gte_mask(f0, 0x7ffffffffffedu64);
    let m1: u64 = crate::fstar::uint64::eq_mask(f1, 0x7ffffffffffffu64);
    let m2: u64 = crate::fstar::uint64::eq_mask(f2, 0x7ffffffffffffu64);
    let m3: u64 = crate::fstar::uint64::eq_mask(f3, 0x7ffffffffffffu64);
    let m4: u64 = crate::fstar::uint64::eq_mask(f4, 0x7ffffffffffffu64);
    let mask: u64 = m0 & m1 & m2 & m3 & m4;
    let f0·: u64 = f0.wrapping_sub(mask & 0x7ffffffffffedu64);
    let f1·: u64 = f1.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f2·: u64 = f2.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f3·: u64 = f3.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f4·: u64 = f4.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f01: u64 = f0·;
    let f11: u64 = f1·;
    let f21: u64 = f2·;
    let f31: u64 = f3·;
    let f41: u64 = f4·;
    out[0usize] = f01;
    out[1usize] = f11;
    out[2usize] = f21;
    out[3usize] = f31;
    out[4usize] = f41
}

pub fn load_51(output: &mut [u64], input: &mut [u8]) -> ()
{
    let mut u64s: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = input.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = (&mut u64s).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let u64s3: u64 = (&mut u64s)[3usize];
    (&mut u64s)[3usize] = u64s3 & 0x7fffffffffffffffu64;
    output[0usize] = (&mut u64s)[0usize] & 0x7ffffffffffffu64;
    output[1usize] =
        ((&mut u64s)[0usize]).wrapping_shr(51u32)
        |
        ((&mut u64s)[1usize] & 0x3fffffffffu64).wrapping_shl(13u32);
    output[2usize] =
        ((&mut u64s)[1usize]).wrapping_shr(38u32)
        |
        ((&mut u64s)[2usize] & 0x1ffffffu64).wrapping_shl(26u32);
    output[3usize] =
        ((&mut u64s)[2usize]).wrapping_shr(25u32)
        |
        ((&mut u64s)[3usize] & 0xfffu64).wrapping_shl(39u32);
    output[4usize] = ((&mut u64s)[3usize]).wrapping_shr(12u32)
}

pub fn store_51(output: &mut [u8], input: &mut [u64]) -> ()
{
    let mut u64s: [u64; 4] = [0u64; 4usize];
    crate::hacl::bignum25519_51::store_felem(&mut u64s, input);
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store64_le(
            &mut output[i.wrapping_mul(8u32) as usize..],
            (&mut u64s)[i as usize]
        )
    }
}

pub fn point_double(out: &mut [u64], p: &mut [u64]) -> ()
{
    let mut tmp: [u64; 20] = [0u64; 20usize];
    let tmp1: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(5usize);
    let tmp3: (&mut [u64], &mut [u64]) = tmp2.1.split_at_mut(5usize);
    let tmp4: (&mut [u64], &mut [u64]) = tmp3.1.split_at_mut(5usize);
    let x1: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
    let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
    fsquare(tmp2.0, y1.0);
    fsquare(tmp3.0, z1.0);
    fsum(tmp4.0, tmp2.0, tmp3.0);
    fdifference(tmp4.1, tmp2.0, tmp3.0);
    fsquare(tmp2.0, z1.1);
    let mut a_copy: [u64; 5] = [0u64; 5usize];
    ((&mut a_copy)[0usize..5usize]).copy_from_slice(&tmp2.0[0usize..5usize]);
    times_2(tmp2.0, &mut a_copy);
    let tmp10: (&mut [u64], &mut [u64]) = tmp2.0.split_at_mut(0usize);
    let tmp20: (&mut [u64], &mut [u64]) = tmp3.0.split_at_mut(0usize);
    let tmp30: (&mut [u64], &mut [u64]) = tmp4.0.split_at_mut(0usize);
    let tmp40: (&mut [u64], &mut [u64]) = tmp4.1.split_at_mut(0usize);
    let x10: (&mut [u64], &mut [u64]) = y1.0.split_at_mut(0usize);
    let y10: (&mut [u64], &mut [u64]) = z1.0.split_at_mut(0usize);
    fsum(tmp20.1, x10.1, y10.1);
    let mut a_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut a_copy0)[0usize..5usize]).copy_from_slice(&tmp20.1[0usize..5usize]);
    fsquare(tmp20.1, &mut a_copy0);
    reduce_513(tmp30.1);
    let mut b_copy: [u64; 5] = [0u64; 5usize];
    ((&mut b_copy)[0usize..5usize]).copy_from_slice(&tmp20.1[0usize..5usize]);
    fdifference(tmp20.1, tmp30.1, &mut b_copy);
    reduce_513(tmp10.1);
    reduce_513(tmp40.1);
    let mut a_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut a_copy1)[0usize..5usize]).copy_from_slice(&tmp10.1[0usize..5usize]);
    fsum(tmp10.1, &mut a_copy1, tmp40.1);
    let tmp_f: (&mut [u64], &mut [u64]) = tmp10.1.split_at_mut(0usize);
    let tmp_e: (&mut [u64], &mut [u64]) = tmp20.1.split_at_mut(0usize);
    let tmp_h: (&mut [u64], &mut [u64]) = tmp30.1.split_at_mut(0usize);
    let tmp_g: (&mut [u64], &mut [u64]) = tmp40.1.split_at_mut(0usize);
    let x3: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(5usize);
    let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(5usize);
    let t3: (&mut [u64], &mut [u64]) = z3.1.split_at_mut(5usize);
    fmul(y3.0, tmp_e.1, tmp_f.1);
    fmul(z3.0, tmp_g.1, tmp_h.1);
    fmul(t3.1, tmp_e.1, tmp_h.1);
    fmul(t3.0, tmp_f.1, tmp_g.1)
}

pub fn point_add(out: &mut [u64], p: &mut [u64], q: &mut [u64]) -> ()
{
    let mut tmp: [u64; 30] = [0u64; 30usize];
    let tmp1: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(5usize);
    let tmp3: (&mut [u64], &mut [u64]) = tmp2.1.split_at_mut(5usize);
    let tmp4: (&mut [u64], &mut [u64]) = tmp3.1.split_at_mut(5usize);
    let x1: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
    let x2: (&mut [u64], &mut [u64]) = q.split_at_mut(0usize);
    let y2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(5usize);
    fdifference(tmp2.0, y1.1, y1.0);
    fdifference(tmp3.0, y2.1, y2.0);
    fmul(tmp4.0, tmp2.0, tmp3.0);
    fsum(tmp2.0, y1.1, y1.0);
    fsum(tmp3.0, y2.1, y2.0);
    fmul(tmp4.1, tmp2.0, tmp3.0);
    let tmp10: (&mut [u64], &mut [u64]) = tmp2.0.split_at_mut(0usize);
    let tmp20: (&mut [u64], &mut [u64]) = tmp3.0.split_at_mut(0usize);
    let tmp30: (&mut [u64], &mut [u64]) = tmp4.0.split_at_mut(0usize);
    let tmp40: (&mut [u64], &mut [u64]) = tmp4.1.split_at_mut(0usize);
    let tmp5: (&mut [u64], &mut [u64]) = tmp40.1.split_at_mut(5usize);
    let tmp6: (&mut [u64], &mut [u64]) = tmp5.1.split_at_mut(5usize);
    let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
    let t1: (&mut [u64], &mut [u64]) = z1.1.split_at_mut(5usize);
    let z2: (&mut [u64], &mut [u64]) = y2.1.split_at_mut(5usize);
    let t2: (&mut [u64], &mut [u64]) = z2.1.split_at_mut(5usize);
    times_2d(tmp10.1, t1.1);
    let mut inp_copy: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy)[0usize..5usize]).copy_from_slice(&tmp10.1[0usize..5usize]);
    fmul(tmp10.1, &mut inp_copy, t2.1);
    times_2(tmp20.1, t1.0);
    let mut inp_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy0)[0usize..5usize]).copy_from_slice(&tmp20.1[0usize..5usize]);
    fmul(tmp20.1, &mut inp_copy0, t2.0);
    fdifference(tmp6.0, tmp5.0, tmp30.1);
    fdifference(tmp6.1, tmp20.1, tmp10.1);
    let mut a_copy: [u64; 5] = [0u64; 5usize];
    ((&mut a_copy)[0usize..5usize]).copy_from_slice(&tmp10.1[0usize..5usize]);
    fsum(tmp10.1, &mut a_copy, tmp20.1);
    fsum(tmp20.1, tmp5.0, tmp30.1);
    let tmp_g: (&mut [u64], &mut [u64]) = tmp10.1.split_at_mut(0usize);
    let tmp_h: (&mut [u64], &mut [u64]) = tmp20.1.split_at_mut(0usize);
    let tmp_e: (&mut [u64], &mut [u64]) = tmp6.0.split_at_mut(0usize);
    let tmp_f: (&mut [u64], &mut [u64]) = tmp6.1.split_at_mut(0usize);
    let x3: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(5usize);
    let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(5usize);
    let t3: (&mut [u64], &mut [u64]) = z3.1.split_at_mut(5usize);
    fmul(y3.0, tmp_e.1, tmp_f.1);
    fmul(z3.0, tmp_g.1, tmp_h.1);
    fmul(t3.1, tmp_e.1, tmp_h.1);
    fmul(t3.0, tmp_f.1, tmp_g.1)
}

pub fn make_point_inf(b: &mut [u64]) -> ()
{
    let x: (&mut [u64], &mut [u64]) = b.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(5usize);
    let t: (&mut [u64], &mut [u64]) = z.1.split_at_mut(5usize);
    y.0[0usize] = 0u64;
    y.0[1usize] = 0u64;
    y.0[2usize] = 0u64;
    y.0[3usize] = 0u64;
    y.0[4usize] = 0u64;
    z.0[0usize] = 1u64;
    z.0[1usize] = 0u64;
    z.0[2usize] = 0u64;
    z.0[3usize] = 0u64;
    z.0[4usize] = 0u64;
    t.0[0usize] = 1u64;
    t.0[1usize] = 0u64;
    t.0[2usize] = 0u64;
    t.0[3usize] = 0u64;
    t.0[4usize] = 0u64;
    t.1[0usize] = 0u64;
    t.1[1usize] = 0u64;
    t.1[2usize] = 0u64;
    t.1[3usize] = 0u64;
    t.1[4usize] = 0u64
}

#[inline] fn pow2_252m2(out: &mut [u64], z: &mut [u64]) -> ()
{
    let mut buf: [u64; 20] = [0u64; 20usize];
    let a: (&mut [u64], &mut [u64]) = (&mut buf).split_at_mut(0usize);
    let t0: (&mut [u64], &mut [u64]) = a.1.split_at_mut(5usize);
    let b: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(5usize);
    let c: (&mut [u64], &mut [u64]) = b.1.split_at_mut(5usize);
    fsquare_times(t0.0, z, 1u32);
    fsquare_times(b.0, t0.0, 2u32);
    fmul(c.0, b.0, z);
    let mut inp_copy: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy)[0usize..5usize]).copy_from_slice(&t0.0[0usize..5usize]);
    fmul(t0.0, &mut inp_copy, c.0);
    fsquare_times(b.0, t0.0, 1u32);
    let mut inp_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy0)[0usize..5usize]).copy_from_slice(&c.0[0usize..5usize]);
    fmul(c.0, &mut inp_copy0, b.0);
    fsquare_times(b.0, c.0, 5u32);
    let mut inp_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy1)[0usize..5usize]).copy_from_slice(&c.0[0usize..5usize]);
    fmul(c.0, &mut inp_copy1, b.0);
    fsquare_times(b.0, c.0, 10u32);
    fmul(c.1, b.0, c.0);
    fsquare_times(b.0, c.1, 20u32);
    let mut inp_copy2: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy2)[0usize..5usize]).copy_from_slice(&b.0[0usize..5usize]);
    fmul(b.0, &mut inp_copy2, c.1);
    fsquare_times_inplace(b.0, 10u32);
    let mut inp_copy3: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy3)[0usize..5usize]).copy_from_slice(&c.0[0usize..5usize]);
    fmul(c.0, &mut inp_copy3, b.0);
    fsquare_times(b.0, c.0, 50u32);
    let a0: (&mut [u64], &mut [u64]) = t0.0.split_at_mut(0usize);
    let t00: (&mut [u64], &mut [u64]) = b.0.split_at_mut(0usize);
    let b0: (&mut [u64], &mut [u64]) = c.0.split_at_mut(0usize);
    let c0: (&mut [u64], &mut [u64]) = c.1.split_at_mut(0usize);
    fsquare_times(a0.1, z, 1u32);
    fmul(c0.1, t00.1, b0.1);
    fsquare_times(t00.1, c0.1, 100u32);
    let mut inp_copy4: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy4)[0usize..5usize]).copy_from_slice(&t00.1[0usize..5usize]);
    fmul(t00.1, &mut inp_copy4, c0.1);
    fsquare_times_inplace(t00.1, 50u32);
    let mut inp_copy5: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy5)[0usize..5usize]).copy_from_slice(&t00.1[0usize..5usize]);
    fmul(t00.1, &mut inp_copy5, b0.1);
    fsquare_times_inplace(t00.1, 2u32);
    fmul(out, t00.1, a0.1)
}

#[inline] fn is_0(x: &mut [u64]) -> bool
{
    let x0: u64 = x[0usize];
    let x1: u64 = x[1usize];
    let x2: u64 = x[2usize];
    let x3: u64 = x[3usize];
    let x4: u64 = x[4usize];
    x0 == 0u64 && x1 == 0u64 && x2 == 0u64 && x3 == 0u64 && x4 == 0u64
}

#[inline] fn mul_modp_sqrt_m1(x: &mut [u64]) -> ()
{
    let mut sqrt_m1: [u64; 5] = [0u64; 5usize];
    (&mut sqrt_m1)[0usize] = 0x00061b274a0ea0b0u64;
    (&mut sqrt_m1)[1usize] = 0x0000d5a5fc8f189du64;
    (&mut sqrt_m1)[2usize] = 0x0007ef5e9cbd0c60u64;
    (&mut sqrt_m1)[3usize] = 0x00078595a6804c9eu64;
    (&mut sqrt_m1)[4usize] = 0x0002b8324804fc1du64;
    let mut inp_copy: [u64; 5] = [0u64; 5usize];
    ((&mut inp_copy)[0usize..5usize]).copy_from_slice(&x[0usize..5usize]);
    fmul(x, &mut inp_copy, &mut sqrt_m1)
}

#[inline] fn recover_x(x: &mut [u64], y: &mut [u64], sign: u64) -> bool
{
    let mut tmp: [u64; 15] = [0u64; 15usize];
    let x2: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let x0: u64 = y[0usize];
    let x1: u64 = y[1usize];
    let x21: u64 = y[2usize];
    let x3: u64 = y[3usize];
    let x4: u64 = y[4usize];
    let b: bool =
        x0 >= 0x7ffffffffffedu64 && x1 == 0x7ffffffffffffu64 && x21 == 0x7ffffffffffffu64
        &&
        x3 == 0x7ffffffffffffu64
        &&
        x4 == 0x7ffffffffffffu64;
    let res: bool =
        if b
        { false }
        else
        {
            let mut tmp1: [u64; 20] = [0u64; 20usize];
            let one: (&mut [u64], &mut [u64]) = (&mut tmp1).split_at_mut(0usize);
            let y2: (&mut [u64], &mut [u64]) = one.1.split_at_mut(5usize);
            let dyyi: (&mut [u64], &mut [u64]) = y2.1.split_at_mut(5usize);
            let dyy: (&mut [u64], &mut [u64]) = dyyi.1.split_at_mut(5usize);
            y2.0[0usize] = 1u64;
            ();
            y2.0[1usize] = 0u64;
            ();
            y2.0[2usize] = 0u64;
            ();
            y2.0[3usize] = 0u64;
            ();
            y2.0[4usize] = 0u64;
            ();
            fsquare(dyyi.0, y);
            times_d(dyy.1, dyyi.0);
            let mut a_copy: [u64; 5] = [0u64; 5usize];
            ((&mut a_copy)[0usize..5usize]).copy_from_slice(&dyy.1[0usize..5usize]);
            ();
            fsum(dyy.1, &mut a_copy, y2.0);
            ();
            reduce_513(dyy.1);
            inverse(dyy.0, dyy.1);
            fdifference(x2.1, dyyi.0, y2.0);
            let mut inp_copy: [u64; 5] = [0u64; 5usize];
            ((&mut inp_copy)[0usize..5usize]).copy_from_slice(&x2.1[0usize..5usize]);
            ();
            fmul(x2.1, &mut inp_copy, dyy.0);
            ();
            reduce(x2.1);
            ();
            let x2_is_0: bool = is_0(x2.1);
            let z: u8 =
                if x2_is_0
                {
                    if sign == 0u64
                    {
                        x[0usize] = 0u64;
                        ();
                        x[1usize] = 0u64;
                        ();
                        x[2usize] = 0u64;
                        ();
                        x[3usize] = 0u64;
                        ();
                        x[4usize] = 0u64;
                        ();
                        1u8
                    }
                    else
                    { 0u8 }
                }
                else
                { 2u8 };
            if z == 0u8
            { false }
            else
            if z == 1u8
            { true }
            else
            {
                let x210: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(0usize);
                let x30: (&mut [u64], &mut [u64]) = x210.1.split_at_mut(5usize);
                let t0: (&mut [u64], &mut [u64]) = x30.1.split_at_mut(5usize);
                pow2_252m2(t0.0, x30.0);
                fsquare(t0.1, t0.0);
                let mut a_copy0: [u64; 5] = [0u64; 5usize];
                ((&mut a_copy0)[0usize..5usize]).copy_from_slice(&t0.1[0usize..5usize]);
                ();
                fdifference(t0.1, &mut a_copy0, x30.0);
                ();
                reduce_513(t0.1);
                reduce(t0.1);
                let t0_is_0: bool = is_0(t0.1);
                if ! t0_is_0 { mul_modp_sqrt_m1(t0.0) };
                let x211: (&mut [u64], &mut [u64]) = x30.0.split_at_mut(0usize);
                let x31: (&mut [u64], &mut [u64]) = t0.0.split_at_mut(0usize);
                let t00: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(0usize);
                fsquare(t00.1, x31.1);
                let mut a_copy1: [u64; 5] = [0u64; 5usize];
                ((&mut a_copy1)[0usize..5usize]).copy_from_slice(&t00.1[0usize..5usize]);
                ();
                fdifference(t00.1, &mut a_copy1, x211.1);
                ();
                reduce_513(t00.1);
                reduce(t00.1);
                let z1: bool = is_0(t00.1);
                if z1 == false
                { false }
                else
                {
                    let x32: (&mut [u64], &mut [u64]) = x31.1.split_at_mut(0usize);
                    let t01: (&mut [u64], &mut [u64]) = t00.1.split_at_mut(0usize);
                    reduce(x32.1);
                    let x00: u64 = x32.1[0usize];
                    let x01: u64 = x00 & 1u64;
                    if ! (x01 == sign)
                    {
                        t01.1[0usize] = 0u64;
                        ();
                        t01.1[1usize] = 0u64;
                        ();
                        t01.1[2usize] = 0u64;
                        ();
                        t01.1[3usize] = 0u64;
                        ();
                        t01.1[4usize] = 0u64;
                        ();
                        let mut b_copy: [u64; 5] = [0u64; 5usize];
                        ((&mut b_copy)[0usize..5usize]).copy_from_slice(&x32.1[0usize..5usize]);
                        ();
                        fdifference(x32.1, t01.1, &mut b_copy);
                        ();
                        reduce_513(x32.1);
                        reduce(x32.1)
                    };
                    (x[0usize..5usize]).copy_from_slice(&x32.1[0usize..5usize]);
                    ();
                    true
                }
            }
        };
    let res0: bool = res;
    res0
}

pub fn point_decompress(out: &mut [u64], s: &mut [u8]) -> bool
{
    let mut tmp: [u64; 10] = [0u64; 10usize];
    let y: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let x: (&mut [u64], &mut [u64]) = y.1.split_at_mut(5usize);
    let s31: u8 = s[31usize];
    let z: u8 = s31.wrapping_shr(7u32);
    let sign: u64 = z as u64;
    load_51(x.0, s);
    let z0: bool = recover_x(x.1, x.0, sign);
    let res: bool =
        if z0 == false
        { false }
        else
        {
            let outx: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
            let outy: (&mut [u64], &mut [u64]) = outx.1.split_at_mut(5usize);
            let outz: (&mut [u64], &mut [u64]) = outy.1.split_at_mut(5usize);
            let outt: (&mut [u64], &mut [u64]) = outz.1.split_at_mut(5usize);
            (outy.0[0usize..5usize]).copy_from_slice(&x.1[0usize..5usize]);
            ();
            (outz.0[0usize..5usize]).copy_from_slice(&x.0[0usize..5usize]);
            ();
            outt.0[0usize] = 1u64;
            ();
            outt.0[1usize] = 0u64;
            ();
            outt.0[2usize] = 0u64;
            ();
            outt.0[3usize] = 0u64;
            ();
            outt.0[4usize] = 0u64;
            ();
            fmul(outt.1, x.1, x.0);
            true
        };
    let res0: bool = res;
    res0
}

pub fn point_compress(z: &mut [u8], p: &mut [u64]) -> ()
{
    let mut tmp: [u64; 15] = [0u64; 15usize];
    let zinv: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let x: (&mut [u64], &mut [u64]) = zinv.1.split_at_mut(5usize);
    let out: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
    let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(5usize);
    let pz: (&mut [u64], &mut [u64]) = py.1.split_at_mut(5usize);
    inverse(x.0, pz.1);
    fmul(out.0, py.0, x.0);
    reduce(out.0);
    fmul(out.1, pz.0, x.0);
    reduce_513(out.1);
    let x0: (&mut [u64], &mut [u64]) = out.0.split_at_mut(0usize);
    let out0: (&mut [u64], &mut [u64]) = out.1.split_at_mut(0usize);
    let x00: u64 = x0.1[0usize];
    let b: u64 = x00 & 1u64;
    store_51(z, out0.1);
    let xbyte: u8 = b as u8;
    let o31: u8 = z[31usize];
    z[31usize] = o31.wrapping_add(xbyte.wrapping_shl(7u32))
}

#[inline] fn barrett_reduction(z: &mut [u64], t: &mut [u64]) -> ()
{
    let t0: u64 = t[0usize];
    let t1: u64 = t[1usize];
    let t2: u64 = t[2usize];
    let t3: u64 = t[3usize];
    let t4: u64 = t[4usize];
    let t5: u64 = t[5usize];
    let t6: u64 = t[6usize];
    let t7: u64 = t[7usize];
    let t8: u64 = t[8usize];
    let t9: u64 = t[9usize];
    let m0: u64 = 0x12631a5cf5d3edu64;
    let m1: u64 = 0xf9dea2f79cd658u64;
    let m2: u64 = 0x000000000014deu64;
    let m3: u64 = 0x00000000000000u64;
    let m4: u64 = 0x00000010000000u64;
    let m00: u64 = m0;
    let m10: u64 = m1;
    let m20: u64 = m2;
    let m30: u64 = m3;
    let m40: u64 = m4;
    let m01: u64 = 0x9ce5a30a2c131bu64;
    let m11: u64 = 0x215d086329a7edu64;
    let m21: u64 = 0xffffffffeb2106u64;
    let m31: u64 = 0xffffffffffffffu64;
    let m41: u64 = 0x00000fffffffffu64;
    let mu0: u64 = m01;
    let mu1: u64 = m11;
    let mu2: u64 = m21;
    let mu3: u64 = m31;
    let mu4: u64 = m41;
    let y·: u64 = (t5 & 0xffffffu64).wrapping_shl(32u32);
    let x·: u64 = t4.wrapping_shr(24u32);
    let z0: u64 = x· | y·;
    let y·0: u64 = (t6 & 0xffffffu64).wrapping_shl(32u32);
    let x·0: u64 = t5.wrapping_shr(24u32);
    let z1: u64 = x·0 | y·0;
    let y·1: u64 = (t7 & 0xffffffu64).wrapping_shl(32u32);
    let x·1: u64 = t6.wrapping_shr(24u32);
    let z2: u64 = x·1 | y·1;
    let y·2: u64 = (t8 & 0xffffffu64).wrapping_shl(32u32);
    let x·2: u64 = t7.wrapping_shr(24u32);
    let z3: u64 = x·2 | y·2;
    let y·3: u64 = (t9 & 0xffffffu64).wrapping_shl(32u32);
    let x·3: u64 = t8.wrapping_shr(24u32);
    let z4: u64 = x·3 | y·3;
    let q0: u64 = z0;
    let q1: u64 = z1;
    let q2: u64 = z2;
    let q3: u64 = z3;
    let q4: u64 = z4;
    let xy00: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu0);
    let xy01: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu1);
    let xy02: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu2);
    let xy03: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu3);
    let xy04: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu4);
    let xy10: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu0);
    let xy11: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu1);
    let xy12: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu2);
    let xy13: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu3);
    let xy14: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu4);
    let xy20: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu0);
    let xy21: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu1);
    let xy22: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu2);
    let xy23: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu3);
    let xy24: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu4);
    let xy30: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu0);
    let xy31: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu1);
    let xy32: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu2);
    let xy33: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu3);
    let xy34: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu4);
    let xy40: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu0);
    let xy41: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu1);
    let xy42: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu2);
    let xy43: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu3);
    let xy44: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu4);
    let z00: crate::fstar::uint128::uint128 = xy00;
    let z10: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy01, xy10);
    let z20: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy02, xy11), xy20);
    let z30: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy03, xy12), xy21),
            xy30
        );
    let z40: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy04, xy13), xy22),
                xy31
            ),
            xy40
        );
    let z5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy14, xy23), xy32),
            xy41
        );
    let z6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy24, xy33), xy42);
    let z7: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy34, xy43);
    let z8: crate::fstar::uint128::uint128 = xy44;
    let carry: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(z00, 56u32);
    let c0: crate::fstar::uint128::uint128 = carry;
    let carry0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z10, c0), 56u32);
    let c1: crate::fstar::uint128::uint128 = carry0;
    let carry1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z20, c1), 56u32);
    let c2: crate::fstar::uint128::uint128 = carry1;
    let carry2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z30, c2), 56u32);
    let c3: crate::fstar::uint128::uint128 = carry2;
    let carry3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z40, c3), 56u32);
    let t10: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z40, c3))
        &
        0xffffffffffffffu64;
    let c4: crate::fstar::uint128::uint128 = carry3;
    let t41: u64 = t10;
    let carry4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z5, c4), 56u32);
    let t100: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z5, c4))
        &
        0xffffffffffffffu64;
    let c5: crate::fstar::uint128::uint128 = carry4;
    let t51: u64 = t100;
    let carry5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z6, c5), 56u32);
    let t101: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z6, c5))
        &
        0xffffffffffffffu64;
    let c6: crate::fstar::uint128::uint128 = carry5;
    let t61: u64 = t101;
    let carry6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z7, c6), 56u32);
    let t102: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z7, c6))
        &
        0xffffffffffffffu64;
    let c7: crate::fstar::uint128::uint128 = carry6;
    let t71: u64 = t102;
    let carry7: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z8, c7), 56u32);
    let t103: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z8, c7))
        &
        0xffffffffffffffu64;
    let c8: crate::fstar::uint128::uint128 = carry7;
    let t81: u64 = t103;
    let t91: u64 = crate::fstar::uint128::uint128_to_uint64(c8);
    let qmu4·: u64 = t41;
    let qmu5·: u64 = t51;
    let qmu6·: u64 = t61;
    let qmu7·: u64 = t71;
    let qmu8·: u64 = t81;
    let qmu9·: u64 = t91;
    let y·4: u64 = (qmu5· & 0xffffffffffu64).wrapping_shl(16u32);
    let x·4: u64 = qmu4·.wrapping_shr(40u32);
    let z01: u64 = x·4 | y·4;
    let y·5: u64 = (qmu6· & 0xffffffffffu64).wrapping_shl(16u32);
    let x·5: u64 = qmu5·.wrapping_shr(40u32);
    let z11: u64 = x·5 | y·5;
    let y·6: u64 = (qmu7· & 0xffffffffffu64).wrapping_shl(16u32);
    let x·6: u64 = qmu6·.wrapping_shr(40u32);
    let z21: u64 = x·6 | y·6;
    let y·7: u64 = (qmu8· & 0xffffffffffu64).wrapping_shl(16u32);
    let x·7: u64 = qmu7·.wrapping_shr(40u32);
    let z31: u64 = x·7 | y·7;
    let y·8: u64 = (qmu9· & 0xffffffffffu64).wrapping_shl(16u32);
    let x·8: u64 = qmu8·.wrapping_shr(40u32);
    let z41: u64 = x·8 | y·8;
    let qdiv0: u64 = z01;
    let qdiv1: u64 = z11;
    let qdiv2: u64 = z21;
    let qdiv3: u64 = z31;
    let qdiv4: u64 = z41;
    let r0: u64 = t0;
    let r1: u64 = t1;
    let r2: u64 = t2;
    let r3: u64 = t3;
    let r4: u64 = t4 & 0xffffffffffu64;
    let xy000: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m00);
    let xy010: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m10);
    let xy020: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m20);
    let xy030: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m30);
    let xy040: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m40);
    let xy100: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m00);
    let xy110: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m10);
    let xy120: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m20);
    let xy130: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m30);
    let xy200: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv2, m00);
    let xy210: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv2, m10);
    let xy220: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv2, m20);
    let xy300: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv3, m00);
    let xy310: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv3, m10);
    let xy400: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv4, m00);
    let carry8: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(xy000, 56u32);
    let t104: u64 = crate::fstar::uint128::uint128_to_uint64(xy000) & 0xffffffffffffffu64;
    let c00: crate::fstar::uint128::uint128 = carry8;
    let t01: u64 = t104;
    let carry9: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy010, xy100), c00),
            56u32
        );
    let t105: u64 =
        crate::fstar::uint128::uint128_to_uint64(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy010, xy100), c00)
        )
        &
        0xffffffffffffffu64;
    let c10: crate::fstar::uint128::uint128 = carry9;
    let t11: u64 = t105;
    let carry10: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy020, xy110), xy200),
                c10
            ),
            56u32
        );
    let t106: u64 =
        crate::fstar::uint128::uint128_to_uint64(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy020, xy110), xy200),
                c10
            )
        )
        &
        0xffffffffffffffu64;
    let c20: crate::fstar::uint128::uint128 = carry10;
    let t21: u64 = t106;
    let carry11: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(
                    crate::fstar::uint128::add_mod(
                        crate::fstar::uint128::add_mod(xy030, xy120),
                        xy210
                    ),
                    xy300
                ),
                c20
            ),
            56u32
        );
    let t107: u64 =
        crate::fstar::uint128::uint128_to_uint64(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(
                    crate::fstar::uint128::add_mod(
                        crate::fstar::uint128::add_mod(xy030, xy120),
                        xy210
                    ),
                    xy300
                ),
                c20
            )
        )
        &
        0xffffffffffffffu64;
    let c30: crate::fstar::uint128::uint128 = carry11;
    let t31: u64 = t107;
    let t410: u64 =
        crate::fstar::uint128::uint128_to_uint64(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(
                    crate::fstar::uint128::add_mod(
                        crate::fstar::uint128::add_mod(
                            crate::fstar::uint128::add_mod(xy040, xy130),
                            xy220
                        ),
                        xy310
                    ),
                    xy400
                ),
                c30
            )
        )
        &
        0xffffffffffu64;
    let qmul0: u64 = t01;
    let qmul1: u64 = t11;
    let qmul2: u64 = t21;
    let qmul3: u64 = t31;
    let qmul4: u64 = t410;
    let b: u64 = r0.wrapping_sub(qmul0).wrapping_shr(63u32);
    let t108: u64 = b.wrapping_shl(56u32).wrapping_add(r0).wrapping_sub(qmul0);
    let c11: u64 = b;
    let t010: u64 = t108;
    let b0: u64 = r1.wrapping_sub(qmul1.wrapping_add(c11)).wrapping_shr(63u32);
    let t109: u64 = b0.wrapping_shl(56u32).wrapping_add(r1).wrapping_sub(qmul1.wrapping_add(c11));
    let c21: u64 = b0;
    let t110: u64 = t109;
    let b1: u64 = r2.wrapping_sub(qmul2.wrapping_add(c21)).wrapping_shr(63u32);
    let t1010: u64 = b1.wrapping_shl(56u32).wrapping_add(r2).wrapping_sub(qmul2.wrapping_add(c21));
    let c31: u64 = b1;
    let t210: u64 = t1010;
    let b2: u64 = r3.wrapping_sub(qmul3.wrapping_add(c31)).wrapping_shr(63u32);
    let t1011: u64 = b2.wrapping_shl(56u32).wrapping_add(r3).wrapping_sub(qmul3.wrapping_add(c31));
    let c40: u64 = b2;
    let t310: u64 = t1011;
    let b3: u64 = r4.wrapping_sub(qmul4.wrapping_add(c40)).wrapping_shr(63u32);
    let t1012: u64 = b3.wrapping_shl(40u32).wrapping_add(r4).wrapping_sub(qmul4.wrapping_add(c40));
    let t411: u64 = t1012;
    let s0: u64 = t010;
    let s1: u64 = t110;
    let s2: u64 = t210;
    let s3: u64 = t310;
    let s4: u64 = t411;
    let m010: u64 = 0x12631a5cf5d3edu64;
    let m110: u64 = 0xf9dea2f79cd658u64;
    let m210: u64 = 0x000000000014deu64;
    let m310: u64 = 0x00000000000000u64;
    let m410: u64 = 0x00000010000000u64;
    let y0: u64 = m010;
    let y1: u64 = m110;
    let y2: u64 = m210;
    let y3: u64 = m310;
    let y4: u64 = m410;
    let b4: u64 = s0.wrapping_sub(y0).wrapping_shr(63u32);
    let t1013: u64 = b4.wrapping_shl(56u32).wrapping_add(s0).wrapping_sub(y0);
    let b00: u64 = b4;
    let t011: u64 = t1013;
    let b5: u64 = s1.wrapping_sub(y1.wrapping_add(b00)).wrapping_shr(63u32);
    let t1014: u64 = b5.wrapping_shl(56u32).wrapping_add(s1).wrapping_sub(y1.wrapping_add(b00));
    let b10: u64 = b5;
    let t111: u64 = t1014;
    let b6: u64 = s2.wrapping_sub(y2.wrapping_add(b10)).wrapping_shr(63u32);
    let t1015: u64 = b6.wrapping_shl(56u32).wrapping_add(s2).wrapping_sub(y2.wrapping_add(b10));
    let b20: u64 = b6;
    let t211: u64 = t1015;
    let b7: u64 = s3.wrapping_sub(y3.wrapping_add(b20)).wrapping_shr(63u32);
    let t1016: u64 = b7.wrapping_shl(56u32).wrapping_add(s3).wrapping_sub(y3.wrapping_add(b20));
    let b30: u64 = b7;
    let t311: u64 = t1016;
    let b8: u64 = s4.wrapping_sub(y4.wrapping_add(b30)).wrapping_shr(63u32);
    let t1017: u64 = b8.wrapping_shl(56u32).wrapping_add(s4).wrapping_sub(y4.wrapping_add(b30));
    let b40: u64 = b8;
    let t412: u64 = t1017;
    let mask: u64 = b40.wrapping_sub(1u64);
    let z02: u64 = s0 ^ mask & (s0 ^ t011);
    let z12: u64 = s1 ^ mask & (s1 ^ t111);
    let z22: u64 = s2 ^ mask & (s2 ^ t211);
    let z32: u64 = s3 ^ mask & (s3 ^ t311);
    let z42: u64 = s4 ^ mask & (s4 ^ t412);
    let z03: u64 = z02;
    let z13: u64 = z12;
    let z23: u64 = z22;
    let z33: u64 = z32;
    let z43: u64 = z42;
    let o0: u64 = z03;
    let o1: u64 = z13;
    let o2: u64 = z23;
    let o3: u64 = z33;
    let o4: u64 = z43;
    let z04: u64 = o0;
    let z14: u64 = o1;
    let z24: u64 = o2;
    let z34: u64 = o3;
    let z44: u64 = o4;
    z[0usize] = z04;
    z[1usize] = z14;
    z[2usize] = z24;
    z[3usize] = z34;
    z[4usize] = z44
}

#[inline] fn mul_modq(out: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let mut tmp: [u64; 10] = [0u64; 10usize];
    let x0: u64 = x[0usize];
    let x1: u64 = x[1usize];
    let x2: u64 = x[2usize];
    let x3: u64 = x[3usize];
    let x4: u64 = x[4usize];
    let y0: u64 = y[0usize];
    let y1: u64 = y[1usize];
    let y2: u64 = y[2usize];
    let y3: u64 = y[3usize];
    let y4: u64 = y[4usize];
    let xy00: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y0);
    let xy01: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y1);
    let xy02: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y2);
    let xy03: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y3);
    let xy04: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y4);
    let xy10: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y0);
    let xy11: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y1);
    let xy12: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y2);
    let xy13: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y3);
    let xy14: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y4);
    let xy20: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y0);
    let xy21: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y1);
    let xy22: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y2);
    let xy23: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y3);
    let xy24: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y4);
    let xy30: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y0);
    let xy31: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y1);
    let xy32: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y2);
    let xy33: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y3);
    let xy34: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y4);
    let xy40: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y0);
    let xy41: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y1);
    let xy42: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y2);
    let xy43: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y3);
    let xy44: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y4);
    let z0: crate::fstar::uint128::uint128 = xy00;
    let z1: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy01, xy10);
    let z2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy02, xy11), xy20);
    let z3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy03, xy12), xy21),
            xy30
        );
    let z4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy04, xy13), xy22),
                xy31
            ),
            xy40
        );
    let z5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy14, xy23), xy32),
            xy41
        );
    let z6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy24, xy33), xy42);
    let z7: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy34, xy43);
    let z8: crate::fstar::uint128::uint128 = xy44;
    let carry: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(z0, 56u32);
    let t: u64 = crate::fstar::uint128::uint128_to_uint64(z0) & 0xffffffffffffffu64;
    let c0: crate::fstar::uint128::uint128 = carry;
    let t0: u64 = t;
    let carry0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z1, c0), 56u32);
    let t1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z1, c0))
        &
        0xffffffffffffffu64;
    let c1: crate::fstar::uint128::uint128 = carry0;
    let t10: u64 = t1;
    let carry1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z2, c1), 56u32);
    let t2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z2, c1))
        &
        0xffffffffffffffu64;
    let c2: crate::fstar::uint128::uint128 = carry1;
    let t20: u64 = t2;
    let carry2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z3, c2), 56u32);
    let t3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z3, c2))
        &
        0xffffffffffffffu64;
    let c3: crate::fstar::uint128::uint128 = carry2;
    let t30: u64 = t3;
    let carry3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z4, c3), 56u32);
    let t4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z4, c3))
        &
        0xffffffffffffffu64;
    let c4: crate::fstar::uint128::uint128 = carry3;
    let t40: u64 = t4;
    let carry4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z5, c4), 56u32);
    let t5: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z5, c4))
        &
        0xffffffffffffffu64;
    let c5: crate::fstar::uint128::uint128 = carry4;
    let t50: u64 = t5;
    let carry5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z6, c5), 56u32);
    let t6: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z6, c5))
        &
        0xffffffffffffffu64;
    let c6: crate::fstar::uint128::uint128 = carry5;
    let t60: u64 = t6;
    let carry6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z7, c6), 56u32);
    let t7: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z7, c6))
        &
        0xffffffffffffffu64;
    let c7: crate::fstar::uint128::uint128 = carry6;
    let t70: u64 = t7;
    let carry7: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z8, c7), 56u32);
    let t8: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z8, c7))
        &
        0xffffffffffffffu64;
    let c8: crate::fstar::uint128::uint128 = carry7;
    let t80: u64 = t8;
    let t9: u64 = crate::fstar::uint128::uint128_to_uint64(c8);
    let z00: u64 = t0;
    let z10: u64 = t10;
    let z20: u64 = t20;
    let z30: u64 = t30;
    let z40: u64 = t40;
    let z50: u64 = t50;
    let z60: u64 = t60;
    let z70: u64 = t70;
    let z80: u64 = t80;
    let z9: u64 = t9;
    (&mut tmp)[0usize] = z00;
    (&mut tmp)[1usize] = z10;
    (&mut tmp)[2usize] = z20;
    (&mut tmp)[3usize] = z30;
    (&mut tmp)[4usize] = z40;
    (&mut tmp)[5usize] = z50;
    (&mut tmp)[6usize] = z60;
    (&mut tmp)[7usize] = z70;
    (&mut tmp)[8usize] = z80;
    (&mut tmp)[9usize] = z9;
    barrett_reduction(out, &mut tmp)
}

#[inline] fn add_modq(out: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
    let x0: u64 = x[0usize];
    let x1: u64 = x[1usize];
    let x2: u64 = x[2usize];
    let x3: u64 = x[3usize];
    let x4: u64 = x[4usize];
    let y0: u64 = y[0usize];
    let y1: u64 = y[1usize];
    let y2: u64 = y[2usize];
    let y3: u64 = y[3usize];
    let y4: u64 = y[4usize];
    let carry: u64 = x0.wrapping_add(y0).wrapping_shr(56u32);
    let t: u64 = x0.wrapping_add(y0) & 0xffffffffffffffu64;
    let t0: u64 = t;
    let c0: u64 = carry;
    let carry0: u64 = x1.wrapping_add(y1).wrapping_add(c0).wrapping_shr(56u32);
    let t1: u64 = x1.wrapping_add(y1).wrapping_add(c0) & 0xffffffffffffffu64;
    let t10: u64 = t1;
    let c1: u64 = carry0;
    let carry1: u64 = x2.wrapping_add(y2).wrapping_add(c1).wrapping_shr(56u32);
    let t2: u64 = x2.wrapping_add(y2).wrapping_add(c1) & 0xffffffffffffffu64;
    let t20: u64 = t2;
    let c2: u64 = carry1;
    let carry2: u64 = x3.wrapping_add(y3).wrapping_add(c2).wrapping_shr(56u32);
    let t3: u64 = x3.wrapping_add(y3).wrapping_add(c2) & 0xffffffffffffffu64;
    let t30: u64 = t3;
    let c3: u64 = carry2;
    let t4: u64 = x4.wrapping_add(y4).wrapping_add(c3);
    let m0: u64 = 0x12631a5cf5d3edu64;
    let m1: u64 = 0xf9dea2f79cd658u64;
    let m2: u64 = 0x000000000014deu64;
    let m3: u64 = 0x00000000000000u64;
    let m4: u64 = 0x00000010000000u64;
    let y01: u64 = m0;
    let y11: u64 = m1;
    let y21: u64 = m2;
    let y31: u64 = m3;
    let y41: u64 = m4;
    let b: u64 = t0.wrapping_sub(y01).wrapping_shr(63u32);
    let t5: u64 = b.wrapping_shl(56u32).wrapping_add(t0).wrapping_sub(y01);
    let b0: u64 = b;
    let t01: u64 = t5;
    let b1: u64 = t10.wrapping_sub(y11.wrapping_add(b0)).wrapping_shr(63u32);
    let t6: u64 = b1.wrapping_shl(56u32).wrapping_add(t10).wrapping_sub(y11.wrapping_add(b0));
    let b10: u64 = b1;
    let t11: u64 = t6;
    let b2: u64 = t20.wrapping_sub(y21.wrapping_add(b10)).wrapping_shr(63u32);
    let t7: u64 = b2.wrapping_shl(56u32).wrapping_add(t20).wrapping_sub(y21.wrapping_add(b10));
    let b20: u64 = b2;
    let t21: u64 = t7;
    let b3: u64 = t30.wrapping_sub(y31.wrapping_add(b20)).wrapping_shr(63u32);
    let t8: u64 = b3.wrapping_shl(56u32).wrapping_add(t30).wrapping_sub(y31.wrapping_add(b20));
    let b30: u64 = b3;
    let t31: u64 = t8;
    let b4: u64 = t4.wrapping_sub(y41.wrapping_add(b30)).wrapping_shr(63u32);
    let t9: u64 = b4.wrapping_shl(56u32).wrapping_add(t4).wrapping_sub(y41.wrapping_add(b30));
    let b40: u64 = b4;
    let t41: u64 = t9;
    let mask: u64 = b40.wrapping_sub(1u64);
    let z0: u64 = t0 ^ mask & (t0 ^ t01);
    let z1: u64 = t10 ^ mask & (t10 ^ t11);
    let z2: u64 = t20 ^ mask & (t20 ^ t21);
    let z3: u64 = t30 ^ mask & (t30 ^ t31);
    let z4: u64 = t4 ^ mask & (t4 ^ t41);
    let z00: u64 = z0;
    let z10: u64 = z1;
    let z20: u64 = z2;
    let z30: u64 = z3;
    let z40: u64 = z4;
    let o0: u64 = z00;
    let o1: u64 = z10;
    let o2: u64 = z20;
    let o3: u64 = z30;
    let o4: u64 = z40;
    let z01: u64 = o0;
    let z11: u64 = o1;
    let z21: u64 = o2;
    let z31: u64 = o3;
    let z41: u64 = o4;
    out[0usize] = z01;
    out[1usize] = z11;
    out[2usize] = z21;
    out[3usize] = z31;
    out[4usize] = z41
}

#[inline] fn gte_q(s: &mut [u64]) -> bool
{
    let s0: u64 = s[0usize];
    let s1: u64 = s[1usize];
    let s2: u64 = s[2usize];
    let s3: u64 = s[3usize];
    let s4: u64 = s[4usize];
    if s4 > 0x00000010000000u64
    { true }
    else
    if s4 < 0x00000010000000u64
    { false }
    else
    if s3 > 0x00000000000000u64
    { true }
    else
    if s2 > 0x000000000014deu64
    { true }
    else
    if s2 < 0x000000000014deu64
    { false }
    else
    if s1 > 0xf9dea2f79cd658u64
    { true }
    else
    if s1 < 0xf9dea2f79cd658u64 { false } else if s0 >= 0x12631a5cf5d3edu64 { true } else { false }
}

#[inline] fn eq(a: &mut [u64], b: &mut [u64]) -> bool
{
    let a0: u64 = a[0usize];
    let a1: u64 = a[1usize];
    let a2: u64 = a[2usize];
    let a3: u64 = a[3usize];
    let a4: u64 = a[4usize];
    let b0: u64 = b[0usize];
    let b1: u64 = b[1usize];
    let b2: u64 = b[2usize];
    let b3: u64 = b[3usize];
    let b4: u64 = b[4usize];
    a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4
}

pub fn point_equal(p: &mut [u64], q: &mut [u64]) -> bool
{
    let mut tmp: [u64; 20] = [0u64; 20usize];
    let pxqz: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let qxpz: (&mut [u64], &mut [u64]) = pxqz.1.split_at_mut(5usize);
    fmul(qxpz.0, &mut p[0usize..], &mut q[10usize..]);
    reduce(qxpz.0);
    fmul(qxpz.1, &mut q[0usize..], &mut p[10usize..]);
    reduce(qxpz.1);
    let b: bool = eq(qxpz.0, qxpz.1);
    if b
    {
        let pyqz: (&mut [u64], &mut [u64]) = qxpz.1.split_at_mut(5usize);
        let qypz: (&mut [u64], &mut [u64]) = pyqz.1.split_at_mut(5usize);
        fmul(qypz.0, &mut p[5usize..], &mut q[10usize..]);
        reduce(qypz.0);
        fmul(qypz.1, &mut q[5usize..], &mut p[10usize..]);
        reduce(qypz.1);
        eq(qypz.0, qypz.1)
    }
    else
    { false }
}

pub fn point_negate(p: &mut [u64], out: &mut [u64]) -> ()
{
    let mut zero: [u64; 5] = [0u64; 5usize];
    (&mut zero)[0usize] = 0u64;
    (&mut zero)[1usize] = 0u64;
    (&mut zero)[2usize] = 0u64;
    (&mut zero)[3usize] = 0u64;
    (&mut zero)[4usize] = 0u64;
    let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
    let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(5usize);
    let t: (&mut [u64], &mut [u64]) = z.1.split_at_mut(5usize);
    let x1: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
    let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
    let t1: (&mut [u64], &mut [u64]) = z1.1.split_at_mut(5usize);
    fdifference(y1.0, &mut zero, y.0);
    reduce_513(y1.0);
    (z1.0[0usize..5usize]).copy_from_slice(&z.0[0usize..5usize]);
    (t1.0[0usize..5usize]).copy_from_slice(&t.0[0usize..5usize]);
    fdifference(t1.1, &mut zero, t.1);
    reduce_513(t1.1)
}

pub fn point_mul(out: &mut [u64], scalar: &mut [u8], q: &mut [u64]) -> ()
{
    let mut bscalar: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = scalar.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = (&mut bscalar).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let mut table: [u64; 320] = [0u64; 320usize];
    let mut tmp: [u64; 20] = [0u64; 20usize];
    let t0: (&mut [u64], &mut [u64]) = (&mut table).split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(20usize);
    make_point_inf(t1.0);
    (t1.1[0usize..20usize]).copy_from_slice(&q[0usize..20usize]);
    crate::lowstar::ignore::ignore::<&mut [u64]>(&mut table);
    for i in 0u32..7u32
    {
        let t11: (&mut [u64], &mut [u64]) =
            (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(20u32) as usize);
        let mut p_copy: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy)[0usize..20usize]).copy_from_slice(&t11.1[0usize..20usize]);
        point_double(&mut tmp, &mut p_copy);
        ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(20u32) as usize..2u32.wrapping_mul(
            i
        ).wrapping_add(2u32).wrapping_mul(20u32)
        as
        usize
        +
        20usize]).copy_from_slice(&(&mut tmp)[0usize..20usize]);
        let t2: (&mut [u64], &mut [u64]) =
            (&mut table).split_at_mut(
                2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(20u32) as usize
            );
        let mut p_copy0: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy0)[0usize..20usize]).copy_from_slice(&q[0usize..20usize]);
        point_add(&mut tmp, &mut p_copy0, t2.1);
        ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(20u32) as usize..2u32.wrapping_mul(
            i
        ).wrapping_add(3u32).wrapping_mul(20u32)
        as
        usize
        +
        20usize]).copy_from_slice(&(&mut tmp)[0usize..20usize])
    };
    make_point_inf(out);
    let mut tmp0: [u64; 20] = [0u64; 20usize];
    for i in 0u32..64u32
    {
        for _i in 0u32..4u32
        {
            let mut p_copy: [u64; 20] = [0u64; 20usize];
            ((&mut p_copy)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
            point_double(out, &mut p_copy)
        };
        let k: u32 = 256u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l: u64 = crate::hacl::bignum_base::bn_get_bits_u64(4u32, &mut bscalar, k, 4u32);
        crate::lowstar::ignore::ignore::<&[u64]>(&mut table);
        ((&mut tmp0)[0usize..20usize]).copy_from_slice(
            &(&mut (&mut table)[0usize..] as &mut [u64])[0usize..20usize]
        );
        for i0 in 0u32..15u32
        {
            let c: u64 = crate::fstar::uint64::eq_mask(bits_l, i0.wrapping_add(1u32) as u64);
            let res_j: (&[u64], &[u64]) =
                (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(20u32) as usize);
            for i1 in 0u32..20u32
            {
                let x: u64 = c & res_j.1[i1 as usize] | ! c & (&mut tmp0)[i1 as usize];
                let os: (&mut [u64], &mut [u64]) = (&mut tmp0).split_at_mut(0usize);
                os.1[i1 as usize] = x
            }
        };
        let mut p_copy: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy, &mut tmp0)
    }
}

#[inline] fn precomp_get_consttime(table: &[u64], bits_l: u64, tmp: &mut [u64]) -> ()
{
    (tmp[0usize..20usize]).copy_from_slice(&(&table[0usize..])[0usize..20usize]);
    for i in 0u32..15u32
    {
        let c: u64 = crate::fstar::uint64::eq_mask(bits_l, i.wrapping_add(1u32) as u64);
        let res_j: (&[u64], &[u64]) =
            table.split_at(i.wrapping_add(1u32).wrapping_mul(20u32) as usize);
        for i0 in 0u32..20u32
        {
            let x: u64 = c & res_j.1[i0 as usize] | ! c & tmp[i0 as usize];
            let os: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
            os.1[i0 as usize] = x
        }
    }
}

#[inline] fn point_mul_g(out: &mut [u64], scalar: &mut [u8]) -> ()
{
    let mut bscalar: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = scalar.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = (&mut bscalar).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let mut q1: [u64; 20] = [0u64; 20usize];
    let gx: (&mut [u64], &mut [u64]) = (&mut q1).split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = gx.1.split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = gy.1.split_at_mut(5usize);
    let gt: (&mut [u64], &mut [u64]) = gz.1.split_at_mut(5usize);
    gy.0[0usize] = 0x00062d608f25d51au64;
    gy.0[1usize] = 0x000412a4b4f6592au64;
    gy.0[2usize] = 0x00075b7171a4b31du64;
    gy.0[3usize] = 0x0001ff60527118feu64;
    gy.0[4usize] = 0x000216936d3cd6e5u64;
    gz.0[0usize] = 0x0006666666666658u64;
    gz.0[1usize] = 0x0004ccccccccccccu64;
    gz.0[2usize] = 0x0001999999999999u64;
    gz.0[3usize] = 0x0003333333333333u64;
    gz.0[4usize] = 0x0006666666666666u64;
    gt.0[0usize] = 1u64;
    gt.0[1usize] = 0u64;
    gt.0[2usize] = 0u64;
    gt.0[3usize] = 0u64;
    gt.0[4usize] = 0u64;
    gt.1[0usize] = 0x00068ab3a5b7dda3u64;
    gt.1[1usize] = 0x00000eea2a5eadbbu64;
    gt.1[2usize] = 0x0002af8df483c27eu64;
    gt.1[3usize] = 0x000332b375274732u64;
    gt.1[4usize] = 0x00067875f0fd78b7u64;
    let mut q2: [u64; 20] =
        [13559344787725u64, 2051621493703448u64, 1947659315640708u64, 626856790370168u64,
            1592804284034836u64, 1781728767459187u64, 278818420518009u64, 2038030359908351u64,
            910625973862690u64, 471887343142239u64, 1298543306606048u64, 794147365642417u64,
            129968992326749u64, 523140861678572u64, 1166419653909231u64, 2009637196928390u64,
            1288020222395193u64, 1007046974985829u64, 208981102651386u64, 2074009315253380u64];
    let mut q3: [u64; 20] =
        [557549315715710u64, 196756086293855u64, 846062225082495u64, 1865068224838092u64,
            991112090754908u64, 522916421512828u64, 2098523346722375u64, 1135633221747012u64,
            858420432114866u64, 186358544306082u64, 1044420411868480u64, 2080052304349321u64,
            557301814716724u64, 1305130257814057u64, 2126012765451197u64, 1441004402875101u64,
            353948968859203u64, 470765987164835u64, 1507675957683570u64, 1086650358745097u64];
    let mut q4: [u64; 20] =
        [1129953239743101u64, 1240339163956160u64, 61002583352401u64, 2017604552196030u64,
            1576867829229863u64, 1508654942849389u64, 270111619664077u64, 1253097517254054u64,
            721798270973250u64, 161923365415298u64, 828530877526011u64, 1494851059386763u64,
            662034171193976u64, 1315349646974670u64, 2199229517308806u64, 497078277852673u64,
            1310507715989956u64, 1881315714002105u64, 2214039404983803u64, 1331036420272667u64];
    let r1: (&mut [u64], &mut [u64]) = (&mut bscalar).split_at_mut(0usize);
    let r2: (&mut [u64], &mut [u64]) = r1.1.split_at_mut(1usize);
    let r3: (&mut [u64], &mut [u64]) = r2.1.split_at_mut(1usize);
    let r4: (&mut [u64], &mut [u64]) = r3.1.split_at_mut(1usize);
    make_point_inf(out);
    let mut tmp: [u64; 20] = [0u64; 20usize];
    for i in 0u32..16u32
    {
        for _i in 0u32..4u32
        {
            let mut p_copy: [u64; 20] = [0u64; 20usize];
            ((&mut p_copy)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
            point_double(out, &mut p_copy)
        };
        let k: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l: u64 = crate::hacl::bignum_base::bn_get_bits_u64(1u32, r4.1, k, 4u32);
        crate::lowstar::ignore::ignore::<&[u64]>(
            &crate::hacl::ed25519_precomptable::precomp_g_pow2_192_table_w4
        );
        precomp_get_consttime(
            &crate::hacl::ed25519_precomptable::precomp_g_pow2_192_table_w4,
            bits_l,
            &mut tmp
        );
        let mut p_copy: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy, &mut tmp);
        let k0: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l0: u64 = crate::hacl::bignum_base::bn_get_bits_u64(1u32, r4.0, k0, 4u32);
        crate::lowstar::ignore::ignore::<&[u64]>(
            &crate::hacl::ed25519_precomptable::precomp_g_pow2_128_table_w4
        );
        precomp_get_consttime(
            &crate::hacl::ed25519_precomptable::precomp_g_pow2_128_table_w4,
            bits_l0,
            &mut tmp
        );
        let mut p_copy0: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy0)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy0, &mut tmp);
        let k1: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l1: u64 = crate::hacl::bignum_base::bn_get_bits_u64(1u32, r3.0, k1, 4u32);
        crate::lowstar::ignore::ignore::<&[u64]>(
            &crate::hacl::ed25519_precomptable::precomp_g_pow2_64_table_w4
        );
        precomp_get_consttime(
            &crate::hacl::ed25519_precomptable::precomp_g_pow2_64_table_w4,
            bits_l1,
            &mut tmp
        );
        let mut p_copy1: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy1)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy1, &mut tmp);
        let k2: u32 = 64u32.wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(4u32);
        let bits_l2: u64 = crate::hacl::bignum_base::bn_get_bits_u64(1u32, r2.0, k2, 4u32);
        crate::lowstar::ignore::ignore::<&[u64]>(
            &crate::hacl::ed25519_precomptable::precomp_basepoint_table_w4
        );
        precomp_get_consttime(
            &crate::hacl::ed25519_precomptable::precomp_basepoint_table_w4,
            bits_l2,
            &mut tmp
        );
        let mut p_copy2: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy2)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy2, &mut tmp)
    };
    crate::lowstar::ignore::ignore::<&mut [u64]>(&mut q2);
    crate::lowstar::ignore::ignore::<&mut [u64]>(&mut q3);
    crate::lowstar::ignore::ignore::<&mut [u64]>(&mut q4)
}

#[inline] fn point_mul_g_double_vartime(
    out: &mut [u64],
    scalar1: &mut [u8],
    scalar2: &mut [u8],
    q2: &mut [u64]
) ->
    ()
{
    let mut tmp: [u64; 28] = [0u64; 28usize];
    let g: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
    let bscalar1: (&mut [u64], &mut [u64]) = g.1.split_at_mut(20usize);
    let bscalar2: (&mut [u64], &mut [u64]) = bscalar1.1.split_at_mut(4usize);
    let gx: (&mut [u64], &mut [u64]) = bscalar1.0.split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = gx.1.split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = gy.1.split_at_mut(5usize);
    let gt: (&mut [u64], &mut [u64]) = gz.1.split_at_mut(5usize);
    gy.0[0usize] = 0x00062d608f25d51au64;
    gy.0[1usize] = 0x000412a4b4f6592au64;
    gy.0[2usize] = 0x00075b7171a4b31du64;
    gy.0[3usize] = 0x0001ff60527118feu64;
    gy.0[4usize] = 0x000216936d3cd6e5u64;
    gz.0[0usize] = 0x0006666666666658u64;
    gz.0[1usize] = 0x0004ccccccccccccu64;
    gz.0[2usize] = 0x0001999999999999u64;
    gz.0[3usize] = 0x0003333333333333u64;
    gz.0[4usize] = 0x0006666666666666u64;
    gt.0[0usize] = 1u64;
    gt.0[1usize] = 0u64;
    gt.0[2usize] = 0u64;
    gt.0[3usize] = 0u64;
    gt.0[4usize] = 0u64;
    gt.1[0usize] = 0x00068ab3a5b7dda3u64;
    gt.1[1usize] = 0x00000eea2a5eadbbu64;
    gt.1[2usize] = 0x0002af8df483c27eu64;
    gt.1[3usize] = 0x000332b375274732u64;
    gt.1[4usize] = 0x00067875f0fd78b7u64;
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = scalar1.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = bscalar2.0.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = scalar2.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = bscalar2.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let mut table2: [u64; 640] = [0u64; 640usize];
    let mut tmp1: [u64; 20] = [0u64; 20usize];
    let t0: (&mut [u64], &mut [u64]) = (&mut table2).split_at_mut(0usize);
    let t1: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(20usize);
    make_point_inf(t1.0);
    (t1.1[0usize..20usize]).copy_from_slice(&q2[0usize..20usize]);
    crate::lowstar::ignore::ignore::<&mut [u64]>(&mut table2);
    for i in 0u32..15u32
    {
        let t11: (&mut [u64], &mut [u64]) =
            (&mut table2).split_at_mut(i.wrapping_add(1u32).wrapping_mul(20u32) as usize);
        let mut p_copy: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy)[0usize..20usize]).copy_from_slice(&t11.1[0usize..20usize]);
        point_double(&mut tmp1, &mut p_copy);
        ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(20u32) as usize..2u32.wrapping_mul(
            i
        ).wrapping_add(2u32).wrapping_mul(20u32)
        as
        usize
        +
        20usize]).copy_from_slice(&(&mut tmp1)[0usize..20usize]);
        let t2: (&mut [u64], &mut [u64]) =
            (&mut table2).split_at_mut(
                2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(20u32) as usize
            );
        let mut p_copy0: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy0)[0usize..20usize]).copy_from_slice(&q2[0usize..20usize]);
        point_add(&mut tmp1, &mut p_copy0, t2.1);
        ((&mut table2)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(20u32) as usize..2u32.wrapping_mul(
            i
        ).wrapping_add(3u32).wrapping_mul(20u32)
        as
        usize
        +
        20usize]).copy_from_slice(&(&mut tmp1)[0usize..20usize])
    };
    let mut tmp10: [u64; 20] = [0u64; 20usize];
    let i: u32 = 255u32;
    let bits_c: u64 = crate::hacl::bignum_base::bn_get_bits_u64(4u32, bscalar2.0, i, 5u32);
    let bits_l32: u32 = bits_c as u32;
    let a_bits_l: &[u64] =
        &(&crate::hacl::ed25519_precomptable::precomp_basepoint_table_w5)[bits_l32.wrapping_mul(
            20u32
        )
        as
        usize..];
    (out[0usize..20usize]).copy_from_slice(&a_bits_l[0usize..20usize]);
    let i0: u32 = 255u32;
    let bits_c0: u64 = crate::hacl::bignum_base::bn_get_bits_u64(4u32, bscalar2.1, i0, 5u32);
    let bits_l320: u32 = bits_c0 as u32;
    let a_bits_l0: (&[u64], &[u64]) =
        (&mut table2).split_at(bits_l320.wrapping_mul(20u32) as usize);
    ((&mut tmp10)[0usize..20usize]).copy_from_slice(&a_bits_l0.1[0usize..20usize]);
    let mut p_copy: [u64; 20] = [0u64; 20usize];
    ((&mut p_copy)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
    point_add(out, &mut p_copy, &mut tmp10);
    let mut tmp11: [u64; 20] = [0u64; 20usize];
    for i1 in 0u32..51u32
    {
        for _i in 0u32..5u32
        {
            let mut p_copy0: [u64; 20] = [0u64; 20usize];
            ((&mut p_copy0)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
            point_double(out, &mut p_copy0)
        };
        let k: u32 = 255u32.wrapping_sub(5u32.wrapping_mul(i1)).wrapping_sub(5u32);
        let bits_l: u64 = crate::hacl::bignum_base::bn_get_bits_u64(4u32, bscalar2.1, k, 5u32);
        crate::lowstar::ignore::ignore::<&[u64]>(&mut table2);
        let bits_l321: u32 = bits_l as u32;
        let a_bits_l1: (&[u64], &[u64]) =
            (&mut table2).split_at(bits_l321.wrapping_mul(20u32) as usize);
        ((&mut tmp11)[0usize..20usize]).copy_from_slice(&a_bits_l1.1[0usize..20usize]);
        let mut p_copy0: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy0)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy0, &mut tmp11);
        let k0: u32 = 255u32.wrapping_sub(5u32.wrapping_mul(i1)).wrapping_sub(5u32);
        let bits_l0: u64 = crate::hacl::bignum_base::bn_get_bits_u64(4u32, bscalar2.0, k0, 5u32);
        crate::lowstar::ignore::ignore::<&[u64]>(
            &crate::hacl::ed25519_precomptable::precomp_basepoint_table_w5
        );
        let bits_l322: u32 = bits_l0 as u32;
        let a_bits_l2: &[u64] =
            &(&crate::hacl::ed25519_precomptable::precomp_basepoint_table_w5)[bits_l322.wrapping_mul(
                20u32
            )
            as
            usize..];
        ((&mut tmp11)[0usize..20usize]).copy_from_slice(&a_bits_l2[0usize..20usize]);
        let mut p_copy1: [u64; 20] = [0u64; 20usize];
        ((&mut p_copy1)[0usize..20usize]).copy_from_slice(&out[0usize..20usize]);
        point_add(out, &mut p_copy1, &mut tmp11)
    }
}

#[inline] fn point_negate_mul_double_g_vartime(
    out: &mut [u64],
    scalar1: &mut [u8],
    scalar2: &mut [u8],
    q2: &mut [u64]
) ->
    ()
{
    let mut q2_neg: [u64; 20] = [0u64; 20usize];
    point_negate(q2, &mut q2_neg);
    point_mul_g_double_vartime(out, scalar1, scalar2, &mut q2_neg)
}

#[inline] fn store_56(out: &mut [u8], b: &mut [u64]) -> ()
{
    let b0: u64 = b[0usize];
    let b1: u64 = b[1usize];
    let b2: u64 = b[2usize];
    let b3: u64 = b[3usize];
    let b4: u64 = b[4usize];
    let b4·: u32 = b4 as u32;
    let b8: (&mut [u8], &mut [u8]) = out.split_at_mut(0usize);
    crate::lowstar::endianness::store64_le(b8.1, b0);
    let b80: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
    crate::lowstar::endianness::store64_le(b80.1, b1);
    let b81: (&mut [u8], &mut [u8]) = b80.1.split_at_mut(7usize);
    crate::lowstar::endianness::store64_le(b81.1, b2);
    let b82: (&mut [u8], &mut [u8]) = b81.1.split_at_mut(7usize);
    crate::lowstar::endianness::store64_le(b82.1, b3);
    crate::lowstar::endianness::store32_le(&mut out[28usize..], b4·)
}

#[inline] fn load_64_bytes(out: &mut [u64], b: &mut [u8]) -> ()
{
    let b8: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
    let z: u64 = u;
    let b0: u64 = z & 0xffffffffffffffu64;
    let b80: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
    let u0: u64 = crate::lowstar::endianness::load64_le(b80.1);
    let z0: u64 = u0;
    let b1: u64 = z0 & 0xffffffffffffffu64;
    let b81: (&mut [u8], &mut [u8]) = b80.1.split_at_mut(7usize);
    let u1: u64 = crate::lowstar::endianness::load64_le(b81.1);
    let z1: u64 = u1;
    let b2: u64 = z1 & 0xffffffffffffffu64;
    let b82: (&mut [u8], &mut [u8]) = b81.1.split_at_mut(7usize);
    let u2: u64 = crate::lowstar::endianness::load64_le(b82.1);
    let z2: u64 = u2;
    let b3: u64 = z2 & 0xffffffffffffffu64;
    let b83: (&mut [u8], &mut [u8]) = b82.1.split_at_mut(7usize);
    let u3: u64 = crate::lowstar::endianness::load64_le(b83.1);
    let z3: u64 = u3;
    let b4: u64 = z3 & 0xffffffffffffffu64;
    let b84: (&mut [u8], &mut [u8]) = b83.1.split_at_mut(7usize);
    let u4: u64 = crate::lowstar::endianness::load64_le(b84.1);
    let z4: u64 = u4;
    let b5: u64 = z4 & 0xffffffffffffffu64;
    let b85: (&mut [u8], &mut [u8]) = b84.1.split_at_mut(7usize);
    let u5: u64 = crate::lowstar::endianness::load64_le(b85.1);
    let z5: u64 = u5;
    let b6: u64 = z5 & 0xffffffffffffffu64;
    let b86: (&mut [u8], &mut [u8]) = b85.1.split_at_mut(7usize);
    let u6: u64 = crate::lowstar::endianness::load64_le(b86.1);
    let z6: u64 = u6;
    let b7: u64 = z6 & 0xffffffffffffffu64;
    let b87: (&mut [u8], &mut [u8]) = b86.1.split_at_mut(7usize);
    let u7: u64 = crate::lowstar::endianness::load64_le(b87.1);
    let z7: u64 = u7;
    let b88: u64 = z7 & 0xffffffffffffffu64;
    let b63: u8 = b[63usize];
    let b9: u64 = b63 as u64;
    out[0usize] = b0;
    out[1usize] = b1;
    out[2usize] = b2;
    out[3usize] = b3;
    out[4usize] = b4;
    out[5usize] = b5;
    out[6usize] = b6;
    out[7usize] = b7;
    out[8usize] = b88;
    out[9usize] = b9
}

#[inline] fn load_32_bytes(out: &mut [u64], b: &mut [u8]) -> ()
{
    let b8: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
    let z: u64 = u;
    let b0: u64 = z & 0xffffffffffffffu64;
    let b80: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
    let u0: u64 = crate::lowstar::endianness::load64_le(b80.1);
    let z0: u64 = u0;
    let b1: u64 = z0 & 0xffffffffffffffu64;
    let b81: (&mut [u8], &mut [u8]) = b80.1.split_at_mut(7usize);
    let u1: u64 = crate::lowstar::endianness::load64_le(b81.1);
    let z1: u64 = u1;
    let b2: u64 = z1 & 0xffffffffffffffu64;
    let b82: (&mut [u8], &mut [u8]) = b81.1.split_at_mut(7usize);
    let u2: u64 = crate::lowstar::endianness::load64_le(b82.1);
    let z2: u64 = u2;
    let b3: u64 = z2 & 0xffffffffffffffu64;
    let u3: u32 = crate::lowstar::endianness::load32_le(&mut b[28usize..]);
    let b4: u32 = u3;
    let b41: u64 = b4 as u64;
    out[0usize] = b0;
    out[1usize] = b1;
    out[2usize] = b2;
    out[3usize] = b3;
    out[4usize] = b41
}

#[inline] fn sha512_pre_msg(hash: &mut [u8], prefix: &mut [u8], len: u32, input: &mut [u8]) ->
    ()
{
    let mut buf: [u8; 128] = [0u8; 128usize];
    let mut block_state: [u64; 8] = [0u64; 8usize];
    crate::hacl::hash_sha2::sha512_init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_64 =
        crate::hacl::streaming_types::state_64
        { block_state: Vec::from(block_state), buf: Vec::from(buf), total_len: 0u32 as u64 };
    let mut p: [crate::hacl::streaming_types::state_64; 1] = [s; 1usize];
    let st: &mut [crate::hacl::streaming_types::state_64] = &mut p;
    let err0: crate::hacl::streaming_types::error_code =
        crate::hacl::hash_sha2::update_512(st, prefix, 32u32);
    let err1: crate::hacl::streaming_types::error_code =
        crate::hacl::hash_sha2::update_512(st, input, len);
    crate::lowstar::ignore::ignore::<crate::hacl::streaming_types::error_code>(err0);
    crate::lowstar::ignore::ignore::<crate::hacl::streaming_types::error_code>(err1);
    crate::hacl::hash_sha2::digest_512(st, hash)
}

#[inline] fn sha512_pre_pre2_msg(
    hash: &mut [u8],
    prefix: &mut [u8],
    prefix2: &mut [u8],
    len: u32,
    input: &mut [u8]
) ->
    ()
{
    let mut buf: [u8; 128] = [0u8; 128usize];
    let mut block_state: [u64; 8] = [0u64; 8usize];
    crate::hacl::hash_sha2::sha512_init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_64 =
        crate::hacl::streaming_types::state_64
        { block_state: Vec::from(block_state), buf: Vec::from(buf), total_len: 0u32 as u64 };
    let mut p: [crate::hacl::streaming_types::state_64; 1] = [s; 1usize];
    let st: &mut [crate::hacl::streaming_types::state_64] = &mut p;
    let err0: crate::hacl::streaming_types::error_code =
        crate::hacl::hash_sha2::update_512(st, prefix, 32u32);
    let err1: crate::hacl::streaming_types::error_code =
        crate::hacl::hash_sha2::update_512(st, prefix2, 32u32);
    let err2: crate::hacl::streaming_types::error_code =
        crate::hacl::hash_sha2::update_512(st, input, len);
    crate::lowstar::ignore::ignore::<crate::hacl::streaming_types::error_code>(err0);
    crate::lowstar::ignore::ignore::<crate::hacl::streaming_types::error_code>(err1);
    crate::lowstar::ignore::ignore::<crate::hacl::streaming_types::error_code>(err2);
    crate::hacl::hash_sha2::digest_512(st, hash)
}

#[inline] fn sha512_modq_pre(out: &mut [u64], prefix: &mut [u8], len: u32, input: &mut [u8]) ->
    ()
{
    let mut tmp: [u64; 10] = [0u64; 10usize];
    let mut hash: [u8; 64] = [0u8; 64usize];
    sha512_pre_msg(&mut hash, prefix, len, input);
    load_64_bytes(&mut tmp, &mut hash);
    barrett_reduction(out, &mut tmp)
}

#[inline] fn sha512_modq_pre_pre2(
    out: &mut [u64],
    prefix: &mut [u8],
    prefix2: &mut [u8],
    len: u32,
    input: &mut [u8]
) ->
    ()
{
    let mut tmp: [u64; 10] = [0u64; 10usize];
    let mut hash: [u8; 64] = [0u8; 64usize];
    sha512_pre_pre2_msg(&mut hash, prefix, prefix2, len, input);
    load_64_bytes(&mut tmp, &mut hash);
    barrett_reduction(out, &mut tmp)
}

#[inline] fn point_mul_g_compress(out: &mut [u8], s: &mut [u8]) -> ()
{
    let mut tmp: [u64; 20] = [0u64; 20usize];
    point_mul_g(&mut tmp, s);
    point_compress(out, &mut tmp)
}

#[inline] fn secret_expand(expanded: &mut [u8], secret: &mut [u8]) -> ()
{
    crate::hacl::hash_sha2::hash_512(expanded, secret, 32u32);
    let h_low: (&mut [u8], &mut [u8]) = expanded.split_at_mut(0usize);
    let h_low0: u8 = h_low.1[0usize];
    let h_low31: u8 = h_low.1[31usize];
    h_low.1[0usize] = h_low0 & 0xf8u8;
    h_low.1[31usize] = h_low31 & 127u8 | 64u8
}

pub fn secret_to_public(public_key: &mut [u8], private_key: &mut [u8]) -> ()
{
    let mut expanded_secret: [u8; 64] = [0u8; 64usize];
    secret_expand(&mut expanded_secret, private_key);
    let a: (&mut [u8], &mut [u8]) = (&mut expanded_secret).split_at_mut(0usize);
    point_mul_g_compress(public_key, a.1)
}

pub fn expand_keys(expanded_keys: &mut [u8], private_key: &mut [u8]) -> ()
{
    let s_prefix: (&mut [u8], &mut [u8]) = expanded_keys.split_at_mut(32usize);
    secret_expand(s_prefix.1, private_key);
    let public_key: (&mut [u8], &mut [u8]) = s_prefix.0.split_at_mut(0usize);
    let s: (&mut [u8], &mut [u8]) = s_prefix.1.split_at_mut(0usize);
    point_mul_g_compress(public_key.1, s.1)
}

pub fn sign_expanded(
    signature: &mut [u8],
    expanded_keys: &mut [u8],
    msg_len: u32,
    msg: &mut [u8]
) ->
    ()
{
    let rs: (&mut [u8], &mut [u8]) = signature.split_at_mut(0usize);
    let ss: (&mut [u8], &mut [u8]) = rs.1.split_at_mut(32usize);
    let mut rq: [u64; 5] = [0u64; 5usize];
    let mut hq: [u64; 5] = [0u64; 5usize];
    let mut rb: [u8; 32] = [0u8; 32usize];
    let public_key: (&mut [u8], &mut [u8]) = expanded_keys.split_at_mut(0usize);
    let s: (&mut [u8], &mut [u8]) = public_key.1.split_at_mut(32usize);
    let prefix: (&mut [u8], &mut [u8]) = s.1.split_at_mut(32usize);
    sha512_modq_pre(&mut rq, prefix.1, msg_len, msg);
    store_56(&mut rb, &mut rq);
    point_mul_g_compress(ss.0, &mut rb);
    sha512_modq_pre_pre2(&mut hq, ss.0, s.0, msg_len, msg);
    let mut aq: [u64; 5] = [0u64; 5usize];
    load_32_bytes(&mut aq, prefix.0);
    let mut y_copy: [u64; 5] = [0u64; 5usize];
    ((&mut y_copy)[0usize..5usize]).copy_from_slice(&(&mut aq)[0usize..5usize]);
    mul_modq(&mut aq, &mut hq, &mut y_copy);
    let mut y_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut y_copy0)[0usize..5usize]).copy_from_slice(&(&mut aq)[0usize..5usize]);
    add_modq(&mut aq, &mut rq, &mut y_copy0);
    store_56(ss.1, &mut aq)
}

pub fn sign(signature: &mut [u8], private_key: &mut [u8], msg_len: u32, msg: &mut [u8]) -> ()
{
    let mut expanded_keys: [u8; 96] = [0u8; 96usize];
    expand_keys(&mut expanded_keys, private_key);
    sign_expanded(signature, &mut expanded_keys, msg_len, msg)
}

pub fn verify(public_key: &mut [u8], msg_len: u32, msg: &mut [u8], signature: &mut [u8]) ->
    bool
{
    let mut a·: [u64; 20] = [0u64; 20usize];
    let b: bool = point_decompress(&mut a·, public_key);
    if b
    {
        let mut r·: [u64; 20] = [0u64; 20usize];
        let rs: (&mut [u8], &mut [u8]) = signature.split_at_mut(0usize);
        let b·: bool = point_decompress(&mut r·, rs.1);
        if b·
        {
            let mut hb: [u8; 32] = [0u8; 32usize];
            let rs1: (&mut [u8], &mut [u8]) = rs.1.split_at_mut(0usize);
            let sb: (&mut [u8], &mut [u8]) = rs1.1.split_at_mut(32usize);
            let mut tmp: [u64; 5] = [0u64; 5usize];
            load_32_bytes(&mut tmp, sb.1);
            let b1: bool = gte_q(&mut tmp);
            let b10: bool = b1;
            if b10
            { false }
            else
            {
                let mut tmp0: [u64; 5] = [0u64; 5usize];
                sha512_modq_pre_pre2(&mut tmp0, sb.0, public_key, msg_len, msg);
                store_56(&mut hb, &mut tmp0);
                let mut exp_d: [u64; 20] = [0u64; 20usize];
                point_negate_mul_double_g_vartime(&mut exp_d, sb.1, &mut hb, &mut a·);
                let b2: bool = point_equal(&mut exp_d, &mut r·);
                b2
            }
        }
        else
        { false }
    }
    else
    { false }
}
