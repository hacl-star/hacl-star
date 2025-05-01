#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub(crate) fn shake128_4x(
    input_len: u32,
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    output_len: u32,
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8]
)
{
    crate::hash_sha3::shake128(output0, output_len, input0, input_len);
    crate::hash_sha3::shake128(output1, output_len, input1, input_len);
    crate::hash_sha3::shake128(output2, output_len, input2, input_len);
    crate::hash_sha3::shake128(output3, output_len, input3, input_len)
}

#[inline] pub(crate) fn mod_pow2(n1: u32, n2: u32, logq: u32, a: &mut [u16])
{
    if logq < 16u32
    {
        for i in 0u32..n1
        {
            for i0 in 0u32..n2
            {
                a[i.wrapping_mul(n2).wrapping_add(i0) as usize] &=
                    1u16.wrapping_shl(logq).wrapping_sub(1u16)
            }
        }
    }
}

#[inline] pub(crate) fn matrix_add(n1: u32, n2: u32, a: &mut [u16], b: &[u16])
{
    for i in 0u32..n1
    {
        for i0 in 0u32..n2
        {
            a[i.wrapping_mul(n2).wrapping_add(i0) as usize] =
                (a[i.wrapping_mul(n2).wrapping_add(i0) as usize]).wrapping_add(
                    b[i.wrapping_mul(n2).wrapping_add(i0) as usize]
                )
        }
    }
}

#[inline] pub(crate) fn matrix_sub(n1: u32, n2: u32, a: &[u16], b: &mut [u16])
{
    for i in 0u32..n1
    {
        for i0 in 0u32..n2
        {
            b[i.wrapping_mul(n2).wrapping_add(i0) as usize] =
                (a[i.wrapping_mul(n2).wrapping_add(i0) as usize]).wrapping_sub(
                    b[i.wrapping_mul(n2).wrapping_add(i0) as usize]
                )
        }
    }
}

#[inline] pub(crate) fn matrix_mul(
    n1: u32,
    n2: u32,
    n3: u32,
    a: &[u16],
    b: &[u16],
    c: &mut [u16]
)
{
    for i in 0u32..n1
    {
        for i0 in 0u32..n3
        {
            let mut res: [u16; 1] = [0u16; 1usize];
            for i1 in 0u32..n2
            {
                let aij: u16 = a[i.wrapping_mul(n2).wrapping_add(i1) as usize];
                let bjk: u16 = b[i1.wrapping_mul(n3).wrapping_add(i0) as usize];
                let res0: u16 = (&res)[0usize];
                (&mut res)[0usize] = res0.wrapping_add(aij.wrapping_mul(bjk))
            };
            c[i.wrapping_mul(n3).wrapping_add(i0) as usize] = (&res)[0usize]
        }
    }
}

#[inline] pub(crate) fn matrix_mul_s(
    n1: u32,
    n2: u32,
    n3: u32,
    a: &[u16],
    b: &[u16],
    c: &mut [u16]
)
{
    for i in 0u32..n1
    {
        for i0 in 0u32..n3
        {
            let mut res: [u16; 1] = [0u16; 1usize];
            for i1 in 0u32..n2
            {
                let aij: u16 = a[i.wrapping_mul(n2).wrapping_add(i1) as usize];
                let bjk: u16 = b[i0.wrapping_mul(n2).wrapping_add(i1) as usize];
                let res0: u16 = (&res)[0usize];
                (&mut res)[0usize] = res0.wrapping_add(aij.wrapping_mul(bjk))
            };
            c[i.wrapping_mul(n3).wrapping_add(i0) as usize] = (&res)[0usize]
        }
    }
}

#[inline] pub(crate) fn matrix_eq(n1: u32, n2: u32, a: &[u16], b: &[u16]) -> u16
{
    let mut res: [u16; 1] = [0xFFFFu16; 1usize];
    for i in 0u32..n1.wrapping_mul(n2)
    {
        let uu____0: u16 = fstar::uint16::eq_mask(a[i as usize], b[i as usize]);
        (&mut res)[0usize] = uu____0 & (&res)[0usize]
    };
    let r: u16 = (&res)[0usize];
    r
}

#[inline] pub(crate) fn matrix_to_lbytes(n1: u32, n2: u32, m: &[u16], res: &mut [u8])
{
    for i in 0u32..n1.wrapping_mul(n2)
    { lowstar::endianness::store16_le(&mut res[2u32.wrapping_mul(i) as usize..], m[i as usize]) }
}

#[inline] pub(crate) fn matrix_from_lbytes(n1: u32, n2: u32, b: &[u8], res: &mut [u16])
{
    for i in 0u32..n1.wrapping_mul(n2)
    {
        let u: u16 = lowstar::endianness::load16_le(&b[2u32.wrapping_mul(i) as usize..]);
        let x: u16 = u;
        let os: (&mut [u16], &mut [u16]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] pub(crate) fn frodo_gen_matrix_shake_4x(n: u32, seed: &[u8], res: &mut [u16])
{
    let mut r: Box<[u8]> = vec![0u8; 8u32.wrapping_mul(n) as usize].into_boxed_slice();
    let mut tmp_seed: [u8; 72] = [0u8; 72usize];
    ((&mut (&mut tmp_seed)[2usize..])[0usize..16usize]).copy_from_slice(&seed[0usize..16usize]);
    ((&mut (&mut tmp_seed)[20usize..])[0usize..16usize]).copy_from_slice(&seed[0usize..16usize]);
    ((&mut (&mut tmp_seed)[38usize..])[0usize..16usize]).copy_from_slice(&seed[0usize..16usize]);
    ((&mut (&mut tmp_seed)[56usize..])[0usize..16usize]).copy_from_slice(&seed[0usize..16usize]);
    (res[0usize..n.wrapping_mul(n) as usize]).copy_from_slice(
        &vec![0u16; n.wrapping_mul(n) as usize].into_boxed_slice()
    );
    for i in 0u32..n.wrapping_div(4u32)
    {
        let r0: (&mut [u8], &mut [u8]) = r.split_at_mut(0u32.wrapping_mul(n) as usize);
        let r1: (&mut [u8], &mut [u8]) =
            (r0.1).split_at_mut(2u32.wrapping_mul(n) as usize - 0u32.wrapping_mul(n) as usize);
        let r2: (&mut [u8], &mut [u8]) =
            (r1.1).split_at_mut(4u32.wrapping_mul(n) as usize - 2u32.wrapping_mul(n) as usize);
        let r3: (&mut [u8], &mut [u8]) =
            (r2.1).split_at_mut(6u32.wrapping_mul(n) as usize - 4u32.wrapping_mul(n) as usize);
        let tmp_seed0: (&mut [u8], &mut [u8]) = tmp_seed.split_at_mut(0usize);
        let tmp_seed1: (&mut [u8], &mut [u8]) = (tmp_seed0.1).split_at_mut(18usize);
        let tmp_seed2: (&mut [u8], &mut [u8]) = (tmp_seed1.1).split_at_mut(18usize);
        let tmp_seed3: (&mut [u8], &mut [u8]) = (tmp_seed2.1).split_at_mut(18usize);
        lowstar::endianness::store16_le(
            &mut tmp_seed1.0[0usize..],
            4u32.wrapping_mul(i).wrapping_add(0u32) as u16
        );
        lowstar::endianness::store16_le(
            &mut tmp_seed2.0[0usize..],
            4u32.wrapping_mul(i).wrapping_add(1u32) as u16
        );
        lowstar::endianness::store16_le(
            &mut tmp_seed3.0[0usize..],
            4u32.wrapping_mul(i).wrapping_add(2u32) as u16
        );
        lowstar::endianness::store16_le(
            &mut tmp_seed3.1[0usize..],
            4u32.wrapping_mul(i).wrapping_add(3u32) as u16
        );
        crate::frodo_kem::shake128_4x(
            18u32,
            tmp_seed1.0,
            tmp_seed2.0,
            tmp_seed3.0,
            tmp_seed3.1,
            2u32.wrapping_mul(n),
            r1.0,
            r2.0,
            r3.0,
            r3.1
        );
        for i0 in 0u32..n
        {
            let resij0: (&[u8], &[u8]) = (r1.0).split_at(i0.wrapping_mul(2u32) as usize);
            let resij1: (&[u8], &[u8]) = (r2.0).split_at(i0.wrapping_mul(2u32) as usize);
            let resij2: (&[u8], &[u8]) = (r3.0).split_at(i0.wrapping_mul(2u32) as usize);
            let resij3: (&[u8], &[u8]) = (r3.1).split_at(i0.wrapping_mul(2u32) as usize);
            let u: u16 = lowstar::endianness::load16_le(resij0.1);
            res[4u32.wrapping_mul(i).wrapping_add(0u32).wrapping_mul(n).wrapping_add(i0) as usize] =
                u;
            let u0: u16 = lowstar::endianness::load16_le(resij1.1);
            res[4u32.wrapping_mul(i).wrapping_add(1u32).wrapping_mul(n).wrapping_add(i0) as usize] =
                u0;
            let u1: u16 = lowstar::endianness::load16_le(resij2.1);
            res[4u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(n).wrapping_add(i0) as usize] =
                u1;
            let u2: u16 = lowstar::endianness::load16_le(resij3.1);
            res[4u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(n).wrapping_add(i0) as usize] =
                u2
        }
    }
}

#[inline] pub(crate) fn frodo_gen_matrix(
    a: crate::spec::frodo_gen_a,
    n: u32,
    seed: &[u8],
    a_matrix: &mut [u16]
)
{
    match a
    {
        crate::spec::frodo_gen_a::SHAKE128 =>
          crate::frodo_kem::frodo_gen_matrix_shake_4x(n, seed, a_matrix),
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub(crate) const cdf_table640: [u16; 13] =
    [4643u16, 13363u16, 20579u16, 25843u16, 29227u16, 31145u16, 32103u16, 32525u16, 32689u16,
        32745u16, 32762u16, 32766u16, 32767u16];

pub(crate) const cdf_table976: [u16; 11] =
    [5638u16, 15915u16, 23689u16, 28571u16, 31116u16, 32217u16, 32613u16, 32731u16, 32760u16,
        32766u16, 32767u16];

pub(crate) const cdf_table1344: [u16; 7] =
    [9142u16, 23462u16, 30338u16, 32361u16, 32725u16, 32765u16, 32767u16];

#[inline] pub(crate) fn frodo_sample_matrix64(n1: u32, n2: u32, r: &[u8], res: &mut [u16])
{
    (res[0usize..n1.wrapping_mul(n2) as usize]).copy_from_slice(
        &vec![0u16; n1.wrapping_mul(n2) as usize].into_boxed_slice()
    );
    for i in 0u32..n1
    {
        for i0 in 0u32..n2
        {
            let resij: (&[u8], &[u8]) =
                r.split_at(2u32.wrapping_mul(n2.wrapping_mul(i).wrapping_add(i0)) as usize);
            let u: u16 = lowstar::endianness::load16_le(resij.1);
            let uu____0: u16 = u;
            let prnd: u16 = uu____0.wrapping_shr(1u32);
            let sign: u16 = uu____0 & 1u16;
            let mut sample: [u16; 1] = [0u16; 1usize];
            let bound: u32 = 12u32;
            for i1 in 0u32..bound
            {
                let sample0: u16 = (&sample)[0usize];
                let ti: u16 = (&crate::frodo_kem::cdf_table640)[i1 as usize];
                let samplei: u16 = (ti.wrapping_sub(prnd) as u32 as u16).wrapping_shr(15u32);
                (&mut sample)[0usize] = samplei.wrapping_add(sample0)
            };
            let sample0: u16 = (&sample)[0usize];
            res[i.wrapping_mul(n2).wrapping_add(i0) as usize] =
                ((! sign).wrapping_add(1u16) ^ sample0).wrapping_add(sign)
        }
    }
}

#[inline] pub(crate) fn frodo_sample_matrix640(n1: u32, n2: u32, r: &[u8], res: &mut [u16])
{
    (res[0usize..n1.wrapping_mul(n2) as usize]).copy_from_slice(
        &vec![0u16; n1.wrapping_mul(n2) as usize].into_boxed_slice()
    );
    for i in 0u32..n1
    {
        for i0 in 0u32..n2
        {
            let resij: (&[u8], &[u8]) =
                r.split_at(2u32.wrapping_mul(n2.wrapping_mul(i).wrapping_add(i0)) as usize);
            let u: u16 = lowstar::endianness::load16_le(resij.1);
            let uu____0: u16 = u;
            let prnd: u16 = uu____0.wrapping_shr(1u32);
            let sign: u16 = uu____0 & 1u16;
            let mut sample: [u16; 1] = [0u16; 1usize];
            let bound: u32 = 12u32;
            for i1 in 0u32..bound
            {
                let sample0: u16 = (&sample)[0usize];
                let ti: u16 = (&crate::frodo_kem::cdf_table640)[i1 as usize];
                let samplei: u16 = (ti.wrapping_sub(prnd) as u32 as u16).wrapping_shr(15u32);
                (&mut sample)[0usize] = samplei.wrapping_add(sample0)
            };
            let sample0: u16 = (&sample)[0usize];
            res[i.wrapping_mul(n2).wrapping_add(i0) as usize] =
                ((! sign).wrapping_add(1u16) ^ sample0).wrapping_add(sign)
        }
    }
}

#[inline] pub(crate) fn frodo_sample_matrix976(n1: u32, n2: u32, r: &[u8], res: &mut [u16])
{
    (res[0usize..n1.wrapping_mul(n2) as usize]).copy_from_slice(
        &vec![0u16; n1.wrapping_mul(n2) as usize].into_boxed_slice()
    );
    for i in 0u32..n1
    {
        for i0 in 0u32..n2
        {
            let resij: (&[u8], &[u8]) =
                r.split_at(2u32.wrapping_mul(n2.wrapping_mul(i).wrapping_add(i0)) as usize);
            let u: u16 = lowstar::endianness::load16_le(resij.1);
            let uu____0: u16 = u;
            let prnd: u16 = uu____0.wrapping_shr(1u32);
            let sign: u16 = uu____0 & 1u16;
            let mut sample: [u16; 1] = [0u16; 1usize];
            let bound: u32 = 10u32;
            for i1 in 0u32..bound
            {
                let sample0: u16 = (&sample)[0usize];
                let ti: u16 = (&crate::frodo_kem::cdf_table976)[i1 as usize];
                let samplei: u16 = (ti.wrapping_sub(prnd) as u32 as u16).wrapping_shr(15u32);
                (&mut sample)[0usize] = samplei.wrapping_add(sample0)
            };
            let sample0: u16 = (&sample)[0usize];
            res[i.wrapping_mul(n2).wrapping_add(i0) as usize] =
                ((! sign).wrapping_add(1u16) ^ sample0).wrapping_add(sign)
        }
    }
}

#[inline] pub(crate) fn frodo_sample_matrix1344(n1: u32, n2: u32, r: &[u8], res: &mut [u16])
{
    (res[0usize..n1.wrapping_mul(n2) as usize]).copy_from_slice(
        &vec![0u16; n1.wrapping_mul(n2) as usize].into_boxed_slice()
    );
    for i in 0u32..n1
    {
        for i0 in 0u32..n2
        {
            let resij: (&[u8], &[u8]) =
                r.split_at(2u32.wrapping_mul(n2.wrapping_mul(i).wrapping_add(i0)) as usize);
            let u: u16 = lowstar::endianness::load16_le(resij.1);
            let uu____0: u16 = u;
            let prnd: u16 = uu____0.wrapping_shr(1u32);
            let sign: u16 = uu____0 & 1u16;
            let mut sample: [u16; 1] = [0u16; 1usize];
            let bound: u32 = 6u32;
            for i1 in 0u32..bound
            {
                let sample0: u16 = (&sample)[0usize];
                let ti: u16 = (&crate::frodo_kem::cdf_table1344)[i1 as usize];
                let samplei: u16 = (ti.wrapping_sub(prnd) as u32 as u16).wrapping_shr(15u32);
                (&mut sample)[0usize] = samplei.wrapping_add(sample0)
            };
            let sample0: u16 = (&sample)[0usize];
            res[i.wrapping_mul(n2).wrapping_add(i0) as usize] =
                ((! sign).wrapping_add(1u16) ^ sample0).wrapping_add(sign)
        }
    }
}

pub(crate) fn randombytes_(len: u32, res: &mut [u8])
{
    let b: bool = lib::randombuffer_system::randombytes(res, len);
    lowstar::ignore::ignore::<bool>(b)
}

#[inline] pub(crate) fn frodo_pack(n1: u32, n2: u32, d: u32, a: &[u16], res: &mut [u8])
{
    let n: u32 = n1.wrapping_mul(n2).wrapping_div(8u32);
    for i in 0u32..n
    {
        let a1: (&[u16], &[u16]) = a.split_at(8u32.wrapping_mul(i) as usize);
        let r: (&mut [u8], &mut [u8]) = res.split_at_mut(d.wrapping_mul(i) as usize);
        let maskd: u16 = (1u32.wrapping_shl(d) as u16).wrapping_sub(1u16);
        let mut v16: [u8; 16] = [0u8; 16usize];
        let a0: u16 = a1.1[0usize] & maskd;
        let a11: u16 = a1.1[1usize] & maskd;
        let a2: u16 = a1.1[2usize] & maskd;
        let a3: u16 = a1.1[3usize] & maskd;
        let a4: u16 = a1.1[4usize] & maskd;
        let a5: u16 = a1.1[5usize] & maskd;
        let a6: u16 = a1.1[6usize] & maskd;
        let a7: u16 = a1.1[7usize] & maskd;
        let templong: fstar::uint128::uint128 =
            fstar::uint128::logor(
                fstar::uint128::logor(
                    fstar::uint128::logor(
                        fstar::uint128::logor(
                            fstar::uint128::logor(
                                fstar::uint128::logor(
                                    fstar::uint128::logor(
                                        fstar::uint128::shift_left(
                                            fstar::uint128::uint64_to_uint128(a0 as u64),
                                            7u32.wrapping_mul(d)
                                        ),
                                        fstar::uint128::shift_left(
                                            fstar::uint128::uint64_to_uint128(a11 as u64),
                                            6u32.wrapping_mul(d)
                                        )
                                    ),
                                    fstar::uint128::shift_left(
                                        fstar::uint128::uint64_to_uint128(a2 as u64),
                                        5u32.wrapping_mul(d)
                                    )
                                ),
                                fstar::uint128::shift_left(
                                    fstar::uint128::uint64_to_uint128(a3 as u64),
                                    4u32.wrapping_mul(d)
                                )
                            ),
                            fstar::uint128::shift_left(
                                fstar::uint128::uint64_to_uint128(a4 as u64),
                                3u32.wrapping_mul(d)
                            )
                        ),
                        fstar::uint128::shift_left(
                            fstar::uint128::uint64_to_uint128(a5 as u64),
                            2u32.wrapping_mul(d)
                        )
                    ),
                    fstar::uint128::shift_left(
                        fstar::uint128::uint64_to_uint128(a6 as u64),
                        1u32.wrapping_mul(d)
                    )
                ),
                fstar::uint128::shift_left(
                    fstar::uint128::uint64_to_uint128(a7 as u64),
                    0u32.wrapping_mul(d)
                )
            );
        lowstar::endianness::store128_be(&mut v16, templong);
        let src: (&[u8], &[u8]) = v16.split_at(16u32.wrapping_sub(d) as usize);
        (r.1[0usize..d as usize]).copy_from_slice(&src.1[0usize..d as usize])
    }
}

#[inline] pub(crate) fn frodo_unpack(n1: u32, n2: u32, d: u32, b: &[u8], res: &mut [u16])
{
    let n: u32 = n1.wrapping_mul(n2).wrapping_div(8u32);
    for i in 0u32..n
    {
        let b1: (&[u8], &[u8]) = b.split_at(d.wrapping_mul(i) as usize);
        let r: (&mut [u16], &mut [u16]) = res.split_at_mut(8u32.wrapping_mul(i) as usize);
        let maskd: u16 = (1u32.wrapping_shl(d) as u16).wrapping_sub(1u16);
        let mut src: [u8; 16] = [0u8; 16usize];
        ((&mut src)[16u32.wrapping_sub(d) as usize..16u32.wrapping_sub(d) as usize + d as usize]).copy_from_slice(
            &b1.1[0usize..d as usize]
        );
        let u: fstar::uint128::uint128 = lowstar::endianness::load128_be(&src);
        let templong: fstar::uint128::uint128 = u;
        r.1[0usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 7u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[1usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 6u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[2usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 5u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[3usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 4u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[4usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 3u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[5usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 2u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[6usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 1u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd;
        r.1[7usize] =
            fstar::uint128::uint128_to_uint64(
                fstar::uint128::shift_right(templong, 0u32.wrapping_mul(d))
            )
            as
            u16
            &
            maskd
    }
}

#[inline] pub(crate) fn frodo_key_encode(logq: u32, b: u32, n: u32, a: &[u8], res: &mut [u16])
{
    for i in 0u32..n
    {
        let mut v8: [u8; 8] = [0u8; 8usize];
        let chunk: (&[u8], &[u8]) = a.split_at(i.wrapping_mul(b) as usize);
        ((&mut v8)[0usize..b as usize]).copy_from_slice(&chunk.1[0usize..b as usize]);
        let u: u64 = lowstar::endianness::load64_le(&v8);
        let x: u64 = u;
        let x0: u64 = x;
        krml::unroll_for!(
            8,
            "i0",
            0u32,
            1u32,
            {
                let rk: u64 =
                    x0.wrapping_shr(b.wrapping_mul(i0)) & 1u64.wrapping_shl(b).wrapping_sub(1u64);
                res[i.wrapping_mul(n).wrapping_add(i0) as usize] =
                    (rk as u16).wrapping_shl(logq.wrapping_sub(b))
            }
        )
    }
}

#[inline] pub(crate) fn frodo_key_decode(logq: u32, b: u32, n: u32, a: &[u16], res: &mut [u8])
{
    for i in 0u32..n
    {
        let mut templong: [u64; 1] = [0u64; 1usize];
        krml::unroll_for!(
            8,
            "i0",
            0u32,
            1u32,
            {
                let aik: u16 = a[i.wrapping_mul(n).wrapping_add(i0) as usize];
                let res1: u16 =
                    aik.wrapping_add(1u16.wrapping_shl(logq.wrapping_sub(b).wrapping_sub(1u32))).wrapping_shr(
                        logq.wrapping_sub(b)
                    );
                (&mut templong)[0usize] =
                    (&templong)[0usize]
                    |
                    ((res1 & 1u16.wrapping_shl(b).wrapping_sub(1u16)) as u64).wrapping_shl(
                        b.wrapping_mul(i0)
                    )
            }
        );
        let templong0: u64 = (&templong)[0usize];
        let mut v8: [u8; 8] = [0u8; 8usize];
        lowstar::endianness::store64_le(&mut v8, templong0);
        let tmp: (&[u8], &[u8]) = v8.split_at(0usize);
        (res[i.wrapping_mul(b) as usize..i.wrapping_mul(b) as usize + b as usize]).copy_from_slice(
            &tmp.1[0usize..b as usize]
        )
    }
}
