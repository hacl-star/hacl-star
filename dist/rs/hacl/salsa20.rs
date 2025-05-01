#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn quarter_round(st: &mut [u32], a: u32, b: u32, c: u32, d: u32)
{
    let sta: u32 = st[b as usize];
    let stb: u32 = st[a as usize];
    let std: u32 = st[d as usize];
    let sta1: u32 =
        sta ^ (stb.wrapping_add(std).wrapping_shl(7u32) | stb.wrapping_add(std).wrapping_shr(25u32));
    st[b as usize] = sta1;
    let sta0: u32 = st[c as usize];
    let stb0: u32 = st[b as usize];
    let std0: u32 = st[a as usize];
    let sta10: u32 =
        sta0
        ^
        (stb0.wrapping_add(std0).wrapping_shl(9u32) | stb0.wrapping_add(std0).wrapping_shr(23u32));
    st[c as usize] = sta10;
    let sta2: u32 = st[d as usize];
    let stb1: u32 = st[c as usize];
    let std1: u32 = st[b as usize];
    let sta11: u32 =
        sta2
        ^
        (stb1.wrapping_add(std1).wrapping_shl(13u32) | stb1.wrapping_add(std1).wrapping_shr(19u32));
    st[d as usize] = sta11;
    let sta3: u32 = st[a as usize];
    let stb2: u32 = st[d as usize];
    let std2: u32 = st[c as usize];
    let sta12: u32 =
        sta3
        ^
        (stb2.wrapping_add(std2).wrapping_shl(18u32) | stb2.wrapping_add(std2).wrapping_shr(14u32));
    st[a as usize] = sta12
}

#[inline] fn double_round(st: &mut [u32])
{
    crate::salsa20::quarter_round(st, 0u32, 4u32, 8u32, 12u32);
    crate::salsa20::quarter_round(st, 5u32, 9u32, 13u32, 1u32);
    crate::salsa20::quarter_round(st, 10u32, 14u32, 2u32, 6u32);
    crate::salsa20::quarter_round(st, 15u32, 3u32, 7u32, 11u32);
    crate::salsa20::quarter_round(st, 0u32, 1u32, 2u32, 3u32);
    crate::salsa20::quarter_round(st, 5u32, 6u32, 7u32, 4u32);
    crate::salsa20::quarter_round(st, 10u32, 11u32, 8u32, 9u32);
    crate::salsa20::quarter_round(st, 15u32, 12u32, 13u32, 14u32)
}

#[inline] fn rounds(st: &mut [u32])
{
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st);
    crate::salsa20::double_round(st)
}

#[inline] fn salsa20_core(k: &mut [u32], ctx: &[u32], ctr: u32)
{
    (k[0usize..16usize]).copy_from_slice(&ctx[0usize..16usize]);
    let ctr_u32: u32 = ctr;
    k[8usize] = (k[8usize]).wrapping_add(ctr_u32);
    crate::salsa20::rounds(k);
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = (k[i as usize]).wrapping_add(ctx[i as usize]);
            let os: (&mut [u32], &mut [u32]) = k.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    k[8usize] = (k[8usize]).wrapping_add(ctr_u32)
}

#[inline] fn salsa20_key_block0(out: &mut [u8], key: &[u8], n: &[u8])
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    let mut k: [u32; 16] = [0u32; 16usize];
    let mut k32: [u32; 8] = [0u32; 8usize];
    let mut n32: [u32; 2] = [0u32; 2usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = key.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = k32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = n.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = n32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    (&mut ctx)[0usize] = 0x61707865u32;
    let k0: (&[u32], &[u32]) = k32.split_at(0usize);
    let k1: (&[u32], &[u32]) = (k0.1).split_at(4usize);
    ((&mut ctx)[1usize..1usize + 4usize]).copy_from_slice(&k1.0[0usize..4usize]);
    (&mut ctx)[5usize] = 0x3320646eu32;
    ((&mut ctx)[6usize..6usize + 2usize]).copy_from_slice(&(&n32)[0usize..2usize]);
    (&mut ctx)[8usize] = 0u32;
    (&mut ctx)[9usize] = 0u32;
    (&mut ctx)[10usize] = 0x79622d32u32;
    ((&mut ctx)[11usize..11usize + 4usize]).copy_from_slice(&k1.1[0usize..4usize]);
    (&mut ctx)[15usize] = 0x6b206574u32;
    crate::salsa20::salsa20_core(&mut k, &ctx, 0u32);
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store32_le(&mut out[i.wrapping_mul(4u32) as usize..], (&k)[i as usize])
    )
}

#[inline] fn salsa20_encrypt(
    len: u32,
    out: &mut [u8],
    text: &[u8],
    key: &[u8],
    n: &[u8],
    ctr: u32
)
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    let mut k32: [u32; 8] = [0u32; 8usize];
    let mut n32: [u32; 2] = [0u32; 2usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = key.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = k32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = n.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = n32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    (&mut ctx)[0usize] = 0x61707865u32;
    let k0: (&[u32], &[u32]) = k32.split_at(0usize);
    let k1: (&[u32], &[u32]) = (k0.1).split_at(4usize);
    ((&mut ctx)[1usize..1usize + 4usize]).copy_from_slice(&k1.0[0usize..4usize]);
    (&mut ctx)[5usize] = 0x3320646eu32;
    ((&mut ctx)[6usize..6usize + 2usize]).copy_from_slice(&(&n32)[0usize..2usize]);
    (&mut ctx)[8usize] = ctr;
    (&mut ctx)[9usize] = 0u32;
    (&mut ctx)[10usize] = 0x79622d32u32;
    ((&mut ctx)[11usize..11usize + 4usize]).copy_from_slice(&k1.1[0usize..4usize]);
    (&mut ctx)[15usize] = 0x6b206574u32;
    let k: [u32; 16] = [0u32; 16usize];
    lowstar::ignore::ignore::<&[u32]>(&k);
    let rem: u32 = len.wrapping_rem(64u32);
    let nb: u32 = len.wrapping_div(64u32);
    let rem1: u32 = len.wrapping_rem(64u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(64u32) as usize);
        let uu____1: (&[u8], &[u8]) = text.split_at(i.wrapping_mul(64u32) as usize);
        let mut k10: [u32; 16] = [0u32; 16usize];
        crate::salsa20::salsa20_core(&mut k10, &ctx, i);
        let mut bl: [u32; 16] = [0u32; 16usize];
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            {
                let bj: (&[u8], &[u8]) = (uu____1.1).split_at(i0.wrapping_mul(4u32) as usize);
                let u: u32 = lowstar::endianness::load32_le(bj.1);
                let r: u32 = u;
                let x: u32 = r;
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i0 as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            {
                let x: u32 = (&bl)[i0 as usize] ^ (&k10)[i0 as usize];
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i0 as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store32_le(
                &mut uu____0.1[i0.wrapping_mul(4u32) as usize..],
                (&bl)[i0 as usize]
            )
        )
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(64u32) as usize);
        let mut plain: [u8; 64] = [0u8; 64usize];
        ((&mut plain)[0usize..rem as usize]).copy_from_slice(
            &(&text[nb.wrapping_mul(64u32) as usize..])[0usize..rem as usize]
        );
        let mut k10: [u32; 16] = [0u32; 16usize];
        crate::salsa20::salsa20_core(&mut k10, &ctx, nb);
        let mut bl: [u32; 16] = [0u32; 16usize];
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            {
                let bj: (&[u8], &[u8]) = plain.split_at(i.wrapping_mul(4u32) as usize);
                let u: u32 = lowstar::endianness::load32_le(bj.1);
                let r: u32 = u;
                let x: u32 = r;
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            {
                let x: u32 = (&bl)[i as usize] ^ (&k10)[i as usize];
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            lowstar::endianness::store32_le(
                &mut (&mut plain)[i.wrapping_mul(4u32) as usize..],
                (&bl)[i as usize]
            )
        );
        (uu____2.1[0usize..rem as usize]).copy_from_slice(
            &(&(&plain)[0usize..])[0usize..rem as usize]
        )
    }
}

#[inline] fn salsa20_decrypt(
    len: u32,
    out: &mut [u8],
    cipher: &[u8],
    key: &[u8],
    n: &[u8],
    ctr: u32
)
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    let mut k32: [u32; 8] = [0u32; 8usize];
    let mut n32: [u32; 2] = [0u32; 2usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = key.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = k32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = n.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = n32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    (&mut ctx)[0usize] = 0x61707865u32;
    let k0: (&[u32], &[u32]) = k32.split_at(0usize);
    let k1: (&[u32], &[u32]) = (k0.1).split_at(4usize);
    ((&mut ctx)[1usize..1usize + 4usize]).copy_from_slice(&k1.0[0usize..4usize]);
    (&mut ctx)[5usize] = 0x3320646eu32;
    ((&mut ctx)[6usize..6usize + 2usize]).copy_from_slice(&(&n32)[0usize..2usize]);
    (&mut ctx)[8usize] = ctr;
    (&mut ctx)[9usize] = 0u32;
    (&mut ctx)[10usize] = 0x79622d32u32;
    ((&mut ctx)[11usize..11usize + 4usize]).copy_from_slice(&k1.1[0usize..4usize]);
    (&mut ctx)[15usize] = 0x6b206574u32;
    let k: [u32; 16] = [0u32; 16usize];
    lowstar::ignore::ignore::<&[u32]>(&k);
    let rem: u32 = len.wrapping_rem(64u32);
    let nb: u32 = len.wrapping_div(64u32);
    let rem1: u32 = len.wrapping_rem(64u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(64u32) as usize);
        let uu____1: (&[u8], &[u8]) = cipher.split_at(i.wrapping_mul(64u32) as usize);
        let mut k10: [u32; 16] = [0u32; 16usize];
        crate::salsa20::salsa20_core(&mut k10, &ctx, i);
        let mut bl: [u32; 16] = [0u32; 16usize];
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            {
                let bj: (&[u8], &[u8]) = (uu____1.1).split_at(i0.wrapping_mul(4u32) as usize);
                let u: u32 = lowstar::endianness::load32_le(bj.1);
                let r: u32 = u;
                let x: u32 = r;
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i0 as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            {
                let x: u32 = (&bl)[i0 as usize] ^ (&k10)[i0 as usize];
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i0 as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store32_le(
                &mut uu____0.1[i0.wrapping_mul(4u32) as usize..],
                (&bl)[i0 as usize]
            )
        )
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(64u32) as usize);
        let mut plain: [u8; 64] = [0u8; 64usize];
        ((&mut plain)[0usize..rem as usize]).copy_from_slice(
            &(&cipher[nb.wrapping_mul(64u32) as usize..])[0usize..rem as usize]
        );
        let mut k10: [u32; 16] = [0u32; 16usize];
        crate::salsa20::salsa20_core(&mut k10, &ctx, nb);
        let mut bl: [u32; 16] = [0u32; 16usize];
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            {
                let bj: (&[u8], &[u8]) = plain.split_at(i.wrapping_mul(4u32) as usize);
                let u: u32 = lowstar::endianness::load32_le(bj.1);
                let r: u32 = u;
                let x: u32 = r;
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            {
                let x: u32 = (&bl)[i as usize] ^ (&k10)[i as usize];
                let os: (&mut [u32], &mut [u32]) = bl.split_at_mut(0usize);
                os.1[i as usize] = x
            }
        );
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            lowstar::endianness::store32_le(
                &mut (&mut plain)[i.wrapping_mul(4u32) as usize..],
                (&bl)[i as usize]
            )
        );
        (uu____2.1[0usize..rem as usize]).copy_from_slice(
            &(&(&plain)[0usize..])[0usize..rem as usize]
        )
    }
}

#[inline] fn hsalsa20(out: &mut [u8], key: &[u8], n: &[u8])
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    let mut k32: [u32; 8] = [0u32; 8usize];
    let mut n32: [u32; 4] = [0u32; 4usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = key.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = k32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = n.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = n32.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let k0: (&[u32], &[u32]) = k32.split_at(0usize);
    let k1: (&[u32], &[u32]) = (k0.1).split_at(4usize);
    (&mut ctx)[0usize] = 0x61707865u32;
    ((&mut ctx)[1usize..1usize + 4usize]).copy_from_slice(&k1.0[0usize..4usize]);
    (&mut ctx)[5usize] = 0x3320646eu32;
    ((&mut ctx)[6usize..6usize + 4usize]).copy_from_slice(&(&n32)[0usize..4usize]);
    (&mut ctx)[10usize] = 0x79622d32u32;
    ((&mut ctx)[11usize..11usize + 4usize]).copy_from_slice(&k1.1[0usize..4usize]);
    (&mut ctx)[15usize] = 0x6b206574u32;
    crate::salsa20::rounds(&mut ctx);
    let r0: u32 = (&ctx)[0usize];
    let r1: u32 = (&ctx)[5usize];
    let r2: u32 = (&ctx)[10usize];
    let r3: u32 = (&ctx)[15usize];
    let r4: u32 = (&ctx)[6usize];
    let r5: u32 = (&ctx)[7usize];
    let r6: u32 = (&ctx)[8usize];
    let r7: u32 = (&ctx)[9usize];
    let res: [u32; 8] = [r0, r1, r2, r3, r4, r5, r6, r7];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store32_le(
            &mut out[i.wrapping_mul(4u32) as usize..],
            (&res)[i as usize]
        )
    )
}

pub fn salsa20_encrypt0(len: u32, out: &mut [u8], text: &[u8], key: &[u8], n: &[u8], ctr: u32)
{ crate::salsa20::salsa20_encrypt(len, out, text, key, n, ctr) }

pub fn salsa20_decrypt0(
    len: u32,
    out: &mut [u8],
    cipher: &[u8],
    key: &[u8],
    n: &[u8],
    ctr: u32
)
{ crate::salsa20::salsa20_decrypt(len, out, cipher, key, n, ctr) }

pub fn salsa20_key_block00(out: &mut [u8], key: &[u8], n: &[u8])
{ crate::salsa20::salsa20_key_block0(out, key, n) }

pub fn hsalsa200(out: &mut [u8], key: &[u8], n: &[u8])
{ crate::salsa20::hsalsa20(out, key, n) }
