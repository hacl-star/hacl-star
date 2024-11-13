#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub(crate) const keccak_rotc: [u32; 24] =
    [1u32, 3u32, 6u32, 10u32, 15u32, 21u32, 28u32, 36u32, 45u32, 55u32, 2u32, 14u32, 27u32, 41u32,
        56u32, 8u32, 25u32, 43u32, 62u32, 18u32, 39u32, 61u32, 20u32, 44u32];

pub(crate) const keccak_piln: [u32; 24] =
    [10u32, 7u32, 11u32, 17u32, 18u32, 3u32, 5u32, 16u32, 8u32, 21u32, 24u32, 4u32, 15u32, 23u32,
        19u32, 13u32, 12u32, 2u32, 20u32, 14u32, 22u32, 9u32, 6u32, 1u32];

pub(crate) const keccak_rndc: [u64; 24] =
    [0x0000000000000001u64, 0x0000000000008082u64, 0x800000000000808au64, 0x8000000080008000u64,
        0x000000000000808bu64, 0x0000000080000001u64, 0x8000000080008081u64, 0x8000000000008009u64,
        0x000000000000008au64, 0x0000000000000088u64, 0x0000000080008009u64, 0x000000008000000au64,
        0x000000008000808bu64, 0x800000000000008bu64, 0x8000000000008089u64, 0x8000000000008003u64,
        0x8000000000008002u64, 0x8000000000000080u64, 0x000000000000800au64, 0x800000008000000au64,
        0x8000000080008081u64, 0x8000000000008080u64, 0x0000000080000001u64, 0x8000000080008008u64];

fn absorb_inner_32(b: &mut [u8], s: &mut [u64])
{
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, s[i as usize] ^= (&mut ws)[i as usize]);
    krml::unroll_for!(
        24,
        "i",
        0u32,
        1u32,
        {
            let mut _C: [u64; 5] = [0u64; 5usize];
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                (&mut _C)[i0 as usize] =
                    s[i0.wrapping_add(0u32) as usize]
                    ^
                    (s[i0.wrapping_add(5u32) as usize]
                    ^
                    (s[i0.wrapping_add(10u32) as usize]
                    ^
                    (s[i0.wrapping_add(15u32) as usize] ^ s[i0.wrapping_add(20u32) as usize])))
            );
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let uu____0: u64 = (&mut _C)[i0.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                    let _D: u64 =
                        (&mut _C)[i0.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                        ^
                        (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize] ^= _D
                    )
                }
            );
            let x: u64 = s[1usize];
            let mut current: [u64; 1] = [x; 1usize];
            krml::unroll_for!(
                24,
                "i0",
                0u32,
                1u32,
                {
                    let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i0 as usize];
                    let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i0 as usize];
                    let temp: u64 = s[_Y as usize];
                    let uu____1: u64 = (&mut current)[0usize];
                    s[_Y as usize] =
                        uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                    (&mut current)[0usize] = temp
                }
            );
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let v0: u64 =
                        s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v1: u64 =
                        s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v2: u64 =
                        s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v3: u64 =
                        s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v4: u64 =
                        s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v0;
                    s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v1;
                    s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v2;
                    s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v3;
                    s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v4
                }
            );
            let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i as usize];
            s[0usize] ^= c
        }
    )
}

fn block_len(a: crate::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::streaming_types::hash_alg::SHA3_224 => 144u32,
        crate::streaming_types::hash_alg::SHA3_256 => 136u32,
        crate::streaming_types::hash_alg::SHA3_384 => 104u32,
        crate::streaming_types::hash_alg::SHA3_512 => 72u32,
        crate::streaming_types::hash_alg::Shake128 => 168u32,
        crate::streaming_types::hash_alg::Shake256 => 136u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

fn hash_len(a: crate::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::streaming_types::hash_alg::SHA3_224 => 28u32,
        crate::streaming_types::hash_alg::SHA3_256 => 32u32,
        crate::streaming_types::hash_alg::SHA3_384 => 48u32,
        crate::streaming_types::hash_alg::SHA3_512 => 64u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub(crate) fn update_multi_sha3(
    a: crate::streaming_types::hash_alg,
    s: &mut [u64],
    blocks: &mut [u8],
    n_blocks: u32
)
{
    let l: u32 = (crate::hash_sha3::block_len(a)).wrapping_mul(n_blocks);
    for i in 0u32..l.wrapping_div(crate::hash_sha3::block_len(a))
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = blocks;
        let bl0: &mut [u8] = b·;
        let uu____0: (&mut [u8], &mut [u8]) =
            b0.split_at_mut(i.wrapping_mul(crate::hash_sha3::block_len(a)) as usize);
        (bl0[0usize..crate::hash_sha3::block_len(a) as usize]).copy_from_slice(
            &uu____0.1[0usize..crate::hash_sha3::block_len(a) as usize]
        );
        let unused: u32 = crate::hash_sha3::block_len(a);
        lowstar::ignore::ignore::<u32>(unused);
        crate::hash_sha3::absorb_inner_32(b·, s)
    }
}

pub(crate) fn update_last_sha3(
    a: crate::streaming_types::hash_alg,
    s: &mut [u64],
    input: &mut [u8],
    input_len: u32
)
{
    let suffix: u8 =
        if
        a == crate::streaming_types::hash_alg::Shake128
        ||
        a == crate::streaming_types::hash_alg::Shake256
        { 0x1fu8 }
        else
        { 0x06u8 };
    let len: u32 = crate::hash_sha3::block_len(a);
    if input_len == len
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = input;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..len as usize]).copy_from_slice(
            &(&mut b0[0u32.wrapping_mul(len) as usize..])[0usize..len as usize]
        );
        crate::hash_sha3::absorb_inner_32(b·, s);
        let mut b1: [u8; 256] = [0u8; 256usize];
        let b·0: &mut [u8] = &mut b1;
        let rem: u32 = 0u32.wrapping_rem(len);
        let b00: (&mut [u8], &mut [u8]) = input.split_at_mut(input_len as usize);
        let bl00: &mut [u8] = b·0;
        (bl00[0usize..rem as usize]).copy_from_slice(
            &(&mut b00.1[0u32.wrapping_sub(rem) as usize..])[0usize..rem as usize]
        );
        let b01: &mut [u8] = b·0;
        b01[0u32.wrapping_rem(len) as usize] = suffix;
        let mut ws: [u64; 32] = [0u64; 32usize];
        let b2: &mut [u8] = b·0;
        let u: u64 = lowstar::endianness::load64_le(&mut b2[0usize..]);
        (&mut ws)[0usize] = u;
        let u0: u64 = lowstar::endianness::load64_le(&mut b2[8usize..]);
        (&mut ws)[1usize] = u0;
        let u1: u64 = lowstar::endianness::load64_le(&mut b2[16usize..]);
        (&mut ws)[2usize] = u1;
        let u2: u64 = lowstar::endianness::load64_le(&mut b2[24usize..]);
        (&mut ws)[3usize] = u2;
        let u3: u64 = lowstar::endianness::load64_le(&mut b2[32usize..]);
        (&mut ws)[4usize] = u3;
        let u4: u64 = lowstar::endianness::load64_le(&mut b2[40usize..]);
        (&mut ws)[5usize] = u4;
        let u5: u64 = lowstar::endianness::load64_le(&mut b2[48usize..]);
        (&mut ws)[6usize] = u5;
        let u6: u64 = lowstar::endianness::load64_le(&mut b2[56usize..]);
        (&mut ws)[7usize] = u6;
        let u7: u64 = lowstar::endianness::load64_le(&mut b2[64usize..]);
        (&mut ws)[8usize] = u7;
        let u8: u64 = lowstar::endianness::load64_le(&mut b2[72usize..]);
        (&mut ws)[9usize] = u8;
        let u9: u64 = lowstar::endianness::load64_le(&mut b2[80usize..]);
        (&mut ws)[10usize] = u9;
        let u10: u64 = lowstar::endianness::load64_le(&mut b2[88usize..]);
        (&mut ws)[11usize] = u10;
        let u11: u64 = lowstar::endianness::load64_le(&mut b2[96usize..]);
        (&mut ws)[12usize] = u11;
        let u12: u64 = lowstar::endianness::load64_le(&mut b2[104usize..]);
        (&mut ws)[13usize] = u12;
        let u13: u64 = lowstar::endianness::load64_le(&mut b2[112usize..]);
        (&mut ws)[14usize] = u13;
        let u14: u64 = lowstar::endianness::load64_le(&mut b2[120usize..]);
        (&mut ws)[15usize] = u14;
        let u15: u64 = lowstar::endianness::load64_le(&mut b2[128usize..]);
        (&mut ws)[16usize] = u15;
        let u16: u64 = lowstar::endianness::load64_le(&mut b2[136usize..]);
        (&mut ws)[17usize] = u16;
        let u17: u64 = lowstar::endianness::load64_le(&mut b2[144usize..]);
        (&mut ws)[18usize] = u17;
        let u18: u64 = lowstar::endianness::load64_le(&mut b2[152usize..]);
        (&mut ws)[19usize] = u18;
        let u19: u64 = lowstar::endianness::load64_le(&mut b2[160usize..]);
        (&mut ws)[20usize] = u19;
        let u20: u64 = lowstar::endianness::load64_le(&mut b2[168usize..]);
        (&mut ws)[21usize] = u20;
        let u21: u64 = lowstar::endianness::load64_le(&mut b2[176usize..]);
        (&mut ws)[22usize] = u21;
        let u22: u64 = lowstar::endianness::load64_le(&mut b2[184usize..]);
        (&mut ws)[23usize] = u22;
        let u23: u64 = lowstar::endianness::load64_le(&mut b2[192usize..]);
        (&mut ws)[24usize] = u23;
        let u24: u64 = lowstar::endianness::load64_le(&mut b2[200usize..]);
        (&mut ws)[25usize] = u24;
        let u25: u64 = lowstar::endianness::load64_le(&mut b2[208usize..]);
        (&mut ws)[26usize] = u25;
        let u26: u64 = lowstar::endianness::load64_le(&mut b2[216usize..]);
        (&mut ws)[27usize] = u26;
        let u27: u64 = lowstar::endianness::load64_le(&mut b2[224usize..]);
        (&mut ws)[28usize] = u27;
        let u28: u64 = lowstar::endianness::load64_le(&mut b2[232usize..]);
        (&mut ws)[29usize] = u28;
        let u29: u64 = lowstar::endianness::load64_le(&mut b2[240usize..]);
        (&mut ws)[30usize] = u29;
        let u30: u64 = lowstar::endianness::load64_le(&mut b2[248usize..]);
        (&mut ws)[31usize] = u30;
        krml::unroll_for!(25, "i", 0u32, 1u32, s[i as usize] ^= (&mut ws)[i as usize]);
        if suffix & 0x80u8 != 0u8 && 0u32.wrapping_rem(len) == len.wrapping_sub(1u32)
        {
            krml::unroll_for!(
                24,
                "i",
                0u32,
                1u32,
                {
                    let mut _C: [u64; 5] = [0u64; 5usize];
                    krml::unroll_for!(
                        5,
                        "i0",
                        0u32,
                        1u32,
                        (&mut _C)[i0 as usize] =
                            s[i0.wrapping_add(0u32) as usize]
                            ^
                            (s[i0.wrapping_add(5u32) as usize]
                            ^
                            (s[i0.wrapping_add(10u32) as usize]
                            ^
                            (s[i0.wrapping_add(15u32) as usize] ^ s[i0.wrapping_add(20u32) as usize])))
                    );
                    krml::unroll_for!(
                        5,
                        "i0",
                        0u32,
                        1u32,
                        {
                            let uu____0: u64 =
                                (&mut _C)[i0.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                            let _D: u64 =
                                (&mut _C)[i0.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                                ^
                                (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                            krml::unroll_for!(
                                5,
                                "i1",
                                0u32,
                                1u32,
                                s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize] ^= _D
                            )
                        }
                    );
                    let x: u64 = s[1usize];
                    let mut current: [u64; 1] = [x; 1usize];
                    krml::unroll_for!(
                        24,
                        "i0",
                        0u32,
                        1u32,
                        {
                            let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i0 as usize];
                            let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i0 as usize];
                            let temp: u64 = s[_Y as usize];
                            let uu____1: u64 = (&mut current)[0usize];
                            s[_Y as usize] =
                                uu____1.wrapping_shl(r)
                                |
                                uu____1.wrapping_shr(64u32.wrapping_sub(r));
                            (&mut current)[0usize] = temp
                        }
                    );
                    krml::unroll_for!(
                        5,
                        "i0",
                        0u32,
                        1u32,
                        {
                            let v0: u64 =
                                s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v1: u64 =
                                s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v2: u64 =
                                s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v3: u64 =
                                s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v4: u64 =
                                s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v0;
                            s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v1;
                            s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v2;
                            s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v3;
                            s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v4
                        }
                    );
                    let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i as usize];
                    s[0usize] ^= c
                }
            )
        };
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b4: &mut [u8] = &mut b3;
        let b02: &mut [u8] = b4;
        b02[len.wrapping_sub(1u32) as usize] = 0x80u8;
        crate::hash_sha3::absorb_inner_32(b4, s)
    }
    else
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let rem: u32 = input_len.wrapping_rem(len);
        let b0: &mut [u8] = input;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rem as usize]).copy_from_slice(
            &(&mut b0[input_len.wrapping_sub(rem) as usize..])[0usize..rem as usize]
        );
        let b00: &mut [u8] = b·;
        b00[input_len.wrapping_rem(len) as usize] = suffix;
        let mut ws: [u64; 32] = [0u64; 32usize];
        let b1: &mut [u8] = b·;
        let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
        (&mut ws)[0usize] = u;
        let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
        (&mut ws)[1usize] = u0;
        let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
        (&mut ws)[2usize] = u1;
        let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
        (&mut ws)[3usize] = u2;
        let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
        (&mut ws)[4usize] = u3;
        let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
        (&mut ws)[5usize] = u4;
        let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
        (&mut ws)[6usize] = u5;
        let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
        (&mut ws)[7usize] = u6;
        let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
        (&mut ws)[8usize] = u7;
        let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
        (&mut ws)[9usize] = u8;
        let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
        (&mut ws)[10usize] = u9;
        let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
        (&mut ws)[11usize] = u10;
        let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
        (&mut ws)[12usize] = u11;
        let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
        (&mut ws)[13usize] = u12;
        let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
        (&mut ws)[14usize] = u13;
        let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
        (&mut ws)[15usize] = u14;
        let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
        (&mut ws)[16usize] = u15;
        let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
        (&mut ws)[17usize] = u16;
        let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
        (&mut ws)[18usize] = u17;
        let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
        (&mut ws)[19usize] = u18;
        let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
        (&mut ws)[20usize] = u19;
        let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
        (&mut ws)[21usize] = u20;
        let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
        (&mut ws)[22usize] = u21;
        let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
        (&mut ws)[23usize] = u22;
        let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
        (&mut ws)[24usize] = u23;
        let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
        (&mut ws)[25usize] = u24;
        let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
        (&mut ws)[26usize] = u25;
        let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
        (&mut ws)[27usize] = u26;
        let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
        (&mut ws)[28usize] = u27;
        let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
        (&mut ws)[29usize] = u28;
        let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
        (&mut ws)[30usize] = u29;
        let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
        (&mut ws)[31usize] = u30;
        krml::unroll_for!(25, "i", 0u32, 1u32, s[i as usize] ^= (&mut ws)[i as usize]);
        if suffix & 0x80u8 != 0u8 && input_len.wrapping_rem(len) == len.wrapping_sub(1u32)
        {
            krml::unroll_for!(
                24,
                "i",
                0u32,
                1u32,
                {
                    let mut _C: [u64; 5] = [0u64; 5usize];
                    krml::unroll_for!(
                        5,
                        "i0",
                        0u32,
                        1u32,
                        (&mut _C)[i0 as usize] =
                            s[i0.wrapping_add(0u32) as usize]
                            ^
                            (s[i0.wrapping_add(5u32) as usize]
                            ^
                            (s[i0.wrapping_add(10u32) as usize]
                            ^
                            (s[i0.wrapping_add(15u32) as usize] ^ s[i0.wrapping_add(20u32) as usize])))
                    );
                    krml::unroll_for!(
                        5,
                        "i0",
                        0u32,
                        1u32,
                        {
                            let uu____2: u64 =
                                (&mut _C)[i0.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                            let _D: u64 =
                                (&mut _C)[i0.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                                ^
                                (uu____2.wrapping_shl(1u32) | uu____2.wrapping_shr(63u32));
                            krml::unroll_for!(
                                5,
                                "i1",
                                0u32,
                                1u32,
                                s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize] ^= _D
                            )
                        }
                    );
                    let x: u64 = s[1usize];
                    let mut current: [u64; 1] = [x; 1usize];
                    krml::unroll_for!(
                        24,
                        "i0",
                        0u32,
                        1u32,
                        {
                            let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i0 as usize];
                            let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i0 as usize];
                            let temp: u64 = s[_Y as usize];
                            let uu____3: u64 = (&mut current)[0usize];
                            s[_Y as usize] =
                                uu____3.wrapping_shl(r)
                                |
                                uu____3.wrapping_shr(64u32.wrapping_sub(r));
                            (&mut current)[0usize] = temp
                        }
                    );
                    krml::unroll_for!(
                        5,
                        "i0",
                        0u32,
                        1u32,
                        {
                            let v0: u64 =
                                s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v1: u64 =
                                s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v2: u64 =
                                s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v3: u64 =
                                s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            let v4: u64 =
                                s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                ^
                                ! s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                                &
                                s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                            s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v0;
                            s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v1;
                            s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v2;
                            s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v3;
                            s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v4
                        }
                    );
                    let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i as usize];
                    s[0usize] ^= c
                }
            )
        };
        let mut b2: [u8; 256] = [0u8; 256usize];
        let b3: &mut [u8] = &mut b2;
        let b01: &mut [u8] = b3;
        b01[len.wrapping_sub(1u32) as usize] = 0x80u8;
        crate::hash_sha3::absorb_inner_32(b3, s)
    }
}

#[derive(PartialEq, Clone)]
pub struct hash_buf
{ pub fst: crate::streaming_types::hash_alg, pub snd: Box<[u64]> }

#[derive(PartialEq, Clone)]
pub struct state_t
{ pub block_state: crate::hash_sha3::hash_buf, pub buf: Box<[u8]>, pub total_len: u64 }

pub fn get_alg(s: &mut [crate::hash_sha3::state_t]) -> crate::streaming_types::hash_alg
{
    let mut block_state: &mut crate::hash_sha3::hash_buf = &mut (s[0usize]).block_state;
    block_state.fst
}

pub fn malloc(a: crate::streaming_types::hash_alg) -> Box<[crate::hash_sha3::state_t]>
{
    let mut buf: Box<[u8]> = vec![0u8; crate::hash_sha3::block_len(a) as usize].into_boxed_slice();
    let mut buf0: Box<[u64]> = vec![0u64; 25usize].into_boxed_slice();
    let mut block_state: crate::hash_sha3::hash_buf =
        crate::hash_sha3::hash_buf { fst: a, snd: buf0 };
    let s: &mut [u64] = &mut block_state.snd;
    (s[0usize..25usize]).copy_from_slice(&[0u64; 25usize]);
    let mut s0: crate::hash_sha3::state_t =
        crate::hash_sha3::state_t { block_state, buf, total_len: 0u32 as u64 };
    let mut p: Box<[crate::hash_sha3::state_t]> = vec![s0].into_boxed_slice();
    p
}

pub fn copy(state: &mut [crate::hash_sha3::state_t]) -> Box<[crate::hash_sha3::state_t]>
{
    let mut block_state0: &mut crate::hash_sha3::hash_buf = &mut (state[0usize]).block_state;
    let buf0: &mut [u8] = &mut (state[0usize]).buf;
    let total_len0: u64 = (state[0usize]).total_len;
    let i: crate::streaming_types::hash_alg = block_state0.fst;
    let mut buf: Box<[u8]> = vec![0u8; crate::hash_sha3::block_len(i) as usize].into_boxed_slice();
    ((&mut buf)[0usize..crate::hash_sha3::block_len(i) as usize]).copy_from_slice(
        &buf0[0usize..crate::hash_sha3::block_len(i) as usize]
    );
    let mut buf1: Box<[u64]> = vec![0u64; 25usize].into_boxed_slice();
    let mut block_state: crate::hash_sha3::hash_buf =
        crate::hash_sha3::hash_buf { fst: i, snd: buf1 };
    let s_src: &mut [u64] = &mut block_state0.snd;
    let s_dst: &mut [u64] = &mut block_state.snd;
    (s_dst[0usize..25usize]).copy_from_slice(&s_src[0usize..25usize]);
    let mut s: crate::hash_sha3::state_t =
        crate::hash_sha3::state_t { block_state, buf, total_len: total_len0 };
    let mut p: Box<[crate::hash_sha3::state_t]> = vec![s].into_boxed_slice();
    p
}

pub fn reset(state: &mut [crate::hash_sha3::state_t])
{
    let mut block_state: &mut crate::hash_sha3::hash_buf = &mut (state[0usize]).block_state;
    let s: &mut [u64] = &mut block_state.snd;
    (s[0usize..25usize]).copy_from_slice(&[0u64; 25usize]);
    let total_len: u64 = 0u32 as u64;
    (state[0usize]).total_len = total_len
}

pub fn update(state: &mut [crate::hash_sha3::state_t], chunk: &mut [u8], chunk_len: u32) ->
    crate::streaming_types::error_code
{
    let mut block_state: &mut crate::hash_sha3::hash_buf = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    let i: crate::streaming_types::hash_alg = block_state.fst;
    if chunk_len as u64 > 0xFFFFFFFFFFFFFFFFu64.wrapping_sub(total_len)
    { crate::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if
            total_len.wrapping_rem(crate::hash_sha3::block_len(i) as u64) == 0u64
            &&
            total_len > 0u64
            { crate::hash_sha3::block_len(i) }
            else
            { total_len.wrapping_rem(crate::hash_sha3::block_len(i) as u64) as u32 };
        if chunk_len <= (crate::hash_sha3::block_len(i)).wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if
                total_len1.wrapping_rem(crate::hash_sha3::block_len(i) as u64) == 0u64
                &&
                total_len1 > 0u64
                { crate::hash_sha3::block_len(i) }
                else
                { total_len1.wrapping_rem(crate::hash_sha3::block_len(i) as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2
        }
        else if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if
                total_len1.wrapping_rem(crate::hash_sha3::block_len(i) as u64) == 0u64
                &&
                total_len1 > 0u64
                { crate::hash_sha3::block_len(i) }
                else
                { total_len1.wrapping_rem(crate::hash_sha3::block_len(i) as u64) as u32 };
            if sz1 != 0u32
            {
                let a1: crate::streaming_types::hash_alg = block_state.fst;
                let s1: &mut [u64] = &mut block_state.snd;
                crate::hash_sha3::update_multi_sha3(
                    a1,
                    s1,
                    buf,
                    (crate::hash_sha3::block_len(i)).wrapping_div(crate::hash_sha3::block_len(a1))
                )
            };
            let ite: u32 =
                if
                (chunk_len as u64).wrapping_rem(crate::hash_sha3::block_len(i) as u64) == 0u64
                &&
                chunk_len as u64 > 0u64
                { crate::hash_sha3::block_len(i) }
                else
                { (chunk_len as u64).wrapping_rem(crate::hash_sha3::block_len(i) as u64) as u32 };
            let n_blocks: u32 =
                chunk_len.wrapping_sub(ite).wrapping_div(crate::hash_sha3::block_len(i));
            let data1_len: u32 = n_blocks.wrapping_mul(crate::hash_sha3::block_len(i));
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            let a1: crate::streaming_types::hash_alg = block_state.fst;
            let s1: &mut [u64] = &mut block_state.snd;
            crate::hash_sha3::update_multi_sha3(
                a1,
                s1,
                data2.0,
                data1_len.wrapping_div(crate::hash_sha3::block_len(a1))
            );
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = (crate::hash_sha3::block_len(i)).wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if
                total_len1.wrapping_rem(crate::hash_sha3::block_len(i) as u64) == 0u64
                &&
                total_len1 > 0u64
                { crate::hash_sha3::block_len(i) }
                else
                { total_len1.wrapping_rem(crate::hash_sha3::block_len(i) as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            (state[0usize]).total_len = total_len2;
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let sz10: u32 =
                if
                total_len10.wrapping_rem(crate::hash_sha3::block_len(i) as u64) == 0u64
                &&
                total_len10 > 0u64
                { crate::hash_sha3::block_len(i) }
                else
                { total_len10.wrapping_rem(crate::hash_sha3::block_len(i) as u64) as u32 };
            if sz10 != 0u32
            {
                let a1: crate::streaming_types::hash_alg = block_state.fst;
                let s1: &mut [u64] = &mut block_state.snd;
                crate::hash_sha3::update_multi_sha3(
                    a1,
                    s1,
                    buf0,
                    (crate::hash_sha3::block_len(i)).wrapping_div(crate::hash_sha3::block_len(a1))
                )
            };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(
                    crate::hash_sha3::block_len(i) as u64
                )
                ==
                0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                { crate::hash_sha3::block_len(i) }
                else
                {
                    (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(
                        crate::hash_sha3::block_len(i) as u64
                    )
                    as
                    u32
                };
            let n_blocks: u32 =
                chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(
                    crate::hash_sha3::block_len(i)
                );
            let data1_len: u32 = n_blocks.wrapping_mul(crate::hash_sha3::block_len(i));
            let data2_len: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk2.1.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            let a1: crate::streaming_types::hash_alg = block_state.fst;
            let s1: &mut [u64] = &mut block_state.snd;
            crate::hash_sha3::update_multi_sha3(
                a1,
                s1,
                data2.0,
                data1_len.wrapping_div(crate::hash_sha3::block_len(a1))
            );
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::streaming_types::error_code::Success
    }
}

fn digest_(
    a: crate::streaming_types::hash_alg,
    state: &mut [crate::hash_sha3::state_t],
    output: &mut [u8],
    l: u32
)
{
    let mut block_state: &mut crate::hash_sha3::hash_buf = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(crate::hash_sha3::block_len(a) as u64) == 0u64 && total_len > 0u64
        { crate::hash_sha3::block_len(a) }
        else
        { total_len.wrapping_rem(crate::hash_sha3::block_len(a) as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut buf: [u64; 25] = [0u64; 25usize];
    let mut tmp_block_state: crate::hash_sha3::hash_buf =
        crate::hash_sha3::hash_buf { fst: a, snd: Box::new(buf) };
    let s_src: &mut [u64] = &mut block_state.snd;
    let s_dst: &mut [u64] = &mut tmp_block_state.snd;
    (s_dst[0usize..25usize]).copy_from_slice(&s_src[0usize..25usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(crate::hash_sha3::block_len(a)) == 0u32 && r > 0u32
        { crate::hash_sha3::block_len(a) }
        else
        { r.wrapping_rem(crate::hash_sha3::block_len(a)) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    let a1: crate::streaming_types::hash_alg = tmp_block_state.fst;
    let s: &mut [u64] = &mut tmp_block_state.snd;
    crate::hash_sha3::update_multi_sha3(
        a1,
        s,
        buf_last.0,
        0u32.wrapping_div(crate::hash_sha3::block_len(a1))
    );
    let a10: crate::streaming_types::hash_alg = tmp_block_state.fst;
    let s0: &mut [u64] = &mut tmp_block_state.snd;
    crate::hash_sha3::update_last_sha3(a10, s0, buf_last.1, r);
    let a11: crate::streaming_types::hash_alg = tmp_block_state.fst;
    let s1: &mut [u64] = &mut tmp_block_state.snd;
    if
    a11 == crate::streaming_types::hash_alg::Shake128
    ||
    a11 == crate::streaming_types::hash_alg::Shake256
    {
        for i in 0u32..l.wrapping_div(crate::hash_sha3::block_len(a11))
        {
            let mut hbuf: [u8; 256] = [0u8; 256usize];
            let mut ws: [u64; 32] = [0u64; 32usize];
            ((&mut ws)[0usize..25usize]).copy_from_slice(&s1[0usize..25usize]);
            krml::unroll_for!(
                32,
                "i0",
                0u32,
                1u32,
                lowstar::endianness::store64_le(
                    &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                    (&mut ws)[i0 as usize]
                )
            );
            let b0: &mut [u8] = output;
            let uu____0: (&mut [u8], &mut [u8]) = hbuf.split_at_mut(0usize);
            (b0[i.wrapping_mul(crate::hash_sha3::block_len(a11)) as usize..i.wrapping_mul(
                crate::hash_sha3::block_len(a11)
            )
            as
            usize
            +
            crate::hash_sha3::block_len(a11) as usize]).copy_from_slice(
                &uu____0.1[0usize..crate::hash_sha3::block_len(a11) as usize]
            );
            krml::unroll_for!(
                24,
                "i0",
                0u32,
                1u32,
                {
                    let mut _C: [u64; 5] = [0u64; 5usize];
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        (&mut _C)[i1 as usize] =
                            s1[i1.wrapping_add(0u32) as usize]
                            ^
                            (s1[i1.wrapping_add(5u32) as usize]
                            ^
                            (s1[i1.wrapping_add(10u32) as usize]
                            ^
                            (s1[i1.wrapping_add(15u32) as usize]
                            ^
                            s1[i1.wrapping_add(20u32) as usize])))
                    );
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        {
                            let uu____1: u64 =
                                (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                            let _D: u64 =
                                (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                                ^
                                (uu____1.wrapping_shl(1u32) | uu____1.wrapping_shr(63u32));
                            krml::unroll_for!(
                                5,
                                "i2",
                                0u32,
                                1u32,
                                s1[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                            )
                        }
                    );
                    let x: u64 = s1[1usize];
                    let mut current: [u64; 1] = [x; 1usize];
                    krml::unroll_for!(
                        24,
                        "i1",
                        0u32,
                        1u32,
                        {
                            let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                            let r1: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                            let temp: u64 = s1[_Y as usize];
                            let uu____2: u64 = (&mut current)[0usize];
                            s1[_Y as usize] =
                                uu____2.wrapping_shl(r1)
                                |
                                uu____2.wrapping_shr(64u32.wrapping_sub(r1));
                            (&mut current)[0usize] = temp
                        }
                    );
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        {
                            let v0: u64 =
                                s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v1: u64 =
                                s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v2: u64 =
                                s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v3: u64 =
                                s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v4: u64 =
                                s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                            s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                            s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                            s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                            s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                        }
                    );
                    let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                    s1[0usize] ^= c
                }
            )
        };
        let remOut: u32 = l.wrapping_rem(crate::hash_sha3::block_len(a11));
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws: [u64; 32] = [0u64; 32usize];
        ((&mut ws)[0usize..25usize]).copy_from_slice(&s1[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
                (&mut ws)[i as usize]
            )
        );
        (output[l.wrapping_sub(remOut) as usize..l.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
        )
    }
    else
    {
        for
        i
        in
        0u32..(crate::hash_sha3::hash_len(a11)).wrapping_div(crate::hash_sha3::block_len(a11))
        {
            let mut hbuf: [u8; 256] = [0u8; 256usize];
            let mut ws: [u64; 32] = [0u64; 32usize];
            ((&mut ws)[0usize..25usize]).copy_from_slice(&s1[0usize..25usize]);
            krml::unroll_for!(
                32,
                "i0",
                0u32,
                1u32,
                lowstar::endianness::store64_le(
                    &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                    (&mut ws)[i0 as usize]
                )
            );
            let b0: &mut [u8] = output;
            let uu____3: (&mut [u8], &mut [u8]) = hbuf.split_at_mut(0usize);
            (b0[i.wrapping_mul(crate::hash_sha3::block_len(a11)) as usize..i.wrapping_mul(
                crate::hash_sha3::block_len(a11)
            )
            as
            usize
            +
            crate::hash_sha3::block_len(a11) as usize]).copy_from_slice(
                &uu____3.1[0usize..crate::hash_sha3::block_len(a11) as usize]
            );
            krml::unroll_for!(
                24,
                "i0",
                0u32,
                1u32,
                {
                    let mut _C: [u64; 5] = [0u64; 5usize];
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        (&mut _C)[i1 as usize] =
                            s1[i1.wrapping_add(0u32) as usize]
                            ^
                            (s1[i1.wrapping_add(5u32) as usize]
                            ^
                            (s1[i1.wrapping_add(10u32) as usize]
                            ^
                            (s1[i1.wrapping_add(15u32) as usize]
                            ^
                            s1[i1.wrapping_add(20u32) as usize])))
                    );
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        {
                            let uu____4: u64 =
                                (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                            let _D: u64 =
                                (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                                ^
                                (uu____4.wrapping_shl(1u32) | uu____4.wrapping_shr(63u32));
                            krml::unroll_for!(
                                5,
                                "i2",
                                0u32,
                                1u32,
                                s1[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                            )
                        }
                    );
                    let x: u64 = s1[1usize];
                    let mut current: [u64; 1] = [x; 1usize];
                    krml::unroll_for!(
                        24,
                        "i1",
                        0u32,
                        1u32,
                        {
                            let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                            let r1: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                            let temp: u64 = s1[_Y as usize];
                            let uu____5: u64 = (&mut current)[0usize];
                            s1[_Y as usize] =
                                uu____5.wrapping_shl(r1)
                                |
                                uu____5.wrapping_shr(64u32.wrapping_sub(r1));
                            (&mut current)[0usize] = temp
                        }
                    );
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        {
                            let v0: u64 =
                                s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v1: u64 =
                                s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v2: u64 =
                                s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v3: u64 =
                                s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            let v4: u64 =
                                s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                ^
                                ! s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                &
                                s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                            s1[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                            s1[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                            s1[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                            s1[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                            s1[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                        }
                    );
                    let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                    s1[0usize] ^= c
                }
            )
        };
        let remOut: u32 =
            (crate::hash_sha3::hash_len(a11)).wrapping_rem(crate::hash_sha3::block_len(a11));
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws: [u64; 32] = [0u64; 32usize];
        ((&mut ws)[0usize..25usize]).copy_from_slice(&s1[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
                (&mut ws)[i as usize]
            )
        );
        let uu____6: (&mut [u8], &mut [u8]) = hbuf.split_at_mut(0usize);
        (output[(crate::hash_sha3::hash_len(a11)).wrapping_sub(remOut) as usize..(crate::hash_sha3::hash_len(
            a11
        )).wrapping_sub(remOut)
        as
        usize
        +
        remOut as usize]).copy_from_slice(&uu____6.1[0usize..remOut as usize])
    }
}

pub fn digest(state: &mut [crate::hash_sha3::state_t], output: &mut [u8]) ->
    crate::streaming_types::error_code
{
    let a1: crate::streaming_types::hash_alg = crate::hash_sha3::get_alg(state);
    if
    a1 == crate::streaming_types::hash_alg::Shake128
    ||
    a1 == crate::streaming_types::hash_alg::Shake256
    { crate::streaming_types::error_code::InvalidAlgorithm }
    else
    {
        crate::hash_sha3::digest_(a1, state, output, crate::hash_sha3::hash_len(a1));
        crate::streaming_types::error_code::Success
    }
}

pub fn squeeze(s: &mut [crate::hash_sha3::state_t], dst: &mut [u8], l: u32) ->
    crate::streaming_types::error_code
{
    let a1: crate::streaming_types::hash_alg = crate::hash_sha3::get_alg(s);
    if
    !
    (a1 == crate::streaming_types::hash_alg::Shake128
    ||
    a1 == crate::streaming_types::hash_alg::Shake256)
    { crate::streaming_types::error_code::InvalidAlgorithm }
    else if l == 0u32
    { crate::streaming_types::error_code::InvalidLength }
    else
    {
        crate::hash_sha3::digest_(a1, s, dst, l);
        crate::streaming_types::error_code::Success
    }
}

pub fn block_len0(s: &mut [crate::hash_sha3::state_t]) -> u32
{
    let a1: crate::streaming_types::hash_alg = crate::hash_sha3::get_alg(s);
    crate::hash_sha3::block_len(a1)
}

pub fn hash_len0(s: &mut [crate::hash_sha3::state_t]) -> u32
{
    let a1: crate::streaming_types::hash_alg = crate::hash_sha3::get_alg(s);
    crate::hash_sha3::hash_len(a1)
}

pub fn is_shake(s: &mut [crate::hash_sha3::state_t]) -> bool
{
    let uu____0: crate::streaming_types::hash_alg = crate::hash_sha3::get_alg(s);
    uu____0 == crate::streaming_types::hash_alg::Shake128
    ||
    uu____0 == crate::streaming_types::hash_alg::Shake256
}

pub fn absorb_inner_320(rateInBytes: u32, b: &mut [u8], s: &mut [u64])
{
    lowstar::ignore::ignore::<u32>(rateInBytes);
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, s[i as usize] ^= (&mut ws)[i as usize]);
    krml::unroll_for!(
        24,
        "i",
        0u32,
        1u32,
        {
            let mut _C: [u64; 5] = [0u64; 5usize];
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                (&mut _C)[i0 as usize] =
                    s[i0.wrapping_add(0u32) as usize]
                    ^
                    (s[i0.wrapping_add(5u32) as usize]
                    ^
                    (s[i0.wrapping_add(10u32) as usize]
                    ^
                    (s[i0.wrapping_add(15u32) as usize] ^ s[i0.wrapping_add(20u32) as usize])))
            );
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let uu____0: u64 = (&mut _C)[i0.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                    let _D: u64 =
                        (&mut _C)[i0.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                        ^
                        (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize] ^= _D
                    )
                }
            );
            let x: u64 = s[1usize];
            let mut current: [u64; 1] = [x; 1usize];
            krml::unroll_for!(
                24,
                "i0",
                0u32,
                1u32,
                {
                    let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i0 as usize];
                    let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i0 as usize];
                    let temp: u64 = s[_Y as usize];
                    let uu____1: u64 = (&mut current)[0usize];
                    s[_Y as usize] =
                        uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                    (&mut current)[0usize] = temp
                }
            );
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let v0: u64 =
                        s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v1: u64 =
                        s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v2: u64 =
                        s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v3: u64 =
                        s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let v4: u64 =
                        s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        ^
                        ! s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        &
                        s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v0;
                    s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v1;
                    s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v2;
                    s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v3;
                    s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v4
                }
            );
            let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i as usize];
            s[0usize] ^= c
        }
    )
}

pub fn shake128(output: &mut [u8], outputByteLen: u32, input: &mut [u8], inputByteLen: u32)
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut s: [u64; 25] = [0u64; 25usize];
    let rateInBytes1: u32 = 168u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = ib;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        crate::hash_sha3::absorb_inner_320(rateInBytes1, b·, &mut s)
    };
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b0: &mut [u8] = ib;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, (&mut s)[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(rateInBytes1, b3, &mut s);
    for i in 0u32..outputByteLen.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws0: [u64; 32] = [0u64; 32usize];
        ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws0)[i0 as usize]
            )
        );
        let b02: &mut [u8] = rb;
        (b02[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        (&mut s)[i1.wrapping_add(0u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(5u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(10u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(15u32) as usize]
                        ^
                        (&mut s)[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = (&mut s)[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = (&mut s)[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                (&mut s)[0usize] ^= c
            }
        )
    };
    let remOut: u32 = outputByteLen.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&mut ws0)[i as usize]
        )
    );
    (rb[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize])
}

pub fn shake256(output: &mut [u8], outputByteLen: u32, input: &mut [u8], inputByteLen: u32)
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut s: [u64; 25] = [0u64; 25usize];
    let rateInBytes1: u32 = 136u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = ib;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        crate::hash_sha3::absorb_inner_320(rateInBytes1, b·, &mut s)
    };
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b0: &mut [u8] = ib;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, (&mut s)[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(rateInBytes1, b3, &mut s);
    for i in 0u32..outputByteLen.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws0: [u64; 32] = [0u64; 32usize];
        ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws0)[i0 as usize]
            )
        );
        let b02: &mut [u8] = rb;
        (b02[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        (&mut s)[i1.wrapping_add(0u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(5u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(10u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(15u32) as usize]
                        ^
                        (&mut s)[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = (&mut s)[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = (&mut s)[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                (&mut s)[0usize] ^= c
            }
        )
    };
    let remOut: u32 = outputByteLen.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&mut ws0)[i as usize]
        )
    );
    (rb[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize])
}

pub fn sha3_224(output: &mut [u8], input: &mut [u8], inputByteLen: u32)
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut s: [u64; 25] = [0u64; 25usize];
    let rateInBytes1: u32 = 144u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = ib;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        crate::hash_sha3::absorb_inner_320(rateInBytes1, b·, &mut s)
    };
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b0: &mut [u8] = ib;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, (&mut s)[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(rateInBytes1, b3, &mut s);
    for i in 0u32..28u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws0: [u64; 32] = [0u64; 32usize];
        ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws0)[i0 as usize]
            )
        );
        let b02: &mut [u8] = rb;
        (b02[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        (&mut s)[i1.wrapping_add(0u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(5u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(10u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(15u32) as usize]
                        ^
                        (&mut s)[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = (&mut s)[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = (&mut s)[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                (&mut s)[0usize] ^= c
            }
        )
    };
    let remOut: u32 = 28u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&mut ws0)[i as usize]
        )
    );
    (rb[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    )
}

pub fn sha3_256(output: &mut [u8], input: &mut [u8], inputByteLen: u32)
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut s: [u64; 25] = [0u64; 25usize];
    let rateInBytes1: u32 = 136u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = ib;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        crate::hash_sha3::absorb_inner_320(rateInBytes1, b·, &mut s)
    };
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b0: &mut [u8] = ib;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, (&mut s)[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(rateInBytes1, b3, &mut s);
    for i in 0u32..32u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws0: [u64; 32] = [0u64; 32usize];
        ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws0)[i0 as usize]
            )
        );
        let b02: &mut [u8] = rb;
        (b02[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        (&mut s)[i1.wrapping_add(0u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(5u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(10u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(15u32) as usize]
                        ^
                        (&mut s)[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = (&mut s)[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = (&mut s)[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                (&mut s)[0usize] ^= c
            }
        )
    };
    let remOut: u32 = 32u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&mut ws0)[i as usize]
        )
    );
    (rb[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    )
}

pub fn sha3_384(output: &mut [u8], input: &mut [u8], inputByteLen: u32)
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut s: [u64; 25] = [0u64; 25usize];
    let rateInBytes1: u32 = 104u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = ib;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        crate::hash_sha3::absorb_inner_320(rateInBytes1, b·, &mut s)
    };
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b0: &mut [u8] = ib;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, (&mut s)[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(rateInBytes1, b3, &mut s);
    for i in 0u32..48u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws0: [u64; 32] = [0u64; 32usize];
        ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws0)[i0 as usize]
            )
        );
        let b02: &mut [u8] = rb;
        (b02[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        (&mut s)[i1.wrapping_add(0u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(5u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(10u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(15u32) as usize]
                        ^
                        (&mut s)[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = (&mut s)[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = (&mut s)[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                (&mut s)[0usize] ^= c
            }
        )
    };
    let remOut: u32 = 48u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&mut ws0)[i as usize]
        )
    );
    (rb[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    )
}

pub fn sha3_512(output: &mut [u8], input: &mut [u8], inputByteLen: u32)
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut s: [u64; 25] = [0u64; 25usize];
    let rateInBytes1: u32 = 72u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = ib;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        crate::hash_sha3::absorb_inner_320(rateInBytes1, b·, &mut s)
    };
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b0: &mut [u8] = ib;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, (&mut s)[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(rateInBytes1, b3, &mut s);
    for i in 0u32..64u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws0: [u64; 32] = [0u64; 32usize];
        ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws0)[i0 as usize]
            )
        );
        let b02: &mut [u8] = rb;
        (b02[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        (&mut s)[i1.wrapping_add(0u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(5u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(10u32) as usize]
                        ^
                        ((&mut s)[i1.wrapping_add(15u32) as usize]
                        ^
                        (&mut s)[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = (&mut s)[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = (&mut s)[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                (&mut s)[0usize] ^= c
            }
        )
    };
    let remOut: u32 = 64u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&mut ws0)[i as usize]
        )
    );
    (rb[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    )
}

/**
Allocate state buffer of 200-bytes
*/
pub fn
state_malloc() ->
    Box<[u64]>
{
    let mut buf: Box<[u64]> = vec![0u64; 25usize].into_boxed_slice();
    buf
}

/**
Free state buffer
*/
pub fn
state_free(s: &mut [u64])
{ () }

/**
Absorb number of input blocks and write the output state

  This function is intended to receive a hash state and input buffer.
  It processes an input of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block are ignored.

  The argument `state` (IN/OUT) points to hash state, i.e., uint64_t[25]
  The argument `input` (IN) points to `inputByteLen` bytes of valid memory,
  i.e., uint8_t[inputByteLen]
*/
pub fn
shake128_absorb_nblocks(state: &mut [u64], input: &mut [u8], inputByteLen: u32)
{
    for i in 0u32..inputByteLen.wrapping_div(168u32)
    {
        let mut b: [u8; 256] = [0u8; 256usize];
        let b·: &mut [u8] = &mut b;
        let b0: &mut [u8] = input;
        let bl0: &mut [u8] = b·;
        (bl0[0usize..168usize]).copy_from_slice(
            &(&mut b0[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
        );
        crate::hash_sha3::absorb_inner_320(168u32, b·, state)
    }
}

/**
Absorb a final partial block of input and write the output state

  This function is intended to receive a hash state and input buffer.
  It processes a sequence of bytes at end of input buffer that is less
  than 168-bytes (SHAKE128 block size),
  any bytes of full blocks at start of input buffer are ignored.

  The argument `state` (IN/OUT) points to hash state, i.e., uint64_t[25]
  The argument `input` (IN) points to `inputByteLen` bytes of valid memory,
  i.e., uint8_t[inputByteLen]

  Note: Full size of input buffer must be passed to `inputByteLen` including
  the number of full-block bytes at start of input buffer that are ignored
*/
pub fn
shake128_absorb_final(state: &mut [u64], input: &mut [u8], inputByteLen: u32)
{
    let mut b: [u8; 256] = [0u8; 256usize];
    let b·: &mut [u8] = &mut b;
    let rem: u32 = inputByteLen.wrapping_rem(168u32);
    let b0: &mut [u8] = input;
    let bl0: &mut [u8] = b·;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b0[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b00: &mut [u8] = b·;
    b00[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
    let mut ws: [u64; 32] = [0u64; 32usize];
    let b1: &mut [u8] = b·;
    let u: u64 = lowstar::endianness::load64_le(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = lowstar::endianness::load64_le(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = lowstar::endianness::load64_le(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = lowstar::endianness::load64_le(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = lowstar::endianness::load64_le(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = lowstar::endianness::load64_le(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = lowstar::endianness::load64_le(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = lowstar::endianness::load64_le(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = lowstar::endianness::load64_le(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = lowstar::endianness::load64_le(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = lowstar::endianness::load64_le(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = lowstar::endianness::load64_le(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = lowstar::endianness::load64_le(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = lowstar::endianness::load64_le(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = lowstar::endianness::load64_le(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = lowstar::endianness::load64_le(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    let u15: u64 = lowstar::endianness::load64_le(&mut b1[128usize..]);
    (&mut ws)[16usize] = u15;
    let u16: u64 = lowstar::endianness::load64_le(&mut b1[136usize..]);
    (&mut ws)[17usize] = u16;
    let u17: u64 = lowstar::endianness::load64_le(&mut b1[144usize..]);
    (&mut ws)[18usize] = u17;
    let u18: u64 = lowstar::endianness::load64_le(&mut b1[152usize..]);
    (&mut ws)[19usize] = u18;
    let u19: u64 = lowstar::endianness::load64_le(&mut b1[160usize..]);
    (&mut ws)[20usize] = u19;
    let u20: u64 = lowstar::endianness::load64_le(&mut b1[168usize..]);
    (&mut ws)[21usize] = u20;
    let u21: u64 = lowstar::endianness::load64_le(&mut b1[176usize..]);
    (&mut ws)[22usize] = u21;
    let u22: u64 = lowstar::endianness::load64_le(&mut b1[184usize..]);
    (&mut ws)[23usize] = u22;
    let u23: u64 = lowstar::endianness::load64_le(&mut b1[192usize..]);
    (&mut ws)[24usize] = u23;
    let u24: u64 = lowstar::endianness::load64_le(&mut b1[200usize..]);
    (&mut ws)[25usize] = u24;
    let u25: u64 = lowstar::endianness::load64_le(&mut b1[208usize..]);
    (&mut ws)[26usize] = u25;
    let u26: u64 = lowstar::endianness::load64_le(&mut b1[216usize..]);
    (&mut ws)[27usize] = u26;
    let u27: u64 = lowstar::endianness::load64_le(&mut b1[224usize..]);
    (&mut ws)[28usize] = u27;
    let u28: u64 = lowstar::endianness::load64_le(&mut b1[232usize..]);
    (&mut ws)[29usize] = u28;
    let u29: u64 = lowstar::endianness::load64_le(&mut b1[240usize..]);
    (&mut ws)[30usize] = u29;
    let u30: u64 = lowstar::endianness::load64_le(&mut b1[248usize..]);
    (&mut ws)[31usize] = u30;
    krml::unroll_for!(25, "i", 0u32, 1u32, state[i as usize] ^= (&mut ws)[i as usize]);
    let mut b2: [u8; 256] = [0u8; 256usize];
    let b3: &mut [u8] = &mut b2;
    let b01: &mut [u8] = b3;
    b01[167usize] = 0x80u8;
    crate::hash_sha3::absorb_inner_320(168u32, b3, state)
}

/**
Squeeze a hash state to output buffer

  This function is intended to receive a hash state and output buffer.
  It produces an output of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block are ignored.

  The argument `state` (IN) points to hash state, i.e., uint64_t[25]
  The argument `output` (OUT) points to `outputByteLen` bytes of valid memory,
  i.e., uint8_t[outputByteLen]
*/
pub fn
shake128_squeeze_nblocks(state: &mut [u64], output: &mut [u8], outputByteLen: u32)
{
    for i in 0u32..outputByteLen.wrapping_div(168u32)
    {
        let mut hbuf: [u8; 256] = [0u8; 256usize];
        let mut ws: [u64; 32] = [0u64; 32usize];
        ((&mut ws)[0usize..25usize]).copy_from_slice(&state[0usize..25usize]);
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lowstar::endianness::store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(8u32) as usize..],
                (&mut ws)[i0 as usize]
            )
        );
        let b0: &mut [u8] = output;
        (b0[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..168usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [u64; 5] = [0u64; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    (&mut _C)[i1 as usize] =
                        state[i1.wrapping_add(0u32) as usize]
                        ^
                        (state[i1.wrapping_add(5u32) as usize]
                        ^
                        (state[i1.wrapping_add(10u32) as usize]
                        ^
                        (state[i1.wrapping_add(15u32) as usize]
                        ^
                        state[i1.wrapping_add(20u32) as usize])))
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: u64 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: u64 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize]
                            ^
                            (uu____0.wrapping_shl(1u32) | uu____0.wrapping_shr(63u32));
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            state[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] ^= _D
                        )
                    }
                );
                let x: u64 = state[1usize];
                let mut current: [u64; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&mut crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&mut crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: u64 = state[_Y as usize];
                        let uu____1: u64 = (&mut current)[0usize];
                        state[_Y as usize] =
                            uu____1.wrapping_shl(r) | uu____1.wrapping_shr(64u32.wrapping_sub(r));
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let v0: u64 =
                            state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v1: u64 =
                            state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v2: u64 =
                            state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v3: u64 =
                            state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let v4: u64 =
                            state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            ^
                            ! state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            &
                            state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v0;
                        state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v1;
                        state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v2;
                        state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v3;
                        state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&mut crate::hash_sha3::keccak_rndc)[i0 as usize];
                state[0usize] ^= c
            }
        )
    }
}
