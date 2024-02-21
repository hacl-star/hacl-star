#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub const h224: [u32; 8] =
    [0xc1059ed8u32, 0x367cd507u32, 0x3070dd17u32, 0xf70e5939u32, 0xffc00b31u32, 0x68581511u32,
        0x64f98fa7u32, 0xbefa4fa4u32];

pub const h256: [u32; 8] =
    [0x6a09e667u32, 0xbb67ae85u32, 0x3c6ef372u32, 0xa54ff53au32, 0x510e527fu32, 0x9b05688cu32,
        0x1f83d9abu32, 0x5be0cd19u32];

pub const h384: [u64; 8] =
    [0xcbbb9d5dc1059ed8u64, 0x629a292a367cd507u64, 0x9159015a3070dd17u64, 0x152fecd8f70e5939u64,
        0x67332667ffc00b31u64, 0x8eb44a8768581511u64, 0xdb0c2e0d64f98fa7u64, 0x47b5481dbefa4fa4u64];

pub const h512: [u64; 8] =
    [0x6a09e667f3bcc908u64, 0xbb67ae8584caa73bu64, 0x3c6ef372fe94f82bu64, 0xa54ff53a5f1d36f1u64,
        0x510e527fade682d1u64, 0x9b05688c2b3e6c1fu64, 0x1f83d9abfb41bd6bu64, 0x5be0cd19137e2179u64];

pub const k224_256: [u32; 64] =
    [0x428a2f98u32, 0x71374491u32, 0xb5c0fbcfu32, 0xe9b5dba5u32, 0x3956c25bu32, 0x59f111f1u32,
        0x923f82a4u32, 0xab1c5ed5u32, 0xd807aa98u32, 0x12835b01u32, 0x243185beu32, 0x550c7dc3u32,
        0x72be5d74u32, 0x80deb1feu32, 0x9bdc06a7u32, 0xc19bf174u32, 0xe49b69c1u32, 0xefbe4786u32,
        0x0fc19dc6u32, 0x240ca1ccu32, 0x2de92c6fu32, 0x4a7484aau32, 0x5cb0a9dcu32, 0x76f988dau32,
        0x983e5152u32, 0xa831c66du32, 0xb00327c8u32, 0xbf597fc7u32, 0xc6e00bf3u32, 0xd5a79147u32,
        0x06ca6351u32, 0x14292967u32, 0x27b70a85u32, 0x2e1b2138u32, 0x4d2c6dfcu32, 0x53380d13u32,
        0x650a7354u32, 0x766a0abbu32, 0x81c2c92eu32, 0x92722c85u32, 0xa2bfe8a1u32, 0xa81a664bu32,
        0xc24b8b70u32, 0xc76c51a3u32, 0xd192e819u32, 0xd6990624u32, 0xf40e3585u32, 0x106aa070u32,
        0x19a4c116u32, 0x1e376c08u32, 0x2748774cu32, 0x34b0bcb5u32, 0x391c0cb3u32, 0x4ed8aa4au32,
        0x5b9cca4fu32, 0x682e6ff3u32, 0x748f82eeu32, 0x78a5636fu32, 0x84c87814u32, 0x8cc70208u32,
        0x90befffau32, 0xa4506cebu32, 0xbef9a3f7u32, 0xc67178f2u32];

pub const k384_512: [u64; 80] =
    [0x428a2f98d728ae22u64, 0x7137449123ef65cdu64, 0xb5c0fbcfec4d3b2fu64, 0xe9b5dba58189dbbcu64,
        0x3956c25bf348b538u64, 0x59f111f1b605d019u64, 0x923f82a4af194f9bu64, 0xab1c5ed5da6d8118u64,
        0xd807aa98a3030242u64, 0x12835b0145706fbeu64, 0x243185be4ee4b28cu64, 0x550c7dc3d5ffb4e2u64,
        0x72be5d74f27b896fu64, 0x80deb1fe3b1696b1u64, 0x9bdc06a725c71235u64, 0xc19bf174cf692694u64,
        0xe49b69c19ef14ad2u64, 0xefbe4786384f25e3u64, 0x0fc19dc68b8cd5b5u64, 0x240ca1cc77ac9c65u64,
        0x2de92c6f592b0275u64, 0x4a7484aa6ea6e483u64, 0x5cb0a9dcbd41fbd4u64, 0x76f988da831153b5u64,
        0x983e5152ee66dfabu64, 0xa831c66d2db43210u64, 0xb00327c898fb213fu64, 0xbf597fc7beef0ee4u64,
        0xc6e00bf33da88fc2u64, 0xd5a79147930aa725u64, 0x06ca6351e003826fu64, 0x142929670a0e6e70u64,
        0x27b70a8546d22ffcu64, 0x2e1b21385c26c926u64, 0x4d2c6dfc5ac42aedu64, 0x53380d139d95b3dfu64,
        0x650a73548baf63deu64, 0x766a0abb3c77b2a8u64, 0x81c2c92e47edaee6u64, 0x92722c851482353bu64,
        0xa2bfe8a14cf10364u64, 0xa81a664bbc423001u64, 0xc24b8b70d0f89791u64, 0xc76c51a30654be30u64,
        0xd192e819d6ef5218u64, 0xd69906245565a910u64, 0xf40e35855771202au64, 0x106aa07032bbd1b8u64,
        0x19a4c116b8d2d0c8u64, 0x1e376c085141ab53u64, 0x2748774cdf8eeb99u64, 0x34b0bcb5e19b48a8u64,
        0x391c0cb3c5c95a63u64, 0x4ed8aa4ae3418acbu64, 0x5b9cca4f7763e373u64, 0x682e6ff3d6b2b8a3u64,
        0x748f82ee5defb2fcu64, 0x78a5636f43172f60u64, 0x84c87814a1f0ab72u64, 0x8cc702081a6439ecu64,
        0x90befffa23631e28u64, 0xa4506cebde82bde9u64, 0xbef9a3f7b2c67915u64, 0xc67178f2e372532bu64,
        0xca273eceea26619cu64, 0xd186b8c721c0c207u64, 0xeada7dd6cde0eb1eu64, 0xf57d4f7fee6ed178u64,
        0x06f067aa72176fbau64, 0x0a637dc5a2c898a6u64, 0x113f9804bef90daeu64, 0x1b710b35131c471bu64,
        0x28db77f523047d84u64, 0x32caab7b40c72493u64, 0x3c9ebe0a15c9bebcu64, 0x431d67c49c100d4cu64,
        0x4cc5d4becb3e42b6u64, 0x597f299cfc657e2au64, 0x5fcb6fab3ad6faecu64, 0x6c44198c4a475817u64];

pub fn sha256_init(hash: &mut [u32]) -> ()
{
    for i in 0u32..8u32
    {
        let x: u32 = (&h256)[i as usize];
        let os: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha256_update(b: &mut [u8], hash: &mut [u32]) -> ()
{
    let mut hash_old: [u32; 8] = [0u32; 8usize];
    let mut ws: [u32; 16] = [0u32; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    let b1: &mut [u8] = b;
    let u: u32 = crate::lowstar::endianness::load32_be(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u32 = crate::lowstar::endianness::load32_be(&mut b1[4usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u32 = crate::lowstar::endianness::load32_be(&mut b1[8usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u32 = crate::lowstar::endianness::load32_be(&mut b1[12usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u32 = crate::lowstar::endianness::load32_be(&mut b1[16usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u32 = crate::lowstar::endianness::load32_be(&mut b1[20usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u32 = crate::lowstar::endianness::load32_be(&mut b1[24usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u32 = crate::lowstar::endianness::load32_be(&mut b1[28usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u32 = crate::lowstar::endianness::load32_be(&mut b1[32usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u32 = crate::lowstar::endianness::load32_be(&mut b1[36usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u32 = crate::lowstar::endianness::load32_be(&mut b1[40usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u32 = crate::lowstar::endianness::load32_be(&mut b1[44usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u32 = crate::lowstar::endianness::load32_be(&mut b1[48usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u32 = crate::lowstar::endianness::load32_be(&mut b1[52usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u32 = crate::lowstar::endianness::load32_be(&mut b1[56usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u32 = crate::lowstar::endianness::load32_be(&mut b1[60usize..]);
    (&mut ws)[15usize] = u14;
    for i in 0u32..4u32
    {
        for i0 in 0u32..16u32
        {
            let k_t: u32 = (&k224_256)[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
            let ws_t: u32 = (&mut ws)[i0 as usize];
            let a0: u32 = hash[0usize];
            let b0: u32 = hash[1usize];
            let c0: u32 = hash[2usize];
            let d0: u32 = hash[3usize];
            let e0: u32 = hash[4usize];
            let f0: u32 = hash[5usize];
            let g0: u32 = hash[6usize];
            let h02: u32 = hash[7usize];
            let k_e_t: u32 = k_t;
            let t1: u32 =
                h02.wrapping_add(
                    (e0.wrapping_shl(26u32) | e0.wrapping_shr(6u32))
                    ^
                    ((e0.wrapping_shl(21u32) | e0.wrapping_shr(11u32))
                    ^
                    (e0.wrapping_shl(7u32) | e0.wrapping_shr(25u32)))
                ).wrapping_add(e0 & f0 ^ ! e0 & g0).wrapping_add(k_e_t).wrapping_add(ws_t);
            let t2: u32 =
                ((a0.wrapping_shl(30u32) | a0.wrapping_shr(2u32))
                ^
                ((a0.wrapping_shl(19u32) | a0.wrapping_shr(13u32))
                ^
                (a0.wrapping_shl(10u32) | a0.wrapping_shr(22u32)))).wrapping_add(
                    a0 & b0 ^ (a0 & c0 ^ b0 & c0)
                );
            let a1: u32 = t1.wrapping_add(t2);
            let b10: u32 = a0;
            let c1: u32 = b0;
            let d1: u32 = c0;
            let e1: u32 = d0.wrapping_add(t1);
            let f1: u32 = e0;
            let g1: u32 = f0;
            let h12: u32 = g0;
            hash[0usize] = a1;
            hash[1usize] = b10;
            hash[2usize] = c1;
            hash[3usize] = d1;
            hash[4usize] = e1;
            hash[5usize] = f1;
            hash[6usize] = g1;
            hash[7usize] = h12
        };
        if i < 3u32
        {
            for i0 in 0u32..16u32
            {
                let t16: u32 = (&mut ws)[i0 as usize];
                let t15: u32 = (&mut ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                let t7: u32 = (&mut ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                let t2: u32 = (&mut ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                let s1: u32 =
                    (t2.wrapping_shl(15u32) | t2.wrapping_shr(17u32))
                    ^
                    ((t2.wrapping_shl(13u32) | t2.wrapping_shr(19u32)) ^ t2.wrapping_shr(10u32));
                let s0: u32 =
                    (t15.wrapping_shl(25u32) | t15.wrapping_shr(7u32))
                    ^
                    ((t15.wrapping_shl(14u32) | t15.wrapping_shr(18u32)) ^ t15.wrapping_shr(3u32));
                (&mut ws)[i0 as usize] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16)
            }
        }
    };
    for i in 0u32..8u32
    {
        let x: u32 = (hash[i as usize]).wrapping_add((&mut hash_old)[i as usize]);
        let os: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn sha256_update_nblocks(len: u32, b: &mut [u8], st: &mut [u32]) -> ()
{
    let blocks: u32 = len.wrapping_div(64u32);
    for i in 0u32..blocks
    {
        let b0: &mut [u8] = b;
        let mb: (&mut [u8], &mut [u8]) = b0.split_at_mut(i.wrapping_mul(64u32) as usize);
        sha256_update(mb.1, st)
    }
}

pub fn sha256_update_last(totlen: u64, len: u32, b: &mut [u8], hash: &mut [u32]) -> ()
{
    let blocks: u32 = if len.wrapping_add(8u32).wrapping_add(1u32) <= 64u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(64u32);
    let mut last: [u8; 128] = [0u8; 128usize];
    let mut totlen_buf: [u8; 8] = [0u8; 8usize];
    let total_len_bits: u64 = totlen.wrapping_shl(3u32);
    crate::lowstar::endianness::store64_be(&mut totlen_buf, total_len_bits);
    let b0: &mut [u8] = b;
    ((&mut last)[0usize..len as usize]).copy_from_slice(&b0[0usize..len as usize]);
    (&mut last)[len as usize] = 0x80u8;
    ((&mut last)[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
        &(&mut totlen_buf)[0usize..8usize]
    );
    let last0: (&mut [u8], &mut [u8]) = (&mut last).split_at_mut(0usize);
    let last1: (&mut [u8], &mut [u8]) = last0.1.split_at_mut(64usize);
    let l0: &mut [u8] = last1.0;
    let l1: &mut [u8] = last1.1;
    let lb0: &mut [u8] = l0;
    let lb1: &mut [u8] = l1;
    let last00: &mut [u8] = lb0;
    let last10: &mut [u8] = lb1;
    sha256_update(last00, hash);
    if blocks > 1u32 { sha256_update(last10, hash) }
}

pub fn sha256_finish(st: &mut [u32], h: &mut [u8]) -> ()
{
    let mut hbuf: [u8; 32] = [0u8; 32usize];
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(4u32) as usize..],
            st[i as usize]
        )
    };
    (h[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..32usize])
}

pub fn sha224_init(hash: &mut [u32]) -> ()
{
    for i in 0u32..8u32
    {
        let x: u32 = (&h224)[i as usize];
        let os: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha224_update_nblocks(len: u32, b: &mut [u8], st: &mut [u32]) -> ()
{ sha256_update_nblocks(len, b, st) }

pub fn sha224_update_last(totlen: u64, len: u32, b: &mut [u8], st: &mut [u32]) -> ()
{ sha256_update_last(totlen, len, b, st) }

pub fn sha224_finish(st: &mut [u32], h: &mut [u8]) -> ()
{
    let mut hbuf: [u8; 32] = [0u8; 32usize];
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(4u32) as usize..],
            st[i as usize]
        )
    };
    (h[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..28usize])
}

pub fn sha512_init(hash: &mut [u64]) -> ()
{
    for i in 0u32..8u32
    {
        let x: u64 = (&h512)[i as usize];
        let os: (&mut [u64], &mut [u64]) = hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha512_update(b: &mut [u8], hash: &mut [u64]) -> ()
{
    let mut hash_old: [u64; 8] = [0u64; 8usize];
    let mut ws: [u64; 16] = [0u64; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    let b1: &mut [u8] = b;
    let u: u64 = crate::lowstar::endianness::load64_be(&mut b1[0usize..]);
    (&mut ws)[0usize] = u;
    let u0: u64 = crate::lowstar::endianness::load64_be(&mut b1[8usize..]);
    (&mut ws)[1usize] = u0;
    let u1: u64 = crate::lowstar::endianness::load64_be(&mut b1[16usize..]);
    (&mut ws)[2usize] = u1;
    let u2: u64 = crate::lowstar::endianness::load64_be(&mut b1[24usize..]);
    (&mut ws)[3usize] = u2;
    let u3: u64 = crate::lowstar::endianness::load64_be(&mut b1[32usize..]);
    (&mut ws)[4usize] = u3;
    let u4: u64 = crate::lowstar::endianness::load64_be(&mut b1[40usize..]);
    (&mut ws)[5usize] = u4;
    let u5: u64 = crate::lowstar::endianness::load64_be(&mut b1[48usize..]);
    (&mut ws)[6usize] = u5;
    let u6: u64 = crate::lowstar::endianness::load64_be(&mut b1[56usize..]);
    (&mut ws)[7usize] = u6;
    let u7: u64 = crate::lowstar::endianness::load64_be(&mut b1[64usize..]);
    (&mut ws)[8usize] = u7;
    let u8: u64 = crate::lowstar::endianness::load64_be(&mut b1[72usize..]);
    (&mut ws)[9usize] = u8;
    let u9: u64 = crate::lowstar::endianness::load64_be(&mut b1[80usize..]);
    (&mut ws)[10usize] = u9;
    let u10: u64 = crate::lowstar::endianness::load64_be(&mut b1[88usize..]);
    (&mut ws)[11usize] = u10;
    let u11: u64 = crate::lowstar::endianness::load64_be(&mut b1[96usize..]);
    (&mut ws)[12usize] = u11;
    let u12: u64 = crate::lowstar::endianness::load64_be(&mut b1[104usize..]);
    (&mut ws)[13usize] = u12;
    let u13: u64 = crate::lowstar::endianness::load64_be(&mut b1[112usize..]);
    (&mut ws)[14usize] = u13;
    let u14: u64 = crate::lowstar::endianness::load64_be(&mut b1[120usize..]);
    (&mut ws)[15usize] = u14;
    for i in 0u32..5u32
    {
        for i0 in 0u32..16u32
        {
            let k_t: u64 = (&k384_512)[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
            let ws_t: u64 = (&mut ws)[i0 as usize];
            let a0: u64 = hash[0usize];
            let b0: u64 = hash[1usize];
            let c0: u64 = hash[2usize];
            let d0: u64 = hash[3usize];
            let e0: u64 = hash[4usize];
            let f0: u64 = hash[5usize];
            let g0: u64 = hash[6usize];
            let h02: u64 = hash[7usize];
            let k_e_t: u64 = k_t;
            let t1: u64 =
                h02.wrapping_add(
                    (e0.wrapping_shl(50u32) | e0.wrapping_shr(14u32))
                    ^
                    ((e0.wrapping_shl(46u32) | e0.wrapping_shr(18u32))
                    ^
                    (e0.wrapping_shl(23u32) | e0.wrapping_shr(41u32)))
                ).wrapping_add(e0 & f0 ^ ! e0 & g0).wrapping_add(k_e_t).wrapping_add(ws_t);
            let t2: u64 =
                ((a0.wrapping_shl(36u32) | a0.wrapping_shr(28u32))
                ^
                ((a0.wrapping_shl(30u32) | a0.wrapping_shr(34u32))
                ^
                (a0.wrapping_shl(25u32) | a0.wrapping_shr(39u32)))).wrapping_add(
                    a0 & b0 ^ (a0 & c0 ^ b0 & c0)
                );
            let a1: u64 = t1.wrapping_add(t2);
            let b10: u64 = a0;
            let c1: u64 = b0;
            let d1: u64 = c0;
            let e1: u64 = d0.wrapping_add(t1);
            let f1: u64 = e0;
            let g1: u64 = f0;
            let h12: u64 = g0;
            hash[0usize] = a1;
            hash[1usize] = b10;
            hash[2usize] = c1;
            hash[3usize] = d1;
            hash[4usize] = e1;
            hash[5usize] = f1;
            hash[6usize] = g1;
            hash[7usize] = h12
        };
        if i < 4u32
        {
            for i0 in 0u32..16u32
            {
                let t16: u64 = (&mut ws)[i0 as usize];
                let t15: u64 = (&mut ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                let t7: u64 = (&mut ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                let t2: u64 = (&mut ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                let s1: u64 =
                    (t2.wrapping_shl(45u32) | t2.wrapping_shr(19u32))
                    ^
                    ((t2.wrapping_shl(3u32) | t2.wrapping_shr(61u32)) ^ t2.wrapping_shr(6u32));
                let s0: u64 =
                    (t15.wrapping_shl(63u32) | t15.wrapping_shr(1u32))
                    ^
                    ((t15.wrapping_shl(56u32) | t15.wrapping_shr(8u32)) ^ t15.wrapping_shr(7u32));
                (&mut ws)[i0 as usize] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16)
            }
        }
    };
    for i in 0u32..8u32
    {
        let x: u64 = (hash[i as usize]).wrapping_add((&mut hash_old)[i as usize]);
        let os: (&mut [u64], &mut [u64]) = hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn sha512_update_nblocks(len: u32, b: &mut [u8], st: &mut [u64]) -> ()
{
    let blocks: u32 = len.wrapping_div(128u32);
    for i in 0u32..blocks
    {
        let b0: &mut [u8] = b;
        let mb: (&mut [u8], &mut [u8]) = b0.split_at_mut(i.wrapping_mul(128u32) as usize);
        sha512_update(mb.1, st)
    }
}

pub fn sha512_update_last(
    totlen: crate::fstar::uint128::uint128,
    len: u32,
    b: &mut [u8],
    hash: &mut [u64]
) ->
    ()
{
    let blocks: u32 =
        if len.wrapping_add(16u32).wrapping_add(1u32) <= 128u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(128u32);
    let mut last: [u8; 256] = [0u8; 256usize];
    let mut totlen_buf: [u8; 16] = [0u8; 16usize];
    let total_len_bits: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::shift_left(totlen, 3u32);
    crate::lowstar::endianness::store128_be(&mut totlen_buf, total_len_bits);
    let b0: &mut [u8] = b;
    ((&mut last)[0usize..len as usize]).copy_from_slice(&b0[0usize..len as usize]);
    (&mut last)[len as usize] = 0x80u8;
    ((&mut last)[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize + 16usize]).copy_from_slice(
        &(&mut totlen_buf)[0usize..16usize]
    );
    let last0: (&mut [u8], &mut [u8]) = (&mut last).split_at_mut(0usize);
    let last1: (&mut [u8], &mut [u8]) = last0.1.split_at_mut(128usize);
    let l0: &mut [u8] = last1.0;
    let l1: &mut [u8] = last1.1;
    let lb0: &mut [u8] = l0;
    let lb1: &mut [u8] = l1;
    let last00: &mut [u8] = lb0;
    let last10: &mut [u8] = lb1;
    sha512_update(last00, hash);
    if blocks > 1u32 { sha512_update(last10, hash) }
}

pub fn sha512_finish(st: &mut [u64], h: &mut [u8]) -> ()
{
    let mut hbuf: [u8; 64] = [0u8; 64usize];
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store64_be(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            st[i as usize]
        )
    };
    (h[0usize..64usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..64usize])
}

pub fn sha384_init(hash: &mut [u64]) -> ()
{
    for i in 0u32..8u32
    {
        let x: u64 = (&h384)[i as usize];
        let os: (&mut [u64], &mut [u64]) = hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn sha384_update_nblocks(len: u32, b: &mut [u8], st: &mut [u64]) -> ()
{ sha512_update_nblocks(len, b, st) }

pub fn sha384_update_last(
    totlen: crate::fstar::uint128::uint128,
    len: u32,
    b: &mut [u8],
    st: &mut [u64]
) ->
    ()
{ sha512_update_last(totlen, len, b, st) }

pub fn sha384_finish(st: &mut [u64], h: &mut [u8]) -> ()
{
    let mut hbuf: [u8; 64] = [0u8; 64usize];
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store64_be(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            st[i as usize]
        )
    };
    (h[0usize..48usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..48usize])
}

pub type state_t_224 = crate::hacl::streaming_types::state_32;

pub type state_t_256 = crate::hacl::streaming_types::state_32;

pub type state_t_384 = crate::hacl::streaming_types::state_64;

pub type state_t_512 = crate::hacl::streaming_types::state_64;

pub fn malloc_256() -> Vec<crate::hacl::streaming_types::state_32>
{
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    let mut block_state: Vec<u32> = vec![0u32; 8usize];
    sha256_init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_32 =
        crate::hacl::streaming_types::state_32
        { block_state: block_state, buf: buf, total_len: 0u32 as u64 };
    let mut p: Vec<crate::hacl::streaming_types::state_32> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_32> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn copy_256(state: &mut [crate::hacl::streaming_types::state_32]) ->
    Vec<crate::hacl::streaming_types::state_32>
{
    let block_state0: &mut [u32] = &mut (state[0usize]).block_state;
    let buf0: &mut [u8] = &mut (state[0usize]).buf;
    let total_len0: u64 = (state[0usize]).total_len;
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    ((&mut buf)[0usize..64usize]).copy_from_slice(&buf0[0usize..64usize]);
    let mut block_state: Vec<u32> = vec![0u32; 8usize];
    ((&mut block_state)[0usize..8usize]).copy_from_slice(&block_state0[0usize..8usize]);
    let mut s: crate::hacl::streaming_types::state_32 =
        crate::hacl::streaming_types::state_32
        { block_state: block_state, buf: buf, total_len: total_len0 };
    let mut p: Vec<crate::hacl::streaming_types::state_32> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_32> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset_256(state: &mut [crate::hacl::streaming_types::state_32]) -> ()
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    sha256_init(block_state);
    (state[0usize]).total_len = 0u32 as u64
}

#[inline] fn update_224_256(
    state: &mut [crate::hacl::streaming_types::state_32],
    chunk: &mut [u8],
    chunk_len: u32
) ->
    crate::hacl::streaming_types::error_code
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 2305843009213693951u64.wrapping_sub(total_len)
    { crate::hacl::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
            { 64u32 }
            else
            { total_len.wrapping_rem(64u32 as u64) as u32 };
        if chunk_len <= 64u32.wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2
        }
        else
        if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz1 == 0u32) { sha256_update_nblocks(64u32, buf, block_state) };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(64u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            sha256_update_nblocks(
                data1_len.wrapping_div(64u32).wrapping_mul(64u32),
                data2.0,
                block_state
            );
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = 64u32.wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            (state[0usize]).total_len = total_len2;
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let sz10: u32 =
                if total_len10.wrapping_rem(64u32 as u64) == 0u64 && total_len10 > 0u64
                { 64u32 }
                else
                { total_len10.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz10 == 0u32) { sha256_update_nblocks(64u32, buf0, block_state) };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(64u32 as u64) == 0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk2.1.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            sha256_update_nblocks(
                data1_len.wrapping_div(64u32).wrapping_mul(64u32),
                data2.0,
                block_state
            );
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::hacl::streaming_types::error_code::Success
    }
}

pub fn update_256(
    state: &mut [crate::hacl::streaming_types::state_32],
    input: &mut [u8],
    input_len: u32
) ->
    crate::hacl::streaming_types::error_code
{ update_224_256(state, input, input_len) }

pub fn digest_256(state: &mut [crate::hacl::streaming_types::state_32], output: &mut [u8]) ->
    ()
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut tmp_block_state: [u32; 8] = [0u32; 8usize];
    ((&mut tmp_block_state)[0usize..8usize]).copy_from_slice(&block_state[0usize..8usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(64u32) == 0u32 && r > 0u32 { 64u32 } else { r.wrapping_rem(64u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    sha256_update_nblocks(0u32, buf_last.0, &mut tmp_block_state);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    sha256_update_last(prev_len_last.wrapping_add(r as u64), r, buf_last.1, &mut tmp_block_state);
    sha256_finish(&mut tmp_block_state, output)
}

pub fn hash_256(output: &mut [u8], input: &mut [u8], input_len: u32) -> ()
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut st: [u32; 8] = [0u32; 8usize];
    sha256_init(&mut st);
    let rem: u32 = input_len.wrapping_rem(64u32);
    let len·: u64 = input_len as u64;
    sha256_update_nblocks(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(64u32);
    let b0: &mut [u8] = ib;
    let lb: (&mut [u8], &mut [u8]) = b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
    sha256_update_last(len·, rem, lb.1, &mut st);
    sha256_finish(&mut st, rb)
}

pub fn malloc_224() -> Vec<crate::hacl::streaming_types::state_32>
{
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    let mut block_state: Vec<u32> = vec![0u32; 8usize];
    sha224_init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_32 =
        crate::hacl::streaming_types::state_32
        { block_state: block_state, buf: buf, total_len: 0u32 as u64 };
    let mut p: Vec<crate::hacl::streaming_types::state_32> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_32> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset_224(state: &mut [crate::hacl::streaming_types::state_32]) -> ()
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    sha224_init(block_state);
    (state[0usize]).total_len = 0u32 as u64
}

pub fn update_224(
    state: &mut [crate::hacl::streaming_types::state_32],
    input: &mut [u8],
    input_len: u32
) ->
    crate::hacl::streaming_types::error_code
{ update_224_256(state, input, input_len) }

pub fn digest_224(state: &mut [crate::hacl::streaming_types::state_32], output: &mut [u8]) ->
    ()
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut tmp_block_state: [u32; 8] = [0u32; 8usize];
    ((&mut tmp_block_state)[0usize..8usize]).copy_from_slice(&block_state[0usize..8usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(64u32) == 0u32 && r > 0u32 { 64u32 } else { r.wrapping_rem(64u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    sha224_update_nblocks(0u32, buf_last.0, &mut tmp_block_state);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    sha224_update_last(prev_len_last.wrapping_add(r as u64), r, buf_last.1, &mut tmp_block_state);
    sha224_finish(&mut tmp_block_state, output)
}

pub fn hash_224(output: &mut [u8], input: &mut [u8], input_len: u32) -> ()
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut st: [u32; 8] = [0u32; 8usize];
    sha224_init(&mut st);
    let rem: u32 = input_len.wrapping_rem(64u32);
    let len·: u64 = input_len as u64;
    sha224_update_nblocks(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(64u32);
    let b0: &mut [u8] = ib;
    let lb: (&mut [u8], &mut [u8]) = b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
    sha224_update_last(len·, rem, lb.1, &mut st);
    sha224_finish(&mut st, rb)
}

pub fn malloc_512() -> Vec<crate::hacl::streaming_types::state_64>
{
    let mut buf: Vec<u8> = vec![0u8; 128usize];
    let mut block_state: Vec<u64> = vec![0u64; 8usize];
    sha512_init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_64 =
        crate::hacl::streaming_types::state_64
        { block_state: block_state, buf: buf, total_len: 0u32 as u64 };
    let mut p: Vec<crate::hacl::streaming_types::state_64> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_64> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn copy_512(state: &mut [crate::hacl::streaming_types::state_64]) ->
    Vec<crate::hacl::streaming_types::state_64>
{
    let block_state0: &mut [u64] = &mut (state[0usize]).block_state;
    let buf0: &mut [u8] = &mut (state[0usize]).buf;
    let total_len0: u64 = (state[0usize]).total_len;
    let mut buf: Vec<u8> = vec![0u8; 128usize];
    ((&mut buf)[0usize..128usize]).copy_from_slice(&buf0[0usize..128usize]);
    let mut block_state: Vec<u64> = vec![0u64; 8usize];
    ((&mut block_state)[0usize..8usize]).copy_from_slice(&block_state0[0usize..8usize]);
    let mut s: crate::hacl::streaming_types::state_64 =
        crate::hacl::streaming_types::state_64
        { block_state: block_state, buf: buf, total_len: total_len0 };
    let mut p: Vec<crate::hacl::streaming_types::state_64> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_64> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset_512(state: &mut [crate::hacl::streaming_types::state_64]) -> ()
{
    let block_state: &mut [u64] = &mut (state[0usize]).block_state;
    sha512_init(block_state);
    (state[0usize]).total_len = 0u32 as u64
}

#[inline] fn update_384_512(
    state: &mut [crate::hacl::streaming_types::state_64],
    chunk: &mut [u8],
    chunk_len: u32
) ->
    crate::hacl::streaming_types::error_code
{
    let block_state: &mut [u64] = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 18446744073709551615u64.wrapping_sub(total_len)
    { crate::hacl::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if total_len.wrapping_rem(128u32 as u64) == 0u64 && total_len > 0u64
            { 128u32 }
            else
            { total_len.wrapping_rem(128u32 as u64) as u32 };
        if chunk_len <= 128u32.wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(128u32 as u64) == 0u64 && total_len1 > 0u64
                { 128u32 }
                else
                { total_len1.wrapping_rem(128u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2
        }
        else
        if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(128u32 as u64) == 0u64 && total_len1 > 0u64
                { 128u32 }
                else
                { total_len1.wrapping_rem(128u32 as u64) as u32 };
            if ! (sz1 == 0u32) { sha512_update_nblocks(128u32, buf, block_state) };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(128u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 128u32 }
                else
                { (chunk_len as u64).wrapping_rem(128u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(128u32);
            let data1_len: u32 = n_blocks.wrapping_mul(128u32);
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            sha512_update_nblocks(
                data1_len.wrapping_div(128u32).wrapping_mul(128u32),
                data2.0,
                block_state
            );
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = 128u32.wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(128u32 as u64) == 0u64 && total_len1 > 0u64
                { 128u32 }
                else
                { total_len1.wrapping_rem(128u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            (state[0usize]).total_len = total_len2;
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let sz10: u32 =
                if total_len10.wrapping_rem(128u32 as u64) == 0u64 && total_len10 > 0u64
                { 128u32 }
                else
                { total_len10.wrapping_rem(128u32 as u64) as u32 };
            if ! (sz10 == 0u32) { sha512_update_nblocks(128u32, buf0, block_state) };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(128u32 as u64) == 0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                { 128u32 }
                else
                { (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(128u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(128u32);
            let data1_len: u32 = n_blocks.wrapping_mul(128u32);
            let data2_len: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk2.1.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            sha512_update_nblocks(
                data1_len.wrapping_div(128u32).wrapping_mul(128u32),
                data2.0,
                block_state
            );
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::hacl::streaming_types::error_code::Success
    }
}

pub fn update_512(
    state: &mut [crate::hacl::streaming_types::state_64],
    input: &mut [u8],
    input_len: u32
) ->
    crate::hacl::streaming_types::error_code
{ update_384_512(state, input, input_len) }

pub fn digest_512(state: &mut [crate::hacl::streaming_types::state_64], output: &mut [u8]) ->
    ()
{
    let block_state: &mut [u64] = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(128u32 as u64) == 0u64 && total_len > 0u64
        { 128u32 }
        else
        { total_len.wrapping_rem(128u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut tmp_block_state: [u64; 8] = [0u64; 8usize];
    ((&mut tmp_block_state)[0usize..8usize]).copy_from_slice(&block_state[0usize..8usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(128u32) == 0u32 && r > 0u32 { 128u32 } else { r.wrapping_rem(128u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    sha512_update_nblocks(0u32, buf_last.0, &mut tmp_block_state);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    sha512_update_last(
        crate::fstar::uint128::add(
            crate::fstar::uint128::uint64_to_uint128(prev_len_last),
            crate::fstar::uint128::uint64_to_uint128(r as u64)
        ),
        r,
        buf_last.1,
        &mut tmp_block_state
    );
    sha512_finish(&mut tmp_block_state, output)
}

pub fn hash_512(output: &mut [u8], input: &mut [u8], input_len: u32) -> ()
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut st: [u64; 8] = [0u64; 8usize];
    sha512_init(&mut st);
    let rem: u32 = input_len.wrapping_rem(128u32);
    let len·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::uint64_to_uint128(input_len as u64);
    sha512_update_nblocks(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(128u32);
    let b0: &mut [u8] = ib;
    let lb: (&mut [u8], &mut [u8]) = b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
    sha512_update_last(len·, rem, lb.1, &mut st);
    sha512_finish(&mut st, rb)
}

pub fn malloc_384() -> Vec<crate::hacl::streaming_types::state_64>
{
    let mut buf: Vec<u8> = vec![0u8; 128usize];
    let mut block_state: Vec<u64> = vec![0u64; 8usize];
    sha384_init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_64 =
        crate::hacl::streaming_types::state_64
        { block_state: block_state, buf: buf, total_len: 0u32 as u64 };
    let mut p: Vec<crate::hacl::streaming_types::state_64> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_64> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset_384(state: &mut [crate::hacl::streaming_types::state_64]) -> ()
{
    let block_state: &mut [u64] = &mut (state[0usize]).block_state;
    sha384_init(block_state);
    (state[0usize]).total_len = 0u32 as u64
}

pub fn update_384(
    state: &mut [crate::hacl::streaming_types::state_64],
    input: &mut [u8],
    input_len: u32
) ->
    crate::hacl::streaming_types::error_code
{ update_384_512(state, input, input_len) }

pub fn digest_384(state: &mut [crate::hacl::streaming_types::state_64], output: &mut [u8]) ->
    ()
{
    let block_state: &mut [u64] = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(128u32 as u64) == 0u64 && total_len > 0u64
        { 128u32 }
        else
        { total_len.wrapping_rem(128u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut tmp_block_state: [u64; 8] = [0u64; 8usize];
    ((&mut tmp_block_state)[0usize..8usize]).copy_from_slice(&block_state[0usize..8usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(128u32) == 0u32 && r > 0u32 { 128u32 } else { r.wrapping_rem(128u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    sha384_update_nblocks(0u32, buf_last.0, &mut tmp_block_state);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    sha384_update_last(
        crate::fstar::uint128::add(
            crate::fstar::uint128::uint64_to_uint128(prev_len_last),
            crate::fstar::uint128::uint64_to_uint128(r as u64)
        ),
        r,
        buf_last.1,
        &mut tmp_block_state
    );
    sha384_finish(&mut tmp_block_state, output)
}

pub fn hash_384(output: &mut [u8], input: &mut [u8], input_len: u32) -> ()
{
    let ib: &mut [u8] = input;
    let rb: &mut [u8] = output;
    let mut st: [u64; 8] = [0u64; 8usize];
    sha384_init(&mut st);
    let rem: u32 = input_len.wrapping_rem(128u32);
    let len·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::uint64_to_uint128(input_len as u64);
    sha384_update_nblocks(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(128u32);
    let b0: &mut [u8] = ib;
    let lb: (&mut [u8], &mut [u8]) = b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
    sha384_update_last(len·, rem, lb.1, &mut st);
    sha384_finish(&mut st, rb)
}
