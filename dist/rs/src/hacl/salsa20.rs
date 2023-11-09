fn quarter_round(st: &mut [u32], a: u32, b: u32, c: u32, d: u32) -> ()
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

fn double_round(st: &mut [u32]) -> ()
{
    quarter_round(st, 0u32, 4u32, 8u32, 12u32);
    quarter_round(st, 5u32, 9u32, 13u32, 1u32);
    quarter_round(st, 10u32, 14u32, 2u32, 6u32);
    quarter_round(st, 15u32, 3u32, 7u32, 11u32);
    quarter_round(st, 0u32, 1u32, 2u32, 3u32);
    quarter_round(st, 5u32, 6u32, 7u32, 4u32);
    quarter_round(st, 10u32, 11u32, 8u32, 9u32);
    quarter_round(st, 15u32, 12u32, 13u32, 14u32)
}

fn rounds(st: &mut [u32]) -> ()
{
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st)
}

fn salsa20_core(k: &mut [u32], ctx: &mut [u32], ctr: u32) -> ()
{
    (k[0u32 as usize..0u32 as usize + 16u32 as usize]).copy_from_slice(
        &ctx[0u32 as usize..0u32 as usize + 16u32 as usize]
    );
    let ctr_u32: u32 = ctr;
    k[8u32 as usize] = (k[8u32 as usize]).wrapping_add(ctr_u32);
    rounds(k);
    for i in 0u32..16u32
    {
        let os: (&mut [u32], &mut [u32]) = k.split_at_mut(0usize);
        let x: u32 = (os.1[i as usize]).wrapping_add(ctx[i as usize]);
        os.1[i as usize] = x
    };
    k[8u32 as usize] = (k[8u32 as usize]).wrapping_add(ctr_u32)
}

fn salsa20_key_block0(out: &mut [u8], key: &mut [u8], n: &mut [u8]) -> ()
{
    let mut ctx: [u32; 16] = [0u32; 16u32 as usize];
    let mut k: [u32; 16] = [0u32; 16u32 as usize];
    let mut k32: [u32; 8] = [0u32; 8u32 as usize];
    let mut n32: [u32; 2] = [0u32; 2u32 as usize];
    for i in 0u32..8u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut k32).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            key.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    for i in 0u32..2u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut n32).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            n.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    (&mut ctx)[0u32 as usize] = 0x61707865u32;
    let k0: (&mut [u32], &mut [u32]) = (&mut k32).split_at_mut(0usize);
    let k1: (&mut [u32], &mut [u32]) = k0.1.split_at_mut(4usize);
    ((&mut ctx)[1u32 as usize..1u32 as usize + 4u32 as usize]).copy_from_slice(
        &k1.0[0u32 as usize..0u32 as usize + 4u32 as usize]
    );
    (&mut ctx)[5u32 as usize] = 0x3320646eu32;
    ((&mut ctx)[6u32 as usize..6u32 as usize + 2u32 as usize]).copy_from_slice(
        &(&mut n32)[0u32 as usize..0u32 as usize + 2u32 as usize]
    );
    (&mut ctx)[8u32 as usize] = 0u32;
    (&mut ctx)[9u32 as usize] = 0u32;
    (&mut ctx)[10u32 as usize] = 0x79622d32u32;
    ((&mut ctx)[11u32 as usize..11u32 as usize + 4u32 as usize]).copy_from_slice(
        &k1.1[0u32 as usize..0u32 as usize + 4u32 as usize]
    );
    (&mut ctx)[15u32 as usize] = 0x6b206574u32;
    salsa20_core(&mut k, &mut ctx, 0u32);
    for i in 0u32..16u32
    {
        crate::lowstar::endianness::store32_le(
            &mut out[i.wrapping_mul(4u32) as usize..],
            (&mut k)[i as usize]
        )
    }
}

fn hsalsa20(out: &mut [u8], key: &mut [u8], n: &mut [u8]) -> ()
{
    let mut ctx: [u32; 16] = [0u32; 16u32 as usize];
    let mut k32: [u32; 8] = [0u32; 8u32 as usize];
    let mut n32: [u32; 4] = [0u32; 4u32 as usize];
    for i in 0u32..8u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut k32).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            key.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut n32).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            n.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let k0: (&mut [u32], &mut [u32]) = (&mut k32).split_at_mut(0usize);
    let k1: (&mut [u32], &mut [u32]) = k0.1.split_at_mut(4usize);
    (&mut ctx)[0u32 as usize] = 0x61707865u32;
    ((&mut ctx)[1u32 as usize..1u32 as usize + 4u32 as usize]).copy_from_slice(
        &k1.0[0u32 as usize..0u32 as usize + 4u32 as usize]
    );
    (&mut ctx)[5u32 as usize] = 0x3320646eu32;
    ((&mut ctx)[6u32 as usize..6u32 as usize + 4u32 as usize]).copy_from_slice(
        &(&mut n32)[0u32 as usize..0u32 as usize + 4u32 as usize]
    );
    (&mut ctx)[10u32 as usize] = 0x79622d32u32;
    ((&mut ctx)[11u32 as usize..11u32 as usize + 4u32 as usize]).copy_from_slice(
        &k1.1[0u32 as usize..0u32 as usize + 4u32 as usize]
    );
    (&mut ctx)[15u32 as usize] = 0x6b206574u32;
    rounds(&mut ctx);
    let r0: u32 = (&mut ctx)[0u32 as usize];
    let r1: u32 = (&mut ctx)[5u32 as usize];
    let r2: u32 = (&mut ctx)[10u32 as usize];
    let r3: u32 = (&mut ctx)[15u32 as usize];
    let r4: u32 = (&mut ctx)[6u32 as usize];
    let r5: u32 = (&mut ctx)[7u32 as usize];
    let r6: u32 = (&mut ctx)[8u32 as usize];
    let r7: u32 = (&mut ctx)[9u32 as usize];
    let mut res: [u32; 8] = [r0, r1, r2, r3, r4, r5, r6, r7];
    for i in 0u32..8u32
    {
        crate::lowstar::endianness::store32_le(
            &mut out[i.wrapping_mul(4u32) as usize..],
            (&mut res)[i as usize]
        )
    }
}

pub fn salsa20_encrypt(
    len: u32,
    out: &mut [u8],
    text: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{ crate::hacl::impl::salsa20::salsa20_encrypt(len, out, text, key, n, ctr) }

pub fn salsa20_decrypt(
    len: u32,
    out: &mut [u8],
    cipher: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{ crate::hacl::impl::salsa20::salsa20_decrypt(len, out, cipher, key, n, ctr) }

pub fn salsa20_key_block0(out: &mut [u8], key: &mut [u8], n: &mut [u8]) -> ()
{ salsa20_key_block0(out, key, n) }

pub fn hsalsa20(out: &mut [u8], key: &mut [u8], n: &mut [u8]) -> () { hsalsa20(out, key, n) }