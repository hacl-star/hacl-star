pub const chacha20_constants: [u32; 4] =
    [0x61707865u32, 0x3320646eu32, 0x79622d32u32, 0x6b206574u32];

fn quarter_round(st: &mut [u32], a: u32, b: u32, c: u32, d: u32) -> ()
{
    let sta: u32 = st[a as usize];
    let stb: u32 = st[b as usize];
    let std: u32 = st[d as usize];
    let sta1: u32 = sta.wrapping_add(stb);
    let std1: u32 = std ^ sta1;
    let std2: u32 = std1.wrapping_shl(16u32) | std1.wrapping_shr(16u32);
    st[a as usize] = sta1;
    st[d as usize] = std2;
    let sta0: u32 = st[c as usize];
    let stb0: u32 = st[d as usize];
    let std0: u32 = st[b as usize];
    let sta10: u32 = sta0.wrapping_add(stb0);
    let std10: u32 = std0 ^ sta10;
    let std20: u32 = std10.wrapping_shl(12u32) | std10.wrapping_shr(20u32);
    st[c as usize] = sta10;
    st[b as usize] = std20;
    let sta2: u32 = st[a as usize];
    let stb1: u32 = st[b as usize];
    let std3: u32 = st[d as usize];
    let sta11: u32 = sta2.wrapping_add(stb1);
    let std11: u32 = std3 ^ sta11;
    let std21: u32 = std11.wrapping_shl(8u32) | std11.wrapping_shr(24u32);
    st[a as usize] = sta11;
    st[d as usize] = std21;
    let sta3: u32 = st[c as usize];
    let stb2: u32 = st[d as usize];
    let std4: u32 = st[b as usize];
    let sta12: u32 = sta3.wrapping_add(stb2);
    let std12: u32 = std4 ^ sta12;
    let std22: u32 = std12.wrapping_shl(7u32) | std12.wrapping_shr(25u32);
    st[c as usize] = sta12;
    st[b as usize] = std22
}

fn double_round(st: &mut [u32]) -> ()
{
    quarter_round(st, 0u32, 4u32, 8u32, 12u32);
    quarter_round(st, 1u32, 5u32, 9u32, 13u32);
    quarter_round(st, 2u32, 6u32, 10u32, 14u32);
    quarter_round(st, 3u32, 7u32, 11u32, 15u32);
    quarter_round(st, 0u32, 5u32, 10u32, 15u32);
    quarter_round(st, 1u32, 6u32, 11u32, 12u32);
    quarter_round(st, 2u32, 7u32, 8u32, 13u32);
    quarter_round(st, 3u32, 4u32, 9u32, 14u32)
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

fn chacha20_core(k: &mut [u32], ctx: &mut [u32], ctr: u32) -> ()
{
    (k[0usize..0usize + 16usize]).copy_from_slice(&ctx[0usize..0usize + 16usize]);
    let ctr_u32: u32 = ctr;
    k[12usize] = (k[12usize]).wrapping_add(ctr_u32);
    rounds(k);
    for i in 0u32..16u32
    {
        let os: (&mut [u32], &mut [u32]) = k.split_at_mut(0usize);
        let x: u32 = (os.1[i as usize]).wrapping_add(ctx[i as usize]);
        os.1[i as usize] = x
    };
    k[12usize] = (k[12usize]).wrapping_add(ctr_u32)
}

pub fn chacha20_init(ctx: &mut [u32], k: &mut [u8], n: &mut [u8], ctr: u32) -> ()
{
    for i in 0u32..4u32
    {
        let os: &mut [u32] = &mut (&mut ctx[0usize..])[0usize..];
        let x: u32 = (&chacha20_constants)[i as usize];
        os[i as usize] = x
    };
    for i in 0u32..8u32
    {
        let os: &mut [u32] = &mut (&mut ctx[4usize..])[0usize..];
        let bj: (&mut [u8], &mut [u8]) =
            k.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    };
    ctx[12usize] = ctr;
    for i in 0u32..3u32
    {
        let os: &mut [u32] = &mut (&mut ctx[13usize..])[0usize..];
        let bj: (&mut [u8], &mut [u8]) =
            n.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    }
}

fn chacha20_encrypt_block(ctx: &mut [u32], out: &mut [u8], incr: u32, text: &mut [u8]) -> ()
{
    let mut k: [u32; 16] = [0u32; 16usize];
    chacha20_core(&mut k, ctx, incr);
    let mut bl: [u32; 16] = [0u32; 16usize];
    for i in 0u32..16u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut bl).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            text.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    for i in 0u32..16u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut bl).split_at_mut(0usize);
        let x: u32 = os.1[i as usize] ^ (&mut k)[i as usize];
        os.1[i as usize] = x
    };
    for i in 0u32..16u32
    {
        crate::lowstar::endianness::store32_le(
            &mut out[i.wrapping_mul(4u32) as usize..],
            (&mut bl)[i as usize]
        )
    }
}

fn chacha20_encrypt_last(ctx: &mut [u32], len: u32, out: &mut [u8], incr: u32, text: &mut [u8]) ->
    ()
{
    let mut plain: [u8; 64] = [0u8; 64usize];
    ((&mut plain)[0usize..0usize + len as usize]).copy_from_slice(
        &text[0usize..0usize + len as usize]
    );
    let mut plain_copy: [u8; 64] = [0u8; 64usize];
    ((&mut plain_copy)[0usize..0usize + 64usize]).copy_from_slice(
        &(&mut plain)[0usize..0usize + 64usize]
    );
    chacha20_encrypt_block(ctx, &mut plain, incr, &mut plain_copy);
    (out[0usize..0usize + len as usize]).copy_from_slice(
        &(&mut (&mut plain)[0usize..])[0usize..0usize + len as usize]
    )
}

pub fn chacha20_update(ctx: &mut [u32], len: u32, out: &mut [u8], text: &mut [u8]) -> ()
{
    let rem: u32 = len.wrapping_rem(64u32);
    let nb: u32 = len.wrapping_div(64u32);
    let rem1: u32 = len.wrapping_rem(64u32);
    for i in 0u32..nb
    {
        chacha20_encrypt_block(
            ctx,
            &mut out[i.wrapping_mul(64u32) as usize..],
            i,
            &mut text[i.wrapping_mul(64u32) as usize..]
        )
    };
    if rem1 > 0u32
    {
        chacha20_encrypt_last(
            ctx,
            rem,
            &mut out[nb.wrapping_mul(64u32) as usize..],
            nb,
            &mut text[nb.wrapping_mul(64u32) as usize..]
        )
    }
}

pub fn chacha20_encrypt(
    len: u32,
    out: &mut [u8],
    text: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    chacha20_init(&mut ctx, key, n, ctr);
    chacha20_update(&mut ctx, len, out, text)
}

pub fn chacha20_decrypt(
    len: u32,
    out: &mut [u8],
    cipher: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    chacha20_init(&mut ctx, key, n, ctr);
    chacha20_update(&mut ctx, len, out, cipher)
}