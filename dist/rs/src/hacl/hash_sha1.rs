const _h0: [u32; 5] =
    [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32, 0xc3d2e1f0u32];

pub fn legacy_init(s: &mut [u32]) -> ()
for i in 0u32..5u32 { s[i as usize] = (&mut _h0)[i as usize] }

fn legacy_update(h: &mut [u32], l: &mut [u8]) -> ()
{
    let ha: u32 = h[0usize];
    let hb: u32 = h[1usize];
    let hc: u32 = h[2usize];
    let hd: u32 = h[3usize];
    let he: u32 = h[4usize];
    let mut _w: [u32; 80] = [0u32; 80usize];
    for i in 0u32..80u32
    {
        let v: u32 =
            if i < 16u32
            {
                let b: (&mut [u8], &mut [u8]) =
                    l.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
                let u: u32 = crate::lowstar::endianness::load32_be(b.1);
                u
            }
            else
            {
                let wmit3: u32 = (&mut _w)[i.wrapping_sub(3u32) as usize];
                let wmit8: u32 = (&mut _w)[i.wrapping_sub(8u32) as usize];
                let wmit14: u32 = (&mut _w)[i.wrapping_sub(14u32) as usize];
                let wmit16: u32 = (&mut _w)[i.wrapping_sub(16u32) as usize];
                (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))).wrapping_shl(1u32)
                |
                (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))).wrapping_shr(31u32)
            };
        (&mut _w)[i as usize] = v
    };
    for i in 0u32..80u32
    {
        let _a: u32 = h[0usize];
        let _b: u32 = h[1usize];
        let _c: u32 = h[2usize];
        let _d: u32 = h[3usize];
        let _e: u32 = h[4usize];
        let wmit: u32 = (&mut _w)[i as usize];
        let ite: u32 =
            if i < 20u32
            { _b & _c ^ ! _b & _d }
            else
            if 39u32 < i && i < 60u32 { _b & _c ^ (_b & _d ^ _c & _d) } else { _b ^ (_c ^ _d) };
        let ite0: u32 =
            if i < 20u32
            { 0x5a827999u32 }
            else
            if i < 40u32
            { 0x6ed9eba1u32 }
            else
            if i < 60u32 { 0x8f1bbcdcu32 } else { 0xca62c1d6u32 };
        let _T: u32 =
            (_a.wrapping_shl(5u32) | _a.wrapping_shr(27u32)).wrapping_add(ite).wrapping_add(_e).wrapping_add(
                ite0
            ).wrapping_add(wmit);
        h[0usize] = _T;
        h[1usize] = _a;
        h[2usize] = _b.wrapping_shl(30u32) | _b.wrapping_shr(2u32);
        h[3usize] = _c;
        h[4usize] = _d
    };
    for i in 0u32..80u32 { (&mut _w)[i as usize] = 0u32 };
    let sta: u32 = h[0usize];
    let stb: u32 = h[1usize];
    let stc: u32 = h[2usize];
    let std: u32 = h[3usize];
    let ste: u32 = h[4usize];
    h[0usize] = sta.wrapping_add(ha);
    h[1usize] = stb.wrapping_add(hb);
    h[2usize] = stc.wrapping_add(hc);
    h[3usize] = std.wrapping_add(hd);
    h[4usize] = ste.wrapping_add(he)
}

fn legacy_pad(len: u64, dst: &mut [u8]) -> ()
{
    let dst1: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
    dst1.1[0usize] = 0x80u8;
    let dst2: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(1usize);
    for
    i
    in
    0u32..128u32.wrapping_sub(9u32.wrapping_add(len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
        64u32
    )
    { dst2.1[i as usize] = 0u8 };
    let dst3: (&mut [u8], &mut [u8]) =
        dst2.1.split_at_mut(
            (128u32.wrapping_sub(9u32.wrapping_add(len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
                64u32
            )
            as
            usize).wrapping_add(0usize)
        );
    crate::lowstar::endianness::store64_be(dst3.1, len.wrapping_shl(3u32))
}

pub fn legacy_finish(s: &mut [u32], dst: &mut [u8]) -> ()
for i in 0u32..5u32
{
    crate::lowstar::endianness::store32_be(
        &mut dst[i.wrapping_mul(4u32) as usize..],
        (&mut s[0usize..])[i as usize]
    )
}

pub fn legacy_update_multi(s: &mut [u32], blocks: &mut [u8], n_blocks: u32) -> ()
for i in 0u32..n_blocks
{
    let sz: u32 = 64u32;
    let block: (&mut [u8], &mut [u8]) =
        blocks.split_at_mut((sz.wrapping_mul(i) as usize).wrapping_add(0usize));
    legacy_update(s, block.1)
}

pub fn legacy_update_last(s: &mut [u32], prev_len: u64, input: &mut [u8], input_len: u32) -> ()
{
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_len: u32 = blocks_n.wrapping_mul(64u32);
    let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&mut [u8], &mut [u8]) =
        blocks.1.split_at_mut((blocks_len as usize).wrapping_add(0usize));
    legacy_update_multi(s, rest.0, blocks_n);
    let total_input_len: u64 = prev_len.wrapping_add(input_len as u64);
    let pad_len: u32 =
        1u32.wrapping_add(
            128u32.wrapping_sub(
                9u32.wrapping_add(total_input_len.wrapping_rem(64u32 as u64) as u32)
            ).wrapping_rem(64u32)
        ).wrapping_add(8u32);
    let tmp_len: u32 = rest_len.wrapping_add(pad_len);
    let mut tmp_twoblocks: [u8; 128] = [0u8; 128usize];
    let tmp: (&mut [u8], &mut [u8]) = (&mut tmp_twoblocks).split_at_mut(0usize);
    let tmp_rest: (&mut [u8], &mut [u8]) = tmp.1.split_at_mut(0usize);
    let tmp_pad: (&mut [u8], &mut [u8]) =
        tmp_rest.1.split_at_mut((rest_len as usize).wrapping_add(0usize));
    (tmp_pad.0[0usize..0usize + rest_len as usize]).copy_from_slice(
        &rest.1[0usize..0usize + rest_len as usize]
    );
    legacy_pad(total_input_len, tmp_pad.1);
    legacy_update_multi(s, tmp_pad.0, tmp_len.wrapping_div(64u32))
}

pub fn legacy_hash(input: &mut [u8], input_len: u32, dst: &mut [u8]) -> ()
{
    let mut s: [u32; 5] =
        [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32, 0xc3d2e1f0u32];
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_n1: u32 =
        if input_len.wrapping_rem(64u32) == 0u32 && blocks_n > 0u32
        { blocks_n.wrapping_sub(1u32) }
        else
        { blocks_n };
    let blocks_len: u32 = blocks_n1.wrapping_mul(64u32);
    let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&mut [u8], &mut [u8]) =
        blocks.1.split_at_mut((blocks_len as usize).wrapping_add(0usize));
    let blocks_n0: u32 = blocks_n1;
    let blocks_len0: u32 = blocks_len;
    let blocks0: &mut [u8] = rest.0;
    let rest_len0: u32 = rest_len;
    let rest0: &mut [u8] = rest.1;
    legacy_update_multi(&mut s, blocks0, blocks_n0);
    legacy_update_last(&mut s, blocks_len0 as u64, rest0, rest_len0);
    legacy_finish(&mut s, dst)
}

pub fn legacy_hash(input: &mut [u8], input_len: u32, dst: &mut [u8]) -> ()
{ legacy_hash(input, input_len, dst) }
