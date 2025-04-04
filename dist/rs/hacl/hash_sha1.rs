#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

const _h0: [u32; 5] =
    [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32, 0xc3d2e1f0u32];

pub(crate) fn init(s: &mut [u32])
{ krml::unroll_for!(5, "i", 0u32, 1u32, s[i as usize] = (&crate::hash_sha1::_h0)[i as usize]) }

fn update(h: &mut [u32], l: &[u8])
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
                let b: (&[u8], &[u8]) = l.split_at(i.wrapping_mul(4u32) as usize);
                let u: u32 = lowstar::endianness::load32_be(b.1);
                u
            }
            else
            {
                let wmit3: u32 = (&_w)[i.wrapping_sub(3u32) as usize];
                let wmit8: u32 = (&_w)[i.wrapping_sub(8u32) as usize];
                let wmit14: u32 = (&_w)[i.wrapping_sub(14u32) as usize];
                let wmit16: u32 = (&_w)[i.wrapping_sub(16u32) as usize];
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
        let wmit: u32 = (&_w)[i as usize];
        let ite: u32 =
            if i < 20u32
            { _b & _c ^ ! _b & _d }
            else if 39u32 < i && i < 60u32 { _b & _c ^ (_b & _d ^ _c & _d) } else { _b ^ (_c ^ _d) };
        let ite0: u32 =
            if i < 20u32
            { 0x5a827999u32 }
            else if i < 40u32
            { 0x6ed9eba1u32 }
            else if i < 60u32 { 0x8f1bbcdcu32 } else { 0xca62c1d6u32 };
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

fn pad(len: u64, dst: &mut [u8])
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
            128u32.wrapping_sub(9u32.wrapping_add(len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
                64u32
            )
            as
            usize
        );
    lowstar::endianness::store64_be(dst3.1, len.wrapping_shl(3u32))
}

pub(crate) fn finish(s: &[u32], dst: &mut [u8])
{
    krml::unroll_for!(
        5,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store32_be(
            &mut dst[i.wrapping_mul(4u32) as usize..],
            (&s[0usize..])[i as usize]
        )
    )
}

pub(crate) fn update_multi(s: &mut [u32], blocks: &[u8], n_blocks: u32)
{
    for i in 0u32..n_blocks
    {
        let sz: u32 = 64u32;
        let block: (&[u8], &[u8]) = blocks.split_at(sz.wrapping_mul(i) as usize);
        crate::hash_sha1::update(s, block.1)
    }
}

pub(crate) fn update_last(s: &mut [u32], prev_len: u64, input: &[u8], input_len: u32)
{
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_len: u32 = blocks_n.wrapping_mul(64u32);
    let blocks: (&[u8], &[u8]) = input.split_at(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&[u8], &[u8]) = blocks.1.split_at(blocks_len as usize);
    crate::hash_sha1::update_multi(s, rest.0, blocks_n);
    let total_input_len: u64 = prev_len.wrapping_add(input_len as u64);
    let pad_len: u32 =
        1u32.wrapping_add(
            128u32.wrapping_sub(
                9u32.wrapping_add(total_input_len.wrapping_rem(64u32 as u64) as u32)
            ).wrapping_rem(64u32)
        ).wrapping_add(8u32);
    let tmp_len: u32 = rest_len.wrapping_add(pad_len);
    let mut tmp_twoblocks: [u8; 128] = [0u8; 128usize];
    let tmp: (&mut [u8], &mut [u8]) = tmp_twoblocks.split_at_mut(0usize);
    let tmp_rest: (&mut [u8], &mut [u8]) = tmp.1.split_at_mut(0usize);
    let tmp_pad: (&mut [u8], &mut [u8]) = tmp_rest.1.split_at_mut(rest_len as usize);
    (tmp_pad.0[0usize..rest_len as usize]).copy_from_slice(&rest.1[0usize..rest_len as usize]);
    crate::hash_sha1::pad(total_input_len, tmp_pad.1);
    crate::hash_sha1::update_multi(s, tmp.1, tmp_len.wrapping_div(64u32))
}

pub(crate) fn hash_oneshot(output: &mut [u8], input: &[u8], input_len: u32)
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
    let blocks: (&[u8], &[u8]) = input.split_at(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&[u8], &[u8]) = blocks.1.split_at(blocks_len as usize);
    let blocks_n0: u32 = blocks_n1;
    let blocks_len0: u32 = blocks_len;
    let blocks0: &[u8] = rest.0;
    let rest_len0: u32 = rest_len;
    let rest0: &[u8] = rest.1;
    crate::hash_sha1::update_multi(&mut s, blocks0, blocks_n0);
    crate::hash_sha1::update_last(&mut s, blocks_len0 as u64, rest0, rest_len0);
    crate::hash_sha1::finish(&s, output)
}

pub type state_t = crate::streaming_types::state_32;

pub fn malloc() -> Box<[crate::streaming_types::state_32]>
{
    let buf: Box<[u8]> = vec![0u8; 64usize].into_boxed_slice();
    let buf1: &[u8] = &buf;
    let mut b: Box<[u32]> = vec![0u32; 5usize].into_boxed_slice();
    let mut block_state: crate::streaming_types::optional_32 =
        crate::streaming_types::optional_32::Some { v: &mut b };
    match block_state
    {
        crate::streaming_types::optional_32::None => { [].into() },
        crate::streaming_types::optional_32::Some { v: ref mut block_state1 } =>
          {
              let block_state2: &mut [u32] = *block_state1;
              let k·: crate::streaming_types::optional = crate::streaming_types::optional::Some;
              match k·
              {
                  crate::streaming_types::optional::None => [].into(),
                  crate::streaming_types::optional::Some =>
                    {
                        crate::hash_sha1::init(block_state2);
                        let s: crate::streaming_types::state_32 =
                            crate::streaming_types::state_32
                            {
                                block_state: (*block_state2).into(),
                                buf: (*buf1).into(),
                                total_len: 0u32 as u64
                            };
                        let p: Box<[crate::streaming_types::state_32]> = vec![s].into_boxed_slice();
                        p
                    },
                  _ => panic!("Precondition of the function most likely violated")
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn reset(state: &mut [crate::streaming_types::state_32])
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    crate::hash_sha1::init(block_state);
    let total_len: u64 = 0u32 as u64;
    (state[0usize]).total_len = total_len
}

/**
0 = success, 1 = max length exceeded
*/
pub fn
update0(state: &mut [crate::streaming_types::state_32], chunk: &[u8], chunk_len: u32) ->
    crate::streaming_types::error_code
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 2305843009213693951u64.wrapping_sub(total_len)
    { crate::streaming_types::error_code::MaximumLengthExceeded }
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
        else if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            if sz1 != 0u32 { crate::hash_sha1::update_multi(block_state, buf, 1u32) };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(64u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&[u8], &[u8]) = chunk.split_at(0usize);
            let data2: (&[u8], &[u8]) = data1.1.split_at(data1_len as usize);
            crate::hash_sha1::update_multi(block_state, data2.0, data1_len.wrapping_div(64u32));
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = 64u32.wrapping_sub(sz);
            let chunk1: (&[u8], &[u8]) = chunk.split_at(0usize);
            let chunk2: (&[u8], &[u8]) = chunk1.1.split_at(diff as usize);
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
            if sz10 != 0u32 { crate::hash_sha1::update_multi(block_state, buf0, 1u32) };
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
            let data1: (&[u8], &[u8]) = chunk2.1.split_at(0usize);
            let data2: (&[u8], &[u8]) = data1.1.split_at(data1_len as usize);
            crate::hash_sha1::update_multi(block_state, data2.0, data1_len.wrapping_div(64u32));
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

pub fn digest(state: &[crate::streaming_types::state_32], output: &mut [u8])
{
    let block_state: &[u32] = &(state[0usize]).block_state;
    let buf_: &[u8] = &(state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&[u8], &[u8]) = buf_.split_at(0usize);
    let mut tmp_block_state: [u32; 5] = [0u32; 5usize];
    ((&mut tmp_block_state)[0usize..5usize]).copy_from_slice(&block_state[0usize..5usize]);
    let buf_multi: (&[u8], &[u8]) = buf_1.1.split_at(0usize);
    let ite: u32 =
        if r.wrapping_rem(64u32) == 0u32 && r > 0u32 { 64u32 } else { r.wrapping_rem(64u32) };
    let buf_last: (&[u8], &[u8]) = buf_multi.1.split_at(r.wrapping_sub(ite) as usize);
    crate::hash_sha1::update_multi(&mut tmp_block_state, buf_last.0, 0u32);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    crate::hash_sha1::update_last(&mut tmp_block_state, prev_len_last, buf_last.1, r);
    crate::hash_sha1::finish(&tmp_block_state, output)
}

pub fn copy(state: &[crate::streaming_types::state_32]) ->
    Box<[crate::streaming_types::state_32]>
{
    let block_state0: &[u32] = &(state[0usize]).block_state;
    let buf0: &[u8] = &(state[0usize]).buf;
    let total_len0: u64 = (state[0usize]).total_len;
    let mut buf: Box<[u8]> = vec![0u8; 64usize].into_boxed_slice();
    ((&mut buf)[0usize..64usize]).copy_from_slice(&buf0[0usize..64usize]);
    let mut b: Box<[u32]> = vec![0u32; 5usize].into_boxed_slice();
    let mut block_state: crate::streaming_types::optional_32 =
        crate::streaming_types::optional_32::Some { v: &mut b };
    match block_state
    {
        crate::streaming_types::optional_32::None => { [].into() },
        crate::streaming_types::optional_32::Some { v: ref mut block_state1 } =>
          {
              let block_state2: &mut [u32] = *block_state1;
              (block_state2[0usize..5usize]).copy_from_slice(&block_state0[0usize..5usize]);
              let k·: crate::streaming_types::optional = crate::streaming_types::optional::Some;
              match k·
              {
                  crate::streaming_types::optional::None => [].into(),
                  crate::streaming_types::optional::Some =>
                    {
                        let s: crate::streaming_types::state_32 =
                            crate::streaming_types::state_32
                            { block_state: (*block_state2).into(), buf, total_len: total_len0 };
                        let p: Box<[crate::streaming_types::state_32]> = vec![s].into_boxed_slice();
                        p
                    },
                  _ => panic!("Precondition of the function most likely violated")
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn hash(output: &mut [u8], input: &[u8], input_len: u32)
{ crate::hash_sha1::hash_oneshot(output, input, input_len) }
