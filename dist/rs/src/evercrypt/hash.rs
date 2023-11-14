const k224_256: [u32; 64] =
    [0x428a2f98u32,
        0x71374491u32,
        0xb5c0fbcfu32,
        0xe9b5dba5u32,
        0x3956c25bu32,
        0x59f111f1u32,
        0x923f82a4u32,
        0xab1c5ed5u32,
        0xd807aa98u32,
        0x12835b01u32,
        0x243185beu32,
        0x550c7dc3u32,
        0x72be5d74u32,
        0x80deb1feu32,
        0x9bdc06a7u32,
        0xc19bf174u32,
        0xe49b69c1u32,
        0xefbe4786u32,
        0x0fc19dc6u32,
        0x240ca1ccu32,
        0x2de92c6fu32,
        0x4a7484aau32,
        0x5cb0a9dcu32,
        0x76f988dau32,
        0x983e5152u32,
        0xa831c66du32,
        0xb00327c8u32,
        0xbf597fc7u32,
        0xc6e00bf3u32,
        0xd5a79147u32,
        0x06ca6351u32,
        0x14292967u32,
        0x27b70a85u32,
        0x2e1b2138u32,
        0x4d2c6dfcu32,
        0x53380d13u32,
        0x650a7354u32,
        0x766a0abbu32,
        0x81c2c92eu32,
        0x92722c85u32,
        0xa2bfe8a1u32,
        0xa81a664bu32,
        0xc24b8b70u32,
        0xc76c51a3u32,
        0xd192e819u32,
        0xd6990624u32,
        0xf40e3585u32,
        0x106aa070u32,
        0x19a4c116u32,
        0x1e376c08u32,
        0x2748774cu32,
        0x34b0bcb5u32,
        0x391c0cb3u32,
        0x4ed8aa4au32,
        0x5b9cca4fu32,
        0x682e6ff3u32,
        0x748f82eeu32,
        0x78a5636fu32,
        0x84c87814u32,
        0x8cc70208u32,
        0x90befffau32,
        0xa4506cebu32,
        0xbef9a3f7u32,
        0xc67178f2u32];

pub fn update_multi_256(s: &mut [u32], blocks: &mut [u8], n: u32) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_shaext: bool = crate::evercrypt::autoconfig2::has_shaext();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        if has_shaext && has_sse
        {
            let n1: u64 = n as u64;
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_sha::sha256_update(s, blocks, n1, &mut k224_256)
            )
        }
        else
        { crate::hacl::hash_sha2::sha256_update_nblocks(n.wrapping_mul(64u32), blocks, s) }
    }
    else
    {
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut k224_256);
        crate::hacl::hash_sha2::sha256_update_nblocks(n.wrapping_mul(64u32), blocks, s)
    }
}

pub fn hash_256(input: &mut [u8], input_len: u32, dst: &mut [u8]) -> ()
{
    let mut st: [u32; 8] = [0u32; 8usize];
    for i in 0u32..8u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut st).split_at_mut(0usize);
        let x: u32 = (&crate::hacl::hash_sha2::h256)[i as usize];
        os.1[i as usize] = x
    };
    let s: &mut [u32] = &mut st;
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_n1: u32 =
        if input_len.wrapping_rem(64u32) == 0u32 && blocks_n > 0u32
        { blocks_n.wrapping_sub(1u32) }
        else
        { blocks_n };
    let blocks_len: u32 = blocks_n1.wrapping_mul(64u32);
    let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&mut [u8], &mut [u8]) = blocks.1.split_at_mut(blocks_len as usize);
    let blocks_n0: u32 = blocks_n1;
    let blocks_len0: u32 = blocks_len;
    let blocks0: &mut [u8] = rest.0;
    let rest_len0: u32 = rest_len;
    let rest0: &mut [u8] = rest.1;
    update_multi_256(s, blocks0, blocks_n0);
    crate::hacl::hash_sha2::sha256_update_last(
        (blocks_len0 as u64).wrapping_add(rest_len0 as u64),
        rest_len0,
        rest0,
        s
    );
    crate::hacl::hash_sha2::sha256_finish(s, dst)
}

fn hash_224(input: &mut [u8], input_len: u32, dst: &mut [u8]) -> ()
{
    let mut st: [u32; 8] = [0u32; 8usize];
    for i in 0u32..8u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut st).split_at_mut(0usize);
        let x: u32 = (&crate::hacl::hash_sha2::h224)[i as usize];
        os.1[i as usize] = x
    };
    let s: &mut [u32] = &mut st;
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_n1: u32 =
        if input_len.wrapping_rem(64u32) == 0u32 && blocks_n > 0u32
        { blocks_n.wrapping_sub(1u32) }
        else
        { blocks_n };
    let blocks_len: u32 = blocks_n1.wrapping_mul(64u32);
    let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&mut [u8], &mut [u8]) = blocks.1.split_at_mut(blocks_len as usize);
    let blocks_n0: u32 = blocks_n1;
    let blocks_len0: u32 = blocks_len;
    let blocks0: &mut [u8] = rest.0;
    let rest_len0: u32 = rest_len;
    let rest0: &mut [u8] = rest.1;
    update_multi_256(s, blocks0, blocks_n0);
    crate::hacl::hash_sha2::sha224_update_last(
        (blocks_len0 as u64).wrapping_add(rest_len0 as u64),
        rest_len0,
        rest0,
        s
    );
    crate::hacl::hash_sha2::sha224_finish(s, dst)
}

pub const md5_hash_len: u32 = 16u32;

pub const sha1_hash_len: u32 = 20u32;

pub const sha2_224_hash_len: u32 = 28u32;

pub const sha2_256_hash_len: u32 = 32u32;

pub const sha2_384_hash_len: u32 = 48u32;

pub const sha2_512_hash_len: u32 = 64u32;

pub const sha3_224_hash_len: u32 = 28u32;

pub const sha3_256_hash_len: u32 = 32u32;

pub const sha3_384_hash_len: u32 = 48u32;

pub const sha3_512_hash_len: u32 = 64u32;

pub const blake2s_hash_len: u32 = 32u32;

pub const blake2b_hash_len: u32 = 64u32;
