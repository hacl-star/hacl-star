pub fn blake2s_init(hash: &mut [crate::lib::intvector_intrinsics::vec128], kk: u32, nn: u32) ->
    ()
{
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        hash.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r2.1.split_at_mut(1usize);
    let iv0: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[0usize];
    let iv1: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[1usize];
    let iv2: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[2usize];
    let iv3: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[3usize];
    let iv4: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[4usize];
    let iv5: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[5usize];
    let iv6: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[6usize];
    let iv7: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[7usize];
    r3.0[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv0, iv1, iv2, iv3);
    r3.1[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv4, iv5, iv6, iv7);
    let kk_shift_8: u32 = kk.wrapping_shl(8u32);
    let iv0_: u32 = iv0 ^ (0x01010000u32 ^ (kk_shift_8 ^ nn));
    r1.0[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv0_, iv1, iv2, iv3);
    r2.0[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv4, iv5, iv6, iv7)
}

pub fn blake2s_update_multi(
    len: u32,
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
    prev: u64,
    blocks: &mut [u8],
    nb: u32
) ->
    ()
{
    crate::lowstar::ignore::ignore::<u32>(len);
    for i in 0u32..nb
    {
        let totlen: u64 = prev.wrapping_add(i.wrapping_add(1u32).wrapping_mul(64u32) as u64);
        let b: (&mut [u8], &mut [u8]) =
            blocks.split_at_mut((i.wrapping_mul(64u32) as usize).wrapping_add(0usize));
        crate::hacl::blake2s_128::blake2s_update_block(wv, hash, falsebool, totlen, b.1)
    }
}

fn blake2s_update(
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
    kk: u32,
    k: &mut [u8],
    ll: u32,
    d: &mut [u8]
) ->
    ()
{
    let lb: u64 = 64u32 as u64;
    if kk > 0u32
    {
        crate::hacl::blake2s_128::blake2s_update_key(wv, hash, kk, k, ll);
        if ! ll == 0u32 { crate::hacl::blake2s_128::blake2s_update_blocks(ll, wv, hash, lb, d) }
    }
    else
    { crate::hacl::blake2s_128::blake2s_update_blocks(ll, wv, hash, 0u32 as u64, d) }
}

pub fn store_state128s_to_state32(
    st32: &mut [u32],
    st: &mut [crate::lib::intvector_intrinsics::vec128]
) ->
    ()
{
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        st.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r2.1.split_at_mut(1usize);
    let b0: (&mut [u32], &mut [u32]) = st32.split_at_mut(0usize);
    let b1: (&mut [u32], &mut [u32]) = b0.1.split_at_mut(4usize);
    let b2: (&mut [u32], &mut [u32]) = b1.1.split_at_mut(4usize);
    let b3: (&mut [u32], &mut [u32]) = b2.1.split_at_mut(4usize);
    let mut b8: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b8, r1.0[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b1.0.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            (&mut b8).split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut b80: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b80, r2.0[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b2.0.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            (&mut b80).split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut b81: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b81, r3.0[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b3.0.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            (&mut b81).split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut b82: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b82, r3.1[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b3.1.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            (&mut b82).split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    }
}

pub fn load_state128s_from_state32(
    st: &mut [crate::lib::intvector_intrinsics::vec128],
    st32: &mut [u32]
) ->
    ()
{
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        st.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r2.1.split_at_mut(1usize);
    let b0: (&mut [u32], &mut [u32]) = st32.split_at_mut(0usize);
    let b1: (&mut [u32], &mut [u32]) = b0.1.split_at_mut(4usize);
    let b2: (&mut [u32], &mut [u32]) = b1.1.split_at_mut(4usize);
    let b3: (&mut [u32], &mut [u32]) = b2.1.split_at_mut(4usize);
    r1.0[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b1.0[0usize],
            b1.0[1usize],
            b1.0[2usize],
            b1.0[3usize]
        );
    r2.0[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b2.0[0usize],
            b2.0[1usize],
            b2.0[2usize],
            b2.0[3usize]
        );
    r3.0[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b3.0[0usize],
            b3.0[1usize],
            b3.0[2usize],
            b3.0[3usize]
        );
    r3.1[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b3.1[0usize],
            b3.1[1usize],
            b3.1[2usize],
            b3.1[3usize]
        )
}

pub fn blake2s_malloc(r: ()) -> &mut [crate::lib::intvector_intrinsics::vec128]
{
    let mut buf: Vec<crate::lib::intvector_intrinsics::vec128> =
        vec![crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    &mut buf
}
