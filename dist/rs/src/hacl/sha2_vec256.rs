fn sha224_init8(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
for i in 0u32..8u32
{
    let
    os:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        hash.split_at_mut(0usize);
    let hi: u32 = (&crate::hacl::hash_sha2::h224)[i as usize];
    let x: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load32(hi);
    os.1[i as usize] = x
}

fn sha256_init8(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
for i in 0u32..8u32
{
    let
    os:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        hash.split_at_mut(0usize);
    let hi: u32 = (&crate::hacl::hash_sha2::h256)[i as usize];
    let x: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load32(hi);
    os.1[i as usize] = x
}

fn sha384_init4(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
for i in 0u32..8u32
{
    let
    os:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        hash.split_at_mut(0usize);
    let hi: u64 = (&crate::hacl::hash_sha2::h384)[i as usize];
    let x: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(hi);
    os.1[i as usize] = x
}

fn sha512_init4(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
for i in 0u32..8u32
{
    let
    os:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        hash.split_at_mut(0usize);
    let hi: u64 = (&crate::hacl::hash_sha2::h512)[i as usize];
    let x: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(hi);
    os.1[i as usize] = x
}
