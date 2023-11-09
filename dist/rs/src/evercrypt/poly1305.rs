fn poly1305_vale(dst: &mut [u8], src: &mut [u8], len: u32, key: &mut [u8]) -> ()
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    crate::lowstar::ignore::ignore::<&mut [u8]>(src);
    crate::lowstar::ignore::ignore::<u32>(len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(key);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let mut ctx: [u8; 192] = [0u8; 192usize];
        ((&mut ctx)[24usize..24usize + 32usize]).copy_from_slice(&key[0usize..0usize + 32usize]);
        let n_blocks: u32 = len.wrapping_div(16u32);
        let n_extra: u32 = len.wrapping_rem(16u32);
        if n_extra == 0u32
        {
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_poly::x64_poly1305(&mut ctx, src, len as u64, 1u64)
            )
        }
        else
        {
            let mut tmp: [u8; 16] = [0u8; 16usize];
            let len16: u32 = n_blocks.wrapping_mul(16u32);
            let src16: (&mut [u8], &mut [u8]) = src.split_at_mut(0usize);
            ((&mut tmp)[0usize..0usize + n_extra as usize]).copy_from_slice(
                &src16.1[len16 as usize..len16 as usize + n_extra as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_poly::x64_poly1305(&mut ctx, src16.1, len16 as u64, 0u64)
            );
            ((&mut ctx)[24usize..24usize + 32usize]).copy_from_slice(&key[0usize..0usize + 32usize]);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_poly::x64_poly1305(
                    &mut ctx,
                    &mut tmp,
                    n_extra as u64,
                    1u64
                )
            )
        };
        (dst[0usize..0usize + 16usize]).copy_from_slice(&(&mut ctx)[0usize..0usize + 16usize])
    }
}
