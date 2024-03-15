#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

const cpu_has_shaext: [bool; 1] = [false];

const cpu_has_aesni: [bool; 1] = [false];

const cpu_has_pclmulqdq: [bool; 1] = [false];

const cpu_has_avx2: [bool; 1] = [false];

const cpu_has_avx: [bool; 1] = [false];

const cpu_has_bmi2: [bool; 1] = [false];

const cpu_has_adx: [bool; 1] = [false];

const cpu_has_sse: [bool; 1] = [false];

const cpu_has_movbe: [bool; 1] = [false];

const cpu_has_rdrand: [bool; 1] = [false];

const cpu_has_avx512: [bool; 1] = [false];

pub fn has_shaext() -> bool { (&mut cpu_has_shaext)[0usize] }

pub fn has_aesni() -> bool { (&mut cpu_has_aesni)[0usize] }

pub fn has_pclmulqdq() -> bool { (&mut cpu_has_pclmulqdq)[0usize] }

pub fn has_avx2() -> bool { (&mut cpu_has_avx2)[0usize] }

pub fn has_avx() -> bool { (&mut cpu_has_avx)[0usize] }

pub fn has_bmi2() -> bool { (&mut cpu_has_bmi2)[0usize] }

pub fn has_adx() -> bool { (&mut cpu_has_adx)[0usize] }

pub fn has_sse() -> bool { (&mut cpu_has_sse)[0usize] }

pub fn has_movbe() -> bool { (&mut cpu_has_movbe)[0usize] }

pub fn has_rdrand() -> bool { (&mut cpu_has_rdrand)[0usize] }

pub fn has_avx512() -> bool { (&mut cpu_has_avx512)[0usize] }

pub fn recall() -> () { () }

pub fn init() -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        if crate::vale::stdcalls_x64_cpuid::check_aesni() != 0u64
        {
            (&mut cpu_has_aesni)[0usize] = true;
            (&mut cpu_has_pclmulqdq)[0usize] = true
        };
        if crate::vale::stdcalls_x64_cpuid::check_sha() != 0u64
        { (&mut cpu_has_shaext)[0usize] = true };
        if crate::vale::stdcalls_x64_cpuid::check_adx_bmi2() != 0u64
        {
            (&mut cpu_has_bmi2)[0usize] = true;
            (&mut cpu_has_adx)[0usize] = true
        };
        if crate::vale::stdcalls_x64_cpuid::check_avx() != 0u64
        {
            if crate::vale::stdcalls_x64_cpuid::check_osxsave() != 0u64
            {
                if crate::vale::stdcalls_x64_cpuid::check_avx_xcr0() != 0u64
                { (&mut cpu_has_avx)[0usize] = true }
            }
        };
        if crate::vale::stdcalls_x64_cpuid::check_avx2() != 0u64
        {
            if crate::vale::stdcalls_x64_cpuid::check_osxsave() != 0u64
            {
                if crate::vale::stdcalls_x64_cpuid::check_avx_xcr0() != 0u64
                { (&mut cpu_has_avx2)[0usize] = true }
            }
        };
        if crate::vale::stdcalls_x64_cpuid::check_sse() != 0u64
        { (&mut cpu_has_sse)[0usize] = true };
        if crate::vale::stdcalls_x64_cpuid::check_movbe() != 0u64
        { (&mut cpu_has_movbe)[0usize] = true };
        if crate::vale::stdcalls_x64_cpuid::check_rdrand() != 0u64
        { (&mut cpu_has_rdrand)[0usize] = true };
        if crate::vale::stdcalls_x64_cpuid::check_avx512() != 0u64
        {
            if crate::vale::stdcalls_x64_cpuid::check_osxsave() != 0u64
            {
                if crate::vale::stdcalls_x64_cpuid::check_avx_xcr0() != 0u64
                {
                    if crate::vale::stdcalls_x64_cpuid::check_avx512_xcr0() != 0u64
                    { (&mut cpu_has_avx512)[0usize] = true }
                }
            }
        }
    }
}

pub type disabler = () ();

pub fn disable_avx2() -> () { (&mut cpu_has_avx2)[0usize] = false }

pub fn disable_avx() -> () { (&mut cpu_has_avx)[0usize] = false }

pub fn disable_bmi2() -> () { (&mut cpu_has_bmi2)[0usize] = false }

pub fn disable_adx() -> () { (&mut cpu_has_adx)[0usize] = false }

pub fn disable_shaext() -> () { (&mut cpu_has_shaext)[0usize] = false }

pub fn disable_aesni() -> () { (&mut cpu_has_aesni)[0usize] = false }

pub fn disable_pclmulqdq() -> () { (&mut cpu_has_pclmulqdq)[0usize] = false }

pub fn disable_sse() -> () { (&mut cpu_has_sse)[0usize] = false }

pub fn disable_movbe() -> () { (&mut cpu_has_movbe)[0usize] = false }

pub fn disable_rdrand() -> () { (&mut cpu_has_rdrand)[0usize] = false }

pub fn disable_avx512() -> () { (&mut cpu_has_avx512)[0usize] = false }

pub fn has_vec128() -> bool
{
    let avx: bool = has_avx();
    let other: bool = crate::evercrypt::targetconfig::has_vec128_not_avx();
    avx || other
}

pub fn has_vec256() -> bool
{
    let avx2: bool = has_avx2();
    let other: bool = crate::evercrypt::targetconfig::has_vec256_not_avx2();
    avx2 || other
}
