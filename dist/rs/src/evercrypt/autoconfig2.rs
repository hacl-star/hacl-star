const cpu_has_shaext: [bool; 1] = [falsebool];

const cpu_has_aesni: [bool; 1] = [falsebool];

const cpu_has_pclmulqdq: [bool; 1] = [falsebool];

const cpu_has_avx2: [bool; 1] = [falsebool];

const cpu_has_avx: [bool; 1] = [falsebool];

const cpu_has_bmi2: [bool; 1] = [falsebool];

const cpu_has_adx: [bool; 1] = [falsebool];

const cpu_has_sse: [bool; 1] = [falsebool];

const cpu_has_movbe: [bool; 1] = [falsebool];

const cpu_has_rdrand: [bool; 1] = [falsebool];

const cpu_has_avx512: [bool; 1] = [falsebool];

pub fn has_shaext(uu___: ()) -> bool { (&mut cpu_has_shaext)[0usize] }

pub fn has_aesni(uu___: ()) -> bool { (&mut cpu_has_aesni)[0usize] }

pub fn has_pclmulqdq(uu___: ()) -> bool { (&mut cpu_has_pclmulqdq)[0usize] }

pub fn has_avx2(uu___: ()) -> bool { (&mut cpu_has_avx2)[0usize] }

pub fn has_avx(uu___: ()) -> bool { (&mut cpu_has_avx)[0usize] }

pub fn has_bmi2(uu___: ()) -> bool { (&mut cpu_has_bmi2)[0usize] }

pub fn has_adx(uu___: ()) -> bool { (&mut cpu_has_adx)[0usize] }

pub fn has_sse(uu___: ()) -> bool { (&mut cpu_has_sse)[0usize] }

pub fn has_movbe(uu___: ()) -> bool { (&mut cpu_has_movbe)[0usize] }

pub fn has_rdrand(uu___: ()) -> bool { (&mut cpu_has_rdrand)[0usize] }

pub fn has_avx512(uu___: ()) -> bool { (&mut cpu_has_avx512)[0usize] }

pub fn recall(uu___: ()) -> () { () }

pub fn init(uu___: ()) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        if crate::vale::stdcalls_x64_cpuid::check_aesni(()) != 0u64
        {
            (&mut cpu_has_aesni)[0usize] = truebool;
            (&mut cpu_has_pclmulqdq)[0usize] = truebool
        };
        if crate::vale::stdcalls_x64_cpuid::check_sha(()) != 0u64
        { (&mut cpu_has_shaext)[0usize] = truebool };
        if crate::vale::stdcalls_x64_cpuid::check_adx_bmi2(()) != 0u64
        {
            (&mut cpu_has_bmi2)[0usize] = truebool;
            (&mut cpu_has_adx)[0usize] = truebool
        };
        if crate::vale::stdcalls_x64_cpuid::check_avx(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_osxsave(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_avx_xcr0(()) != 0u64
        { (&mut cpu_has_avx)[0usize] = truebool };
        if crate::vale::stdcalls_x64_cpuid::check_avx2(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_osxsave(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_avx_xcr0(()) != 0u64
        { (&mut cpu_has_avx2)[0usize] = truebool };
        if crate::vale::stdcalls_x64_cpuid::check_sse(()) != 0u64
        { (&mut cpu_has_sse)[0usize] = truebool };
        if crate::vale::stdcalls_x64_cpuid::check_movbe(()) != 0u64
        { (&mut cpu_has_movbe)[0usize] = truebool };
        if crate::vale::stdcalls_x64_cpuid::check_rdrand(()) != 0u64
        { (&mut cpu_has_rdrand)[0usize] = truebool };
        if crate::vale::stdcalls_x64_cpuid::check_avx512(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_osxsave(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_avx_xcr0(()) != 0u64
        if crate::vale::stdcalls_x64_cpuid::check_avx512_xcr0(()) != 0u64
        { (&mut cpu_has_avx512)[0usize] = truebool }
    }
}

pub fn disable_avx2(uu___: ()) -> () { (&mut cpu_has_avx2)[0usize] = falsebool }

pub fn disable_avx(uu___: ()) -> () { (&mut cpu_has_avx)[0usize] = falsebool }

pub fn disable_bmi2(uu___: ()) -> () { (&mut cpu_has_bmi2)[0usize] = falsebool }

pub fn disable_adx(uu___: ()) -> () { (&mut cpu_has_adx)[0usize] = falsebool }

pub fn disable_shaext(uu___: ()) -> () { (&mut cpu_has_shaext)[0usize] = falsebool }

pub fn disable_aesni(uu___: ()) -> () { (&mut cpu_has_aesni)[0usize] = falsebool }

pub fn disable_pclmulqdq(uu___: ()) -> () { (&mut cpu_has_pclmulqdq)[0usize] = falsebool }

pub fn disable_sse(uu___: ()) -> () { (&mut cpu_has_sse)[0usize] = falsebool }

pub fn disable_movbe(uu___: ()) -> () { (&mut cpu_has_movbe)[0usize] = falsebool }

pub fn disable_rdrand(uu___: ()) -> () { (&mut cpu_has_rdrand)[0usize] = falsebool }

pub fn disable_avx512(uu___: ()) -> () { (&mut cpu_has_avx512)[0usize] = falsebool }

pub fn has_vec128(uu___: ()) -> bool
{
    let avx: bool = has_avx(());
    let other: bool = crate::evercrypt::targetconfig::has_vec128_not_avx(());
    avx || other
}

pub fn has_vec256(uu___: ()) -> bool
{
    let avx2: bool = has_avx2(());
    let other: bool = crate::evercrypt::targetconfig::has_vec256_not_avx2(());
    avx2 || other
}
