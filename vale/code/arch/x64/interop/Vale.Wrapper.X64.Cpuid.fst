module Vale.Wrapper.X64.Cpuid
open FStar.Mul

let check_aesni () =
  let x, _ = Vale.Stdcalls.X64.Cpuid.check_aesni () in //This is a call to the interop wrapper
  x

let check_sha () =
  let x, _ = Vale.Stdcalls.X64.Cpuid.check_sha () in //This is a call to the interop wrapper
  x

let check_adx_bmi2 () =
  let x, _ = Vale.Stdcalls.X64.Cpuid.check_adx_bmi2 () in //This is a call to the interop wrapper
  x

let check_avx () =
  let x, _ = Vale.Stdcalls.X64.Cpuid.check_avx () in //This is a call to the interop wrapper
  x

let check_avx2 () =
  let x, _ = Vale.Stdcalls.X64.Cpuid.check_avx2 () in //This is a call to the interop wrapper
  x
