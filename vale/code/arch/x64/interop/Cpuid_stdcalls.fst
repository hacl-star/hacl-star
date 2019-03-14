module Cpuid_stdcalls

let check_aesni () =  
  let x, _ = Vale.Stdcalls.Cpuid.check_aesni () in //This is a call to the interop wrapper
  x

let check_sha () =  
  let x, _ = Vale.Stdcalls.Cpuid.check_sha () in //This is a call to the interop wrapper
  x

let check_adx_bmi2 () =  
  let x, _ = Vale.Stdcalls.Cpuid.check_adx_bmi2 () in //This is a call to the interop wrapper
  x

let check_avx () =  
  let x, _ = Vale.Stdcalls.Cpuid.check_avx () in //This is a call to the interop wrapper
  x

let check_avx2 () =  
  let x, _ = Vale.Stdcalls.Cpuid.check_avx2 () in //This is a call to the interop wrapper
  x
