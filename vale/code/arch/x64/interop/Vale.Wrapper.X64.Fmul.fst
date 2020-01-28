module Vale.Wrapper.X64.Fmul
open FStar.Mul

module DV = LowStar.BufferView.Down
open Vale.Interop.Base

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let fmul_e tmp f1 out f2 =
  DV.length_eq (get_downview tmp);
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  Vale.AsLowStar.MemoryHelpers.as_vale_buffer_len #TUInt64 #TUInt64 tmp;
  Vale.AsLowStar.MemoryHelpers.as_vale_buffer_len #TUInt64 #TUInt64 out;
  let (x, _) = Vale.Stdcalls.X64.Fmul.fmul_e tmp f1 out f2 () in
  ()

#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 400 --using_facts_from '* -Vale.Interop.*'"

let fmul2_e tmp f1 out f2 =
  DV.length_eq (get_downview tmp);
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let (x, _) = Vale.Stdcalls.X64.Fmul.fmul2_e tmp f1 out f2 () in
  ()

#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let fmul_scalar_e out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  let (x, _) = Vale.Stdcalls.X64.Fmul.fmul_scalar_e out f1 f2 () in
  ()

#pop-options
