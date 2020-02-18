module Vale.Wrapper.X64.Fsqr
open FStar.Mul

module DV = LowStar.BufferView.Down
open Vale.Interop.Base

open Vale.AsLowStar.MemoryHelpers

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsqr_e tmp f1 out =
  DV.length_eq (get_downview tmp);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview out);
  as_vale_buffer_len #TUInt64 #TUInt64 tmp;
  as_vale_buffer_len #TUInt64 #TUInt64 f1;
  as_vale_buffer_len #TUInt64 #TUInt64 out;
  let (x, _) = Vale.Stdcalls.X64.Fsqr.fsqr_e tmp f1 out () in
  ()

#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsqr2_e tmp f1 out =
  DV.length_eq (get_downview tmp);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview out);
  let (x, _) = Vale.Stdcalls.X64.Fsqr.fsqr2_e tmp f1 out () in
  ()

#pop-options
