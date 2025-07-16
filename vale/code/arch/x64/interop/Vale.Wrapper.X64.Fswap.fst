module Vale.Wrapper.X64.Fswap
open FStar.Mul

module DV = LowStar.BufferView.Down
open Vale.Interop.Base

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
#set-options "--ext compat:normalizer_memo_ignore_cfg"

let cswap2_e bit p0 p1 =
  DV.length_eq (get_downview p0);
  DV.length_eq (get_downview p1);
  let (x, _) = Vale.Stdcalls.X64.Fswap.cswap2_e bit p0 p1 () in
  ()

#pop-options
