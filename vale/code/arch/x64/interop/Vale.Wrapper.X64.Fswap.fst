module Vale.Wrapper.X64.Fswap
open FStar.Mul

module DV = LowStar.BufferView.Down
open Vale.Interop.Base

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let cswap2_e bit p0 p1 =
  DV.length_eq (get_downview p0);
  DV.length_eq (get_downview p1);
  let (x, _) = Vale.Stdcalls.X64.Fswap.cswap2_e bit p0 p1 () in
  ()

#pop-options
