module Fswap_stdcalls

module DV = LowStar.BufferView.Down
open Interop.Base

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let cswap2 p0 p1 bit =
  DV.length_eq (get_downview p0);
  DV.length_eq (get_downview p1);
  let x, _ = Vale.Stdcalls.Fswap.cswap2 p0 p1 bit () in
  ()

#pop-options
