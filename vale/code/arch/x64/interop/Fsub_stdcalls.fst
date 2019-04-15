module Fsub_stdcalls

open Interop.Base
module DV = LowStar.BufferView.Down

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsub out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let x, _ = Vale.Stdcalls.Fsub.fsub_ out f1 f2 () in
  ()

#pop-options
