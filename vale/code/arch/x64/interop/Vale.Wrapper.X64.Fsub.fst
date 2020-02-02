module Vale.Wrapper.X64.Fsub

open FStar.Mul
open Vale.Interop.Base
module DV = LowStar.BufferView.Down

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let fsub_e out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let (x, _) = Vale.Stdcalls.X64.Fsub.fsub_e out f1 f2 () in
  ()

#pop-options
