module Vale.Wrapper.X64.Fadd

open FStar.Mul
open Vale.Interop.Base
module DV = LowStar.BufferView.Down

#set-options "--z3rlimit 50"

let add_scalar_e out f1 f2 =
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview out);
  let (x, _) = Vale.Stdcalls.X64.Fadd.add_scalar_e out f1 f2 () in
  x

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fadd_e out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let (x, _) = Vale.Stdcalls.X64.Fadd.fadd_e out f1 f2 () in
  ()

#pop-options
