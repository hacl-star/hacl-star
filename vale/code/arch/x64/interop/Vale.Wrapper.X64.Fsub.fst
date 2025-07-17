module Vale.Wrapper.X64.Fsub

open FStar.Mul
open Vale.Interop.Base
module DV = LowStar.BufferView.Down

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
#set-options "--ext compat:normalizer_memo_ignore_cfg"

let fsub_e out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let (x, _) = Vale.Stdcalls.X64.Fsub.fsub_e out f1 f2 () in
  ()

#pop-options
