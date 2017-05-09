module Chacha20.Vec128


open FStar.Buffer


#reset-options "--max_fuel 0 --z3rlimit 20"


open Hacl.Impl.Chacha20.Vec128.State
open Hacl.Impl.Chacha20.Vec128

let chacha20 output plain len k n ctr =
  push_frame();
  let st = state_alloc () in
  let log = init st k n ctr in
  chacha20_counter_mode log output plain len st;
  pop_frame()
