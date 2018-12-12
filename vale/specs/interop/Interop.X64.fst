module Interop.X64

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module IA = Interop.Assumptions
module ST = FStar.HyperStack.ST

let wrap c args h0 predict =
  let h0' = ST.get () in
  assert (mem_roots_p h0' args);
  ST.push_frame ();
  let h1 = ST.get () in
  B.fresh_frame_modifies h0' h1;
  mem_roots_p_modifies_none args h0' h1;
  let stack_b : lowstar_buffer ME.(TBase TUInt8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
  let h2 = ST.get () in
  assert (HS.fresh_frame h0 h1);
  mem_roots_p_modifies_none args h1 h2;
  assert (mem_roots_p h2 args);
  let sarg = arg_of_lb stack_b in
  all_live_cons sarg args h2;
  disjoint_or_eq_cons sarg args;
  disjoint_or_eq_fresh stack_b args h1;
  assert (mem_roots_p h2 (sarg::args));
  let (fuel, final_mem) =
    IA.st_put
      (fun h0' -> h0' == h2)
      (fun h0' ->
        let va_s0, mem_s0 =
          create_initial_trusted_state args h0' stack_b in
        let (fuel, final_mem) = predict va_s0 h1 h2 stack_b in
        assert (B.frameOf stack_b = HS.get_tip h0');
        assert (B.live h0' stack_b);
        let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
        ((fuel, final_mem), Adapters.hs_of_mem final_mem)
      ) in //conveniently, st_put assumes that the shape of the stack did not change
  ST.pop_frame ();
  As_lowstar_sig_ret h1 h2 stack_b fuel final_mem
