module Interop.X64

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module IA = Interop.Assumptions
module ST = FStar.HyperStack.ST

let wrap c args h0 #rel predict =
  let h0' = ST.get () in
  assert (mem_roots_p h0' args);
  ST.push_frame ();
  let push_h0 = ST.get () in
  B.fresh_frame_modifies h0' push_h0;
  mem_roots_p_modifies_none args h0' push_h0;
  let stack_b : lowstar_buffer ME.(TBase TUInt8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
  let alloc_push_h0 = ST.get () in
  assert (HS.fresh_frame h0 push_h0);
  mem_roots_p_modifies_none args push_h0 alloc_push_h0;
  assert (mem_roots_p alloc_push_h0 args);
  let sarg = arg_of_lb stack_b in
  all_live_cons sarg args alloc_push_h0;
  disjoint_or_eq_cons sarg args;
  disjoint_or_eq_fresh stack_b args push_h0;
  assert (mem_roots_p alloc_push_h0 (sarg::args));
  let (fuel, final_mem) =
    IA.st_put
      (fun h0' -> h0' == alloc_push_h0)
      (fun h0' ->
        let va_s0, mem_s0 =
          create_initial_trusted_state args h0' stack_b in
        let (fuel, final_mem) = predict va_s0 push_h0 alloc_push_h0 stack_b in
        assert (B.frameOf stack_b = HS.get_tip h0');
        assert (B.live h0' stack_b);
        let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
        let final_hs = Adapters.hs_of_mem final_mem in
        ((fuel, final_mem), Adapters.hs_of_mem final_mem)
      ) in
  ST.pop_frame ();
  assert (ST.equal_domains alloc_push_h0 (Adapters.hs_of_mem final_mem));
  As_lowstar_sig_ret push_h0 alloc_push_h0 stack_b fuel final_mem
