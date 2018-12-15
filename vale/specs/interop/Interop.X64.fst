module Interop.X64

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module IA = Interop.Assumptions
module ST = FStar.HyperStack.ST

let wrap_variadic c args #pre_rel #post_rel predict =
  let h0 = ST.get () in
  let h0' = h0 in
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
        let (fuel, final_mem) = predict h0 va_s0 push_h0 alloc_push_h0 stack_b in
        assert (B.frameOf stack_b = HS.get_tip h0');
        assert (B.live h0' stack_b);
        let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
        let final_hs = Adapters.hs_of_mem final_mem in
        ((fuel, final_mem), Adapters.hs_of_mem final_mem)
      ) in
  ST.pop_frame ();
  assert (ST.equal_domains alloc_push_h0 (Adapters.hs_of_mem final_mem));
  As_lowstar_sig_ret push_h0 alloc_push_h0 stack_b fuel final_mem

let rec wrap_aux
    (c:TS.tainted_code)
    (dom:list td)
    (args:list arg{List.length dom + List.length args < max_arity})
    (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
    (post_rel:rel_gen_t c dom args (prediction_post_rel_t c))
    (predict:prediction_t c dom args pre_rel post_rel)
  : as_lowstar_sig_t c dom args pre_rel post_rel predict
  = match dom with
    | [] ->
      let f () :
        FStar.HyperStack.ST.Stack (as_lowstar_sig_ret args)
           (requires (fun h0 -> mem_roots_p h0 args /\ elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 -> as_lowstar_sig_post c args h0 #pre_rel #post_rel (elim_predict_t_nil predict) ret h1) =
        wrap_variadic c args (elim_predict_t_nil predict)
      in
      f <: as_lowstar_sig_t c [] args pre_rel post_rel predict

    | hd::tl ->
      fun (x:td_as_type hd) ->
      wrap_aux c tl
        (x ++ args)
        (elim_rel_gen_t_cons hd tl pre_rel x)
        (elim_rel_gen_t_cons hd tl post_rel x)
        (elim_predict_t_cons hd tl predict x)

let wrap c dom #pre_rel #post_rel predict = wrap_aux c dom [] pre_rel post_rel predict
