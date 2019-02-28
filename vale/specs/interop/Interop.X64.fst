module Interop.X64

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module HS = FStar.HyperStack
module TS = X64.Taint_Semantics_s
module IA = Interop.Assumptions
module ST = FStar.HyperStack.ST

let wrap_variadic c n arg_reg regs_modified xmms_modified down_mem num_b8_slots args #pre_rel #post_rel predict =
  let h0 = ST.get () in
  let h0' = h0 in
  assert (mem_roots_p h0' args);
  ST.push_frame ();
  let push_h0 = ST.get () in
  B.fresh_frame_modifies h0' push_h0;
  mem_roots_p_modifies_none args h0' push_h0;
  let stack_b = B.alloca (UInt64.uint_to_t 0) (UInt32.uint_to_t (num_b8_slots/8)) in
  DV.length_eq (get_downview stack_b);
  assert_norm ((num_b8_slots / 8) * 8 == num_b8_slots);
  let stack_b : stack_buffer num_b8_slots = stack_b in
  let alloc_push_h0 = ST.get () in
  assert (HS.fresh_frame h0 push_h0);
  mem_roots_p_modifies_none args push_h0 alloc_push_h0;
  assert (mem_roots_p alloc_push_h0 args);
  let sarg = arg_of_sb stack_b in
  all_live_cons sarg args alloc_push_h0;
  disjoint_or_eq_cons sarg args;
  disjoint_or_eq_fresh stack_b args push_h0;
  assert (mem_roots_p alloc_push_h0 (sarg::args));
  let rax, fuel, final_mem =
    IA.st_put
      #(UInt64.t & nat & mem)
      (fun h0' -> h0' == alloc_push_h0)
      (fun h0' ->
        let va_s0, mem_s0 =
          create_initial_trusted_state n arg_reg num_b8_slots args down_mem h0' stack_b in
        let (rax, fuel, final_mem) = predict h0 va_s0 push_h0 alloc_push_h0 stack_b in
        assert (B.frameOf stack_b = HS.get_tip h0');
        assert (B.live h0' stack_b);
        let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
        let final_hs = hs_of_mem final_mem in
        (rax, fuel, final_mem), hs_of_mem final_mem
      ) in
  ST.pop_frame ();
  assert (ST.equal_domains alloc_push_h0 (hs_of_mem final_mem));
  rax, Ghost.hide (As_lowstar_sig_ret n num_b8_slots args push_h0 alloc_push_h0 stack_b fuel final_mem)

let rec wrap_aux
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)    
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (dom:list td)
    (args:list arg{arity_ok_2 n dom args})
    (pre_rel:rel_gen_t n c dom args (prediction_pre_rel_t n c))
    (post_rel:rel_gen_t n c dom args (prediction_post_rel_t n c num_b8_slots))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom args pre_rel post_rel)
  : as_lowstar_sig_t n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom args pre_rel post_rel predict
  = match dom with
    | [] ->
      let f () :
        FStar.HyperStack.ST.Stack als_ret
           (requires fun h0 ->
             mem_roots_p h0 args /\ elim_rel_gen_t_nil pre_rel h0)
           (ensures fun h0 ret h1 ->
             as_lowstar_sig_post n arg_reg regs_modified xmms_modified down_mem c num_b8_slots args h0 #pre_rel #post_rel (elim_predict_t_nil predict) ret h1) =
        wrap_variadic c n arg_reg regs_modified xmms_modified down_mem num_b8_slots args (elim_predict_t_nil predict)
      in
      f <: as_lowstar_sig_t n arg_reg regs_modified xmms_modified down_mem c num_b8_slots [] args pre_rel post_rel predict

    | hd::tl ->
      fun (x:td_as_type hd) ->
      wrap_aux n arg_reg regs_modified xmms_modified down_mem c num_b8_slots tl
        (x ++ args)
        (elim_rel_gen_t_cons hd tl pre_rel x)
        (elim_rel_gen_t_cons hd tl post_rel x)
        (elim_predict_t_cons hd tl predict x)

let wrap n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom #pre_rel #post_rel predict =
  wrap_aux n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom [] pre_rel post_rel predict

let rec wrap_aux_weak
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (dom:list td)
    (args:list arg{arity_ok_2 n dom args})
    (pre_rel:rel_gen_t n c dom args (prediction_pre_rel_t n c))
    (post_rel:rel_gen_t n c dom args (prediction_post_rel_t n c num_b8_slots))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom args pre_rel post_rel)
  : as_lowstar_sig_t_weak n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom args pre_rel post_rel predict
  = match dom with
    | [] ->
      let f () 
        : FStar.HyperStack.ST.Stack als_ret
           (requires fun h0 ->
             mem_roots_p h0 args /\ elim_rel_gen_t_nil pre_rel h0)
           (ensures fun h0 ret h1 ->
             as_lowstar_sig_post_weak
               n arg_reg regs_modified xmms_modified
               down_mem c num_b8_slots args h0 
               #pre_rel #post_rel (elim_predict_t_nil predict) ret h1)
        = wrap_variadic c n arg_reg regs_modified xmms_modified down_mem num_b8_slots args (elim_predict_t_nil predict)
      in
      f <: as_lowstar_sig_t_weak n arg_reg regs_modified xmms_modified down_mem c num_b8_slots [] args pre_rel post_rel predict

    | hd::tl ->
      fun (x:td_as_type hd) ->
      wrap_aux_weak n arg_reg regs_modified xmms_modified down_mem c num_b8_slots tl
        (x ++ args)
        (elim_rel_gen_t_cons hd tl pre_rel x)
        (elim_rel_gen_t_cons hd tl post_rel x)
        (elim_predict_t_cons hd tl predict x)

let wrap_weak n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom #pre_rel #post_rel predict =
  wrap_aux_weak n arg_reg regs_modified xmms_modified down_mem c num_b8_slots dom [] pre_rel post_rel predict
