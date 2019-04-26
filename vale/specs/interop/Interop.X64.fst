module Interop.X64

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module HS = FStar.HyperStack
module TS = X64.Taint_Semantics_s
module IA = Interop.Assumptions
module ST = FStar.HyperStack.ST

let wrap_variadic c n arg_reg regs_modified xmms_modified down_mem args #pre_rel #post_rel predict =
  let h0 = ST.get () in
  assert (mem_roots_p h0 args);
  let rax, fuel, final_mem =
    IA.st_put
      #(UInt64.t & nat & mem)
      (fun h0' -> h0' == h0)
      (fun h0' ->
        let va_s0, mem_s0 =
          create_initial_trusted_state n arg_reg args down_mem h0' in
        let (rax, fuel, final_mem) = predict h0 va_s0 in
        let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
        let final_hs = hs_of_mem final_mem in
        (rax, fuel, final_mem), hs_of_mem final_mem
      ) in
  assert (ST.equal_domains h0 (hs_of_mem final_mem));
  rax, Ghost.hide (As_lowstar_sig_ret n args fuel final_mem)

let rec wrap_aux
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)    
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (dom:list td)
    (args:list arg{List.length args + List.length dom <= 20})
    (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
    (post_rel:rel_gen_t c dom args (prediction_post_rel_t c))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel)
  : as_lowstar_sig_t n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel predict
  = match dom with
    | [] ->
      let f () :
        FStar.HyperStack.ST.Stack als_ret
           (requires fun h0 ->
             mem_roots_p h0 args /\ elim_rel_gen_t_nil pre_rel h0)
           (ensures fun h0 ret h1 ->
             as_lowstar_sig_post n arg_reg regs_modified xmms_modified down_mem c args h0 #pre_rel #post_rel (elim_predict_t_nil predict) ret h1) =
        wrap_variadic c n arg_reg regs_modified xmms_modified down_mem args (elim_predict_t_nil predict)
      in
      f <: as_lowstar_sig_t n arg_reg regs_modified xmms_modified down_mem c [] args pre_rel post_rel predict

    | hd::tl ->
      fun (x:td_as_type hd) ->
      wrap_aux n arg_reg regs_modified xmms_modified down_mem c tl
        (x ++ args)
        (elim_rel_gen_t_cons hd tl pre_rel x)
        (elim_rel_gen_t_cons hd tl post_rel x)
        (elim_predict_t_cons hd tl predict x)

let wrap' n arg_reg regs_modified xmms_modified down_mem c dom #pre_rel #post_rel predict =
  wrap_aux n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel predict

let rec wrap_aux_weak
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (dom:list td)
    (args:list arg{List.length args + List.length dom <= 20})
    (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
    (post_rel:rel_gen_t c dom args (prediction_post_rel_t c))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel)
  : as_lowstar_sig_t_weak' n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel predict
  = match dom with
    | [] ->
      let f () 
        : FStar.HyperStack.ST.Stack als_ret
           (requires fun h0 ->
             mem_roots_p h0 args /\ elim_rel_gen_t_nil pre_rel h0)
           (ensures fun h0 ret h1 ->
             as_lowstar_sig_post_weak
               n arg_reg regs_modified xmms_modified
               down_mem c args h0 
               #pre_rel #post_rel (elim_predict_t_nil predict) ret h1)
        = wrap_variadic c n arg_reg regs_modified xmms_modified down_mem args (elim_predict_t_nil predict)
      in
      f <: as_lowstar_sig_t_weak' n arg_reg regs_modified xmms_modified down_mem c [] args pre_rel post_rel predict

    | hd::tl ->
      fun (x:td_as_type hd) ->
      wrap_aux_weak n arg_reg regs_modified xmms_modified down_mem c tl
        (x ++ args)
        (elim_rel_gen_t_cons hd tl pre_rel x)
        (elim_rel_gen_t_cons hd tl post_rel x)
        (elim_predict_t_cons hd tl predict x)

let wrap_weak' n arg_reg regs_modified xmms_modified down_mem c dom #pre_rel #post_rel predict =
  wrap_aux_weak n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel predict

let wrap_weak n = wrap_weak' n
