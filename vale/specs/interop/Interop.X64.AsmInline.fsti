module Interop.X64.AsmInline

open FStar.Mul
open Interop.Base
module MS = X64.Machine_s
module TS = X64.Taint_Semantics_s
module BS = X64.Bytes_Semantics_s
module B = LowStar.Buffer
module HS = FStar.HyperStack
module IX64 = Interop.X64
module IA = Interop.Assumptions
module List = FStar.List.Tot

let inline_arg = td & MS.reg & string


[@__reduce__]
let get_inline_td x = let a, _, _ = x in a
[@__reduce__]
let get_inline_reg x = let _, r, _ = x in r
[@__reduce__]
let get_inline_name x = let _, _, s = x in s
[@__reduce__]
let valid_inline_args' (a:inline_arg) (b:inline_arg) =
  get_inline_reg a =!= get_inline_reg b /\ get_inline_name a =!= get_inline_name b
[@__reduce__]
let valid_inline_args (l:list inline_arg) =
  BigOps.pairwise_and' valid_inline_args' l
[@__reduce__]
let inline_args = l:list inline_arg{valid_inline_args l}
[@__reduce__]
let valid_retname (so:option string) (l:inline_args) =
  None? so \/ BigOps.big_and' (fun x -> Some?.v so =!= get_inline_name x) l

type inline_input = 
  | AsmInline: args:inline_args -> 
               mods:list MS.reg -> 
               ret_val:option string{valid_retname ret_val args} -> 
               inline_input

let inl_arg = t:inline_arg & td_as_type (get_inline_td t)

[@__reduce__]
let extract_arg (x:inl_arg) : arg =
  let (| td, arg |) = x in
  (| get_inline_td td, arg |)

[@__reduce__]
let rec extract_args (l:list inl_arg) : list arg =
  match l with
  | [] -> []
  | hd::tl -> extract_arg hd :: extract_args tl

let upd_reg (regs:IX64.registers) (i:MS.reg) (v:_) : IX64.registers =
    fun (r:MS.reg) ->
      if r = i then v else regs r

let update_regs (x:inl_arg) (regs:IX64.registers) : GTot IX64.registers =
    let (| td, _ |) = x in
    upd_reg regs (get_inline_reg td) (IX64.arg_as_nat64 (extract_arg x))

[@__reduce__]
let rec register_of_args (args:list inl_arg)
                         (regs:IX64.registers) : GTot IX64.registers =
    match args with
    | [] -> regs
    | hd::tl ->
      update_regs hd (register_of_args tl regs)

////////////////////////////////////////////////////////////////////////////////
// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let state_builder_t (num_b8_slots:IX64.max_slots) (args:list inl_arg) (codom:Type) =
    h0:HS.mem ->
    stack:IX64.stack_buffer num_b8_slots{mem_roots_p h0 (arg_of_sb stack::(extract_args args))} ->
    GTot codom

let create_initial_inline_trusted_state
      (num_b8_slots:IX64.max_slots)
      (args:list inl_arg)
      (down_mem: down_mem_t)
  : state_builder_t num_b8_slots args (TS.traceState & mem) =
  fun h0 stack ->
    let open MS in
    let regs = register_of_args args IA.init_regs in
    let regs = FunctionalExtensionality.on reg (IX64.regs_with_stack regs stack) in
    let xmms = FunctionalExtensionality.on xmm IA.init_xmms in
    let args = arg_of_sb stack::(extract_args args) in
    liveness_disjointness args h0;
    let mem:mem = mk_mem args h0 in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = IA.init_flags;
      BS.mem = down_mem mem
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = create_memtaint mem (args_b8 args) (IX64.mk_taint args IX64.init_taint)
    },
    mem

////////////////////////////////////////////////////////////////////////////////
let inline_prediction_pre_rel_t (c:TS.tainted_code) (args:list inl_arg) =
    h0:mem_roots (extract_args args) ->
    prop

let inline_prediction_post_rel_t (c:TS.tainted_code) (num_b8_slots:IX64.max_slots) (args:list inl_arg) =
    h0:mem_roots (extract_args args) ->
    s0:TS.traceState ->
    push_h0:mem_roots (extract_args args) ->
    alloc_push_h0:mem_roots (extract_args args) ->
    b:IX64.stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::(extract_args args))} ->
    (UInt64.t & nat & mem) ->
    sn:TS.traceState ->
    prop

[@__reduce__]
let inline_prediction_pre
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (args:list inl_arg)
    (pre_rel: inline_prediction_pre_rel_t c args)
    (h0:mem_roots (extract_args args))
    (s0:TS.traceState)
    (push_h0:mem_roots (extract_args args))
    (alloc_push_h0:mem_roots (extract_args args))
    (b:IX64.stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::(extract_args args))})
    =
  pre_rel h0 /\
  HS.fresh_frame h0 push_h0 /\
  B.modifies B.loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  s0 == fst (create_initial_inline_trusted_state num_b8_slots args down_mem alloc_push_h0 b)

[@__reduce__]
let inline_prediction_post
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (args:list inl_arg)
    (post_rel: inline_prediction_post_rel_t c num_b8_slots args)
    (h0:mem_roots (extract_args args))
    (s0:TS.traceState)
    (push_h0:mem_roots (extract_args args))
    (alloc_push_h0:mem_roots (extract_args args))
    (sb:IX64.stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb sb::(extract_args args))})
    (rax_fuel_mem:(UInt64.t & nat & mem)) =
  let s_args = arg_of_sb sb :: (extract_args args) in
  let rax, fuel, final_mem = rax_fuel_mem in
  Some? (TS.taint_eval_code c fuel s0) /\ (
    let s1 = Some?.v (TS.taint_eval_code c fuel s0) in
    let h1 = hs_of_mem final_mem in
    FStar.HyperStack.ST.equal_domains alloc_push_h0 h1 /\
    B.modifies (loc_modified_args s_args) alloc_push_h0 h1 /\
    mem_roots_p h1 s_args /\
    down_mem (mk_mem s_args h1) == s1.TS.state.BS.mem /\
    // TODO: Add check for non-modified buffers here
//    calling_conventions s0 s1 /\
    rax == IX64.return_val s1 /\
    post_rel h0 s0 push_h0 alloc_push_h0 sb rax_fuel_mem s1
  )

let inline_prediction
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (args:list inl_arg)
    (pre_rel:inline_prediction_pre_rel_t c args)
    (post_rel:inline_prediction_post_rel_t c num_b8_slots args) =
  h0:mem_roots (extract_args args){pre_rel h0} ->
  s0:TS.traceState ->
  push_h0:mem_roots (extract_args args) ->
  alloc_push_h0:mem_roots (extract_args args) ->
  b:IX64.stack_buffer num_b8_slots{mem_roots_p h0 (extract_args args) /\ mem_roots_p alloc_push_h0 (arg_of_sb b::(extract_args args))} ->
  Ghost (UInt64.t & nat & mem)
    (requires inline_prediction_pre down_mem c num_b8_slots args pre_rel h0 s0 push_h0 alloc_push_h0 b)
    (ensures inline_prediction_post down_mem c num_b8_slots args post_rel h0 s0 push_h0 alloc_push_h0 b)

noeq
type inline_as_lowstar_sig_ret =
  | As_lowstar_sig_ret :
      num_b8_slots:IX64.max_slots ->
      args:list inl_arg ->
      push_h0:mem_roots (extract_args args) ->
      alloc_push_h0:mem_roots (extract_args args) ->
      b:IX64.stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::(extract_args args))} ->
      fuel:nat ->
      final_mem:mem ->
      inline_as_lowstar_sig_ret

let inline_als_ret = UInt64.t & Ghost.erased inline_as_lowstar_sig_ret

[@__reduce__]
let inline_as_lowstar_sig_post
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (args:list inl_arg)
    (h0:mem_roots (extract_args args))
    (#pre_rel:_)
    (#post_rel: _)
    (predict:inline_prediction down_mem c num_b8_slots args pre_rel post_rel)
    (ret:inline_als_ret)
    (h1:HS.mem) =
  (* write it this way to be reduction friendly *)
  let rax = fst ret in
  let ret = Ghost.reveal (snd ret) in
  num_b8_slots == As_lowstar_sig_ret?.num_b8_slots ret /\
  args == As_lowstar_sig_ret?.args ret /\
 (let push_h0 = As_lowstar_sig_ret?.push_h0 ret in
  let alloc_push_h0 = As_lowstar_sig_ret?.alloc_push_h0 ret in
  let b = As_lowstar_sig_ret?.b ret in
  let fuel = As_lowstar_sig_ret?.fuel ret in
  let final_mem = As_lowstar_sig_ret?.final_mem ret in
  let s0 = fst (create_initial_inline_trusted_state num_b8_slots args down_mem alloc_push_h0 b) in
  let pre_pop = hs_of_mem final_mem in
  inline_prediction_pre down_mem c num_b8_slots args pre_rel h0 s0 push_h0 alloc_push_h0 b /\
  (rax, fuel, final_mem) == predict h0 s0 push_h0 alloc_push_h0 b /\
  inline_prediction_post down_mem c num_b8_slots args post_rel h0 s0 push_h0 alloc_push_h0 b (rax, fuel, final_mem) /\
  FStar.HyperStack.ST.equal_domains alloc_push_h0 pre_pop /\
  HS.poppable pre_pop /\
  h1 == HS.pop pre_pop)

[@__reduce__]
let inline_as_lowstar_sig_post_weak
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (args:list inl_arg)
    (h0:mem_roots (extract_args args))
    (#pre_rel:_)
    (#post_rel: _)
    (predict:inline_prediction down_mem c num_b8_slots args pre_rel post_rel)
    (ret:inline_als_ret)
    (h1:HS.mem) =
  (* write it this way to be reduction friendly *)
  let rax = fst ret in
  let ret = Ghost.reveal (snd ret) in
  num_b8_slots == As_lowstar_sig_ret?.num_b8_slots ret /\
  args == As_lowstar_sig_ret?.args ret /\
 (let push_h0 = As_lowstar_sig_ret?.push_h0 ret in
  let alloc_push_h0 = As_lowstar_sig_ret?.alloc_push_h0 ret in
  let b = As_lowstar_sig_ret?.b ret in
  let fuel = As_lowstar_sig_ret?.fuel ret in
  let final_mem = As_lowstar_sig_ret?.final_mem ret in
  let s0 = fst (create_initial_inline_trusted_state num_b8_slots args down_mem alloc_push_h0 b) in
  let pre_pop = hs_of_mem final_mem in
  (exists fuel
     final_mem
     s1.
     let pre_pop = hs_of_mem final_mem in
     HS.poppable pre_pop /\
     h1 == HS.pop pre_pop /\
     rax == IX64.return_val s1 /\
     post_rel h0 s0 push_h0 alloc_push_h0 b (IX64.return_val s1, fuel, final_mem) s1))

[@__reduce__]
let inline_as_lowstar_sig (c:TS.tainted_code) =
    down_mem:down_mem_t ->
    num_b8_slots:IX64.max_slots ->
    args:list inl_arg ->
    #pre_rel:_ ->
    #post_rel:_ ->
    predict:inline_prediction down_mem c num_b8_slots args pre_rel post_rel ->
    FStar.HyperStack.ST.Stack inline_als_ret
        (requires (fun h0 -> mem_roots_p h0 (extract_args args) /\ pre_rel h0))
        (ensures fun h0 ret h1 -> inline_as_lowstar_sig_post down_mem c num_b8_slots args h0 predict ret h1)

val inline_wrap_variadic (c:TS.tainted_code) : inline_as_lowstar_sig c

[@__reduce__]
let (++) (#t:inline_arg) (x:td_as_type (get_inline_td t)) (args:list inl_arg) = (| t, x |) :: args

[@__reduce__]
let rec inline_rel_gen_t
      (c:TS.tainted_code)
      (td:list inline_arg)
      (args:list inl_arg)
      (f: list inl_arg -> Type) =
    match td with
    | [] -> f args
    | hd::tl ->
      x:td_as_type (get_inline_td hd) ->
      inline_rel_gen_t c tl (x++args) f

[@__reduce__]
let elim_inline_rel_gen_t_nil #c #args #f (x:inline_rel_gen_t c [] args f)
  : f args
  = x

[@__reduce__]
let elim_inline_rel_gen_t_cons #c hd tl #args #f (p:inline_rel_gen_t c (hd::tl) args f)
  : (x:td_as_type (get_inline_td hd) ->
      inline_rel_gen_t c tl (x++args) f)
  = p

let rec inline_prediction_t
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:IX64.max_slots)
      (dom:list inline_arg)
      (args:list inl_arg)
      (pre_rel:inline_rel_gen_t c dom args (inline_prediction_pre_rel_t c))
      (post_rel:inline_rel_gen_t c dom args (inline_prediction_post_rel_t c num_b8_slots))
    = match dom with
      | [] ->
        inline_prediction down_mem c num_b8_slots args pre_rel post_rel

      | hd::tl ->
        x:td_as_type (get_inline_td hd) ->
        inline_prediction_t
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_inline_rel_gen_t_cons hd tl pre_rel x)
          (elim_inline_rel_gen_t_cons hd tl post_rel x)

[@__reduce__]
let elim_inline_predict_t_nil
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#num_b8_slots:IX64.max_slots)
      (#args:list inl_arg)
      (#pre_rel:_)
      (#post_rel:_)
      (p:inline_prediction_t down_mem c num_b8_slots [] args pre_rel post_rel)
   : inline_prediction down_mem c num_b8_slots args pre_rel post_rel
   = p

[@__reduce__]
let elim_inline_predict_t_cons
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#num_b8_slots:IX64.max_slots)
      (hd:inline_arg)
      (tl:list inline_arg)
      (#args:list inl_arg)
      (#pre_rel:_)
      (#post_rel:_)
      (p:inline_prediction_t down_mem c num_b8_slots (hd::tl) args pre_rel post_rel)
   : x:td_as_type (get_inline_td hd) ->
     inline_prediction_t down_mem c num_b8_slots tl (x ++ args)
       (elim_inline_rel_gen_t_cons hd tl pre_rel x)
       (elim_inline_rel_gen_t_cons hd tl post_rel x)
   = p

[@__reduce__]
let rec inline_as_lowstar_sig_t
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:IX64.max_slots)
      (dom:list inline_arg)
      (args:list inl_arg)
      (pre_rel:inline_rel_gen_t c dom args (inline_prediction_pre_rel_t c))
      (post_rel:inline_rel_gen_t c dom args (inline_prediction_post_rel_t c num_b8_slots))
      (predict:inline_prediction_t down_mem c num_b8_slots dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack inline_als_ret
           (requires (fun h0 ->
              mem_roots_p h0 (extract_args args) /\
              elim_inline_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              inline_as_lowstar_sig_post down_mem c num_b8_slots args h0
                #pre_rel #post_rel (elim_inline_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type (get_inline_td hd) ->
        inline_as_lowstar_sig_t
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_inline_rel_gen_t_cons hd tl pre_rel x)
          (elim_inline_rel_gen_t_cons hd tl post_rel x)
          (elim_inline_predict_t_cons hd tl predict x)

val inline_wrap
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (dom:inline_args)
    (#pre_rel:inline_rel_gen_t c dom [] (inline_prediction_pre_rel_t c))
    (#post_rel:inline_rel_gen_t c dom [] (inline_prediction_post_rel_t c num_b8_slots))
    (predict:inline_prediction_t down_mem c num_b8_slots dom [] pre_rel post_rel)
  : inline_as_lowstar_sig_t down_mem c num_b8_slots dom [] pre_rel post_rel predict


[@__reduce__]
let rec inline_as_lowstar_sig_t_weak
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:IX64.max_slots)
      (dom:list inline_arg)
      (args:list inl_arg)
      (pre_rel:inline_rel_gen_t c dom args (inline_prediction_pre_rel_t c))
      (post_rel:inline_rel_gen_t c dom args (inline_prediction_post_rel_t c num_b8_slots))
      (predict:inline_prediction_t down_mem c num_b8_slots dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack inline_als_ret
           (requires (fun h0 ->
              mem_roots_p h0 (extract_args args) /\
              elim_inline_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              inline_as_lowstar_sig_post_weak down_mem c num_b8_slots args h0
                #pre_rel #post_rel (elim_inline_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type (get_inline_td hd) ->
        inline_as_lowstar_sig_t_weak
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_inline_rel_gen_t_cons hd tl pre_rel x)
          (elim_inline_rel_gen_t_cons hd tl post_rel x)
          (elim_inline_predict_t_cons hd tl predict x)

val inline_wrap_weak
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:IX64.max_slots)
    (dom:inline_args)
    (#pre_rel:inline_rel_gen_t c dom [] (inline_prediction_pre_rel_t c))
    (#post_rel:inline_rel_gen_t c dom [] (inline_prediction_post_rel_t c num_b8_slots))
    (predict:inline_prediction_t down_mem c num_b8_slots dom [] pre_rel post_rel)
  : inline_as_lowstar_sig_t_weak down_mem c num_b8_slots dom [] pre_rel post_rel predict
