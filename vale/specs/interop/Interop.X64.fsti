module Interop.X64
open FStar.Mul
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module List = FStar.List.Tot

////////////////////////////////////////////////////////////////////////////////
//The calling convention w.r.t the register mapping
////////////////////////////////////////////////////////////////////////////////

// Callee-saved registers that must be saved through an execution
let calling_conventions (s0:TS.traceState) (s1:TS.traceState) =
  let open MS in
  let s0 = s0.TS.state in
  let s1 = s1.TS.state in
  // Ensures that the execution didn't crash
  s1.BS.ok /\
  // Ensures that the callee_saved registers are correct
  (if IA.win then (
    // Calling conventions for Windows
    s0.BS.regs Rbx == s1.BS.regs Rbx /\
    s0.BS.regs Rbp == s1.BS.regs Rbp /\
    s0.BS.regs Rdi == s1.BS.regs Rdi /\
    s0.BS.regs Rsi == s1.BS.regs Rsi /\
    s0.BS.regs Rsp == s1.BS.regs Rsp /\
    s0.BS.regs R12 == s1.BS.regs R12 /\
    s0.BS.regs R13 == s1.BS.regs R13 /\
    s0.BS.regs R14 == s1.BS.regs R14 /\
    s0.BS.regs R15 == s1.BS.regs R15 /\
    s0.BS.xmms 6 == s1.BS.xmms 6 /\
    s0.BS.xmms 7 == s1.BS.xmms 7 /\
    s0.BS.xmms 8 == s1.BS.xmms 8 /\
    s0.BS.xmms 9 == s1.BS.xmms 9 /\
    s0.BS.xmms 10 == s1.BS.xmms 10 /\
    s0.BS.xmms 11 == s1.BS.xmms 11 /\
    s0.BS.xmms 12 == s1.BS.xmms 12 /\
    s0.BS.xmms 13 == s1.BS.xmms 13 /\
    s0.BS.xmms 14 == s1.BS.xmms 14 /\
    s0.BS.xmms 15 == s1.BS.xmms 15
  ) else (
    // Calling conventions for Linux
    s0.BS.regs Rbx == s1.BS.regs Rbx /\
    s0.BS.regs Rbp == s1.BS.regs Rbp /\
    s0.BS.regs R12 == s1.BS.regs R12 /\
    s0.BS.regs R13 == s1.BS.regs R13 /\
    s0.BS.regs R14 == s1.BS.regs R14 /\
    s0.BS.regs R15 == s1.BS.regs R15
    )
  )

let max_arity : nat = if IA.win then 4 else 6
let reg_nat = i:nat{i < max_arity}
let arity_ok 'a = l:list 'a { List.Tot.length l < max_arity }

let register_of_arg_i (i:reg_nat) : MS.reg =
  let open MS in
  if IA.win then
    match i with
    | 0 -> Rcx
    | 1 -> Rdx
    | 2 -> R8
    | 3 -> R9
  else
    match i with
    | 0 -> Rdi
    | 1 -> Rsi
    | 2 -> Rdx
    | 3 -> Rcx
    | 4 -> R8
    | 5 -> R9

//A partial inverse of the above function
[@__reduce__]
let arg_of_register (r:MS.reg)
  : option (i:reg_nat{register_of_arg_i i = r})
  = let open MS in
    if IA.win then
       match r with
       | Rcx -> Some 0
       | Rdx -> Some 1
       | R8 -> Some 2
       | R9 -> Some 3
       | _ -> None
    else
       match r with
       | Rdi -> Some 0
       | Rsi -> Some 1
       | Rdx -> Some 2
       | Rcx -> Some 3
       | R8 -> Some 4
       | R9 -> Some 5
       | _ -> None

let registers = MS.reg -> MS.nat64

let upd_reg (regs:registers) (i:nat) (v:_) : registers =
    fun (r:MS.reg) ->
      match arg_of_register r with
      | Some j ->
        if i = j then v
        else regs r
      | _ -> regs r

[@__reduce__]
let arg_as_nat64 (a:arg) : GTot MS.nat64 =
  let (| tag, x |) = a in
  match tag with
  | TD_Base TUInt8 ->
     UInt8.v x
  | TD_Base TUInt16 ->
     UInt16.v x
  | TD_Base TUInt32 ->
     UInt32.v x
  | TD_Base TUInt64 ->
     UInt64.v x
  | TD_Buffer _ _ ->
    global_addrs_map x

[@__reduce__]
let update_regs (x:arg)
                (i:reg_nat)
                (regs:registers)
  : GTot registers
  = upd_reg regs i (arg_as_nat64 x)

let max_slots = n:pos{n < UInt32.n /\ n % 8 == 0}

let stack_buffer (num_b8_slots:max_slots) =
  b:buf_t TUInt64{
    B.length b == num_b8_slots
  }

let regs_with_stack (regs:registers) (#num_b8_slots:_) (stack_b:stack_buffer num_b8_slots)
  : registers =
    fun r ->
      let open FStar.Mul in
      if r = MS.Rsp then
        global_addrs_map stack_b + num_b8_slots
      else regs r

[@__reduce__]
let rec register_of_args (n:nat{n < max_arity})
                         (args:list arg{List.Tot.length args = n})
                         (regs:registers) : GTot registers =
    match args with
    | [] -> regs
    | hd::tl ->
      update_regs hd (n - 1) (register_of_args (n - 1) tl regs)

////////////////////////////////////////////////////////////////////////////////
let taint_map = b8 -> GTot MS.taint

let upd_taint_map_b8 (taint:taint_map) (x:b8) (tnt:MS.taint)  : taint_map =
   fun (y:b8) ->
     if StrongExcludedMiddle.strong_excluded_middle ((x <: b8) == y) then
        tnt
     else taint y

[@__reduce__]
let upd_taint_map_arg (a:arg) (tm:taint_map) : taint_map =
    match a with
    | (| TD_Buffer t {taint=tnt}, x |) ->
      upd_taint_map_b8 tm x tnt
    | _ ->
      tm

let init_taint : taint_map = fun r -> MS.Public

[@__reduce__]
let mk_taint (as:list arg) (tm:taint_map) : GTot taint_map =
  List.fold_right_gtot as upd_taint_map_arg init_taint

////////////////////////////////////////////////////////////////////////////////

let state_builder_t (num_b8_slots:max_slots) (args:list arg) (codom:Type) =
    h0:HS.mem ->
    stack:stack_buffer num_b8_slots{mem_roots_p h0 (arg_of_sb stack::args)} ->
    GTot codom

// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let create_initial_trusted_state
      (num_b8_slots:max_slots)
      (args:arity_ok arg)
      (down_mem: down_mem_t)
  : state_builder_t num_b8_slots args (TS.traceState & mem) =
  fun h0 stack ->
    let open MS in
    let regs = register_of_args (List.Tot.length args) args IA.init_regs in
    let regs = FunctionalExtensionality.on reg (regs_with_stack regs stack) in
    let xmms = FunctionalExtensionality.on xmm IA.init_xmms in
    let args = arg_of_sb stack::args in
    liveness_disjointness args h0;
    let mem:mem = mk_mem args h0 in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = 0;
      BS.mem = down_mem mem
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = create_memtaint mem (args_b8 args) (mk_taint args init_taint)
    },
    mem

////////////////////////////////////////////////////////////////////////////////
let prediction_pre_rel_t (c:TS.tainted_code) (args:arity_ok arg) =
    h0:mem_roots args ->
    prop

let prediction_post_rel_t (c:TS.tainted_code) (num_b8_slots:max_slots) (args:arity_ok arg) =
    h0:mem_roots args ->
    s0:TS.traceState ->
    push_h0:mem_roots args ->
    alloc_push_h0:mem_roots args ->
    b:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::args)} ->
    (nat & mem) ->
    sn:TS.traceState ->
    prop

[@__reduce__]
let prediction_pre
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok arg)
    (pre_rel: prediction_pre_rel_t c args)
    (h0:mem_roots args)
    (s0:TS.traceState)
    (push_h0:mem_roots args)
    (alloc_push_h0:mem_roots args)
    (b:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::args)})
    =
  pre_rel h0 /\
  HS.fresh_frame h0 push_h0 /\
  B.modifies B.loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  s0 == fst (create_initial_trusted_state num_b8_slots args down_mem alloc_push_h0 b)

[@__reduce__]
let prediction_post
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok arg)
    (post_rel: prediction_post_rel_t c num_b8_slots args)
    (h0:mem_roots args)
    (s0:TS.traceState)
    (push_h0:mem_roots args)
    (alloc_push_h0:mem_roots args)
    (sb:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb sb::args)})
    (fuel_mem:nat & mem) =
  let s_args = arg_of_sb sb :: args in
  let fuel, final_mem = fuel_mem in
  Some? (TS.taint_eval_code c fuel s0) /\ (
    let s1 = Some?.v (TS.taint_eval_code c fuel s0) in
    let h1 = hs_of_mem final_mem in
    FStar.HyperStack.ST.equal_domains alloc_push_h0 h1 /\
    B.modifies (loc_modified_args s_args) alloc_push_h0 h1 /\
    mem_roots_p h1 s_args /\
    down_mem (mk_mem s_args h1) == s1.TS.state.BS.mem /\
    calling_conventions s0 s1 /\
    post_rel h0 s0 push_h0 alloc_push_h0 sb fuel_mem s1
  )

let prediction
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok arg)
    (pre_rel:prediction_pre_rel_t c args)
    (post_rel:prediction_post_rel_t c num_b8_slots args) =
  h0:mem_roots args{pre_rel h0} ->
  s0:TS.traceState ->
  push_h0:mem_roots args ->
  alloc_push_h0:mem_roots args ->
  b:stack_buffer num_b8_slots{mem_roots_p h0 args /\ mem_roots_p alloc_push_h0 (arg_of_sb b::args)} ->
  Ghost (nat & mem)
    (requires prediction_pre down_mem c num_b8_slots args pre_rel h0 s0 push_h0 alloc_push_h0 b)
    (ensures prediction_post down_mem c num_b8_slots args post_rel h0 s0 push_h0 alloc_push_h0 b)

noeq
type as_lowstar_sig_ret =
  | As_lowstar_sig_ret :
      num_b8_slots:max_slots ->
      args:arity_ok arg ->
      push_h0:mem_roots args ->
      alloc_push_h0:mem_roots args ->
      b:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::args)} ->
      fuel:nat ->
      final_mem:mem ->
      as_lowstar_sig_ret

let als_ret = Ghost.erased as_lowstar_sig_ret

[@__reduce__]
let as_lowstar_sig_post
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok arg)
    (h0:mem_roots args)
    (#pre_rel:_)
    (#post_rel: _)
    (predict:prediction down_mem c num_b8_slots args pre_rel post_rel)
    (ret:als_ret)
    (h1:HS.mem) =
  (* write it this way to be reduction friendly *)
  let ret = Ghost.reveal ret in
  num_b8_slots == As_lowstar_sig_ret?.num_b8_slots ret /\
  args == As_lowstar_sig_ret?.args ret /\
 (let push_h0 = As_lowstar_sig_ret?.push_h0 ret in
  let alloc_push_h0 = As_lowstar_sig_ret?.alloc_push_h0 ret in
  let b = As_lowstar_sig_ret?.b ret in
  let fuel = As_lowstar_sig_ret?.fuel ret in
  let final_mem = As_lowstar_sig_ret?.final_mem ret in
  let s0 = fst (create_initial_trusted_state num_b8_slots args down_mem alloc_push_h0 b) in
  let pre_pop = hs_of_mem final_mem in
  prediction_pre down_mem c num_b8_slots args pre_rel h0 s0 push_h0 alloc_push_h0 b /\
  (fuel, final_mem) == predict h0 s0 push_h0 alloc_push_h0 b /\
  prediction_post down_mem c num_b8_slots args post_rel h0 s0 push_h0 alloc_push_h0 b (fuel, final_mem) /\
  FStar.HyperStack.ST.equal_domains alloc_push_h0 pre_pop /\
  HS.poppable pre_pop /\
  h1 == HS.pop pre_pop)

[@__reduce__]
let as_lowstar_sig_post_weak
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok arg)
    (h0:mem_roots args)
    (#pre_rel:_)
    (#post_rel: _)
    (predict:prediction down_mem c num_b8_slots args pre_rel post_rel)
    (ret:als_ret)
    (h1:HS.mem) =
  (* write it this way to be reduction friendly *)
  let ret = Ghost.reveal ret in
  num_b8_slots == As_lowstar_sig_ret?.num_b8_slots ret /\
  args == As_lowstar_sig_ret?.args ret /\
 (let push_h0 = As_lowstar_sig_ret?.push_h0 ret in
  let alloc_push_h0 = As_lowstar_sig_ret?.alloc_push_h0 ret in
  let b = As_lowstar_sig_ret?.b ret in
  let fuel = As_lowstar_sig_ret?.fuel ret in
  let final_mem = As_lowstar_sig_ret?.final_mem ret in
  let s0 = fst (create_initial_trusted_state num_b8_slots args down_mem alloc_push_h0 b) in
  let pre_pop = hs_of_mem final_mem in
  (exists fuel
     final_mem
     _s1.
     let pre_pop = hs_of_mem final_mem in
     HS.poppable pre_pop /\
     h1 == HS.pop pre_pop /\
     post_rel h0 s0 push_h0 alloc_push_h0 b (fuel, final_mem) _s1))

[@__reduce__]
let as_lowstar_sig (c:TS.tainted_code) =
    down_mem:down_mem_t ->
    num_b8_slots:max_slots ->
    args:arity_ok arg ->
    #pre_rel:_ ->
    #post_rel:_ ->
    predict:prediction down_mem c num_b8_slots args pre_rel post_rel ->
    FStar.HyperStack.ST.Stack als_ret
        (requires (fun h0 -> mem_roots_p h0 args /\ pre_rel h0))
        (ensures fun h0 ret h1 -> as_lowstar_sig_post down_mem c num_b8_slots args h0 predict ret h1)

val wrap_variadic (c:TS.tainted_code) : as_lowstar_sig c

[@__reduce__]
let (++) (#t:td) (x:td_as_type t) (args:list arg) = (| t, x |) :: args

let arity_ok_2 (l:list 'a) (m:list 'b) = List.length l + List.length m < max_arity

[@__reduce__]
let rec rel_gen_t
      (c:TS.tainted_code)
      (td:list td)
      (args:list arg{arity_ok_2 td args})
      (f: arity_ok arg -> Type) =
    match td with
    | [] -> f args
    | hd::tl ->
      x:td_as_type hd ->
      rel_gen_t c tl (x++args) f

[@__reduce__]
let elim_rel_gen_t_nil #c #args #f (x:rel_gen_t c [] args f)
  : f args
  = x

[@__reduce__]
let elim_rel_gen_t_cons #c hd tl #args #f (p:rel_gen_t c (hd::tl) args f)
  : (x:td_as_type hd ->
      rel_gen_t c tl (x++args) f)
  = p

let rec prediction_t
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:max_slots)
      (dom:list td)
      (args:list arg{List.length dom + List.length args < max_arity})
      (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
      (post_rel:rel_gen_t c dom args (prediction_post_rel_t c num_b8_slots))
    = match dom with
      | [] ->
        prediction down_mem c num_b8_slots args pre_rel post_rel

      | hd::tl ->
        x:td_as_type hd ->
        prediction_t
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)

[@__reduce__]
let elim_predict_t_nil
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#num_b8_slots:max_slots)
      (#args:arity_ok arg)
      (#pre_rel:_)
      (#post_rel:_)
      (p:prediction_t down_mem c num_b8_slots [] args pre_rel post_rel)
   : prediction down_mem c num_b8_slots args pre_rel post_rel
   = p

[@__reduce__]
let elim_predict_t_cons
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#num_b8_slots:max_slots)
      (hd:td)
      (tl:list td)
      (#args:list arg{arity_ok_2 (hd::tl) args})
      (#pre_rel:_)
      (#post_rel:_)
      (p:prediction_t down_mem c num_b8_slots (hd::tl) args pre_rel post_rel)
   : x:td_as_type hd ->
     prediction_t down_mem c num_b8_slots tl (x ++ args)
       (elim_rel_gen_t_cons hd tl pre_rel x)
       (elim_rel_gen_t_cons hd tl post_rel x)
   = p

[@__reduce__]
let rec as_lowstar_sig_t
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:max_slots)
      (dom:list td)
      (args:list arg{List.length dom + List.length args < max_arity})
      (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
      (post_rel:rel_gen_t c dom args (prediction_post_rel_t c num_b8_slots))
      (predict:prediction_t down_mem c num_b8_slots dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack als_ret
           (requires (fun h0 ->
              mem_roots_p h0 args /\
              elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              as_lowstar_sig_post down_mem c num_b8_slots args h0
                #pre_rel #post_rel (elim_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type hd ->
        as_lowstar_sig_t
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)
          (elim_predict_t_cons hd tl predict x)

val wrap
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (dom:arity_ok td)
    (#pre_rel:rel_gen_t c dom [] (prediction_pre_rel_t c))
    (#post_rel:rel_gen_t c dom [] (prediction_post_rel_t c num_b8_slots))
    (predict:prediction_t down_mem c num_b8_slots dom [] pre_rel post_rel)
  : as_lowstar_sig_t down_mem c num_b8_slots dom [] pre_rel post_rel predict


[@__reduce__]
let rec as_lowstar_sig_t_weak
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:max_slots)
      (dom:list td)
      (args:list arg{List.length dom + List.length args < max_arity})
      (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
      (post_rel:rel_gen_t c dom args (prediction_post_rel_t c num_b8_slots))
      (predict:prediction_t down_mem c num_b8_slots dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack als_ret
           (requires (fun h0 ->
              mem_roots_p h0 args /\
              elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              as_lowstar_sig_post_weak down_mem c num_b8_slots args h0
                #pre_rel #post_rel (elim_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type hd ->
        as_lowstar_sig_t_weak
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)
          (elim_predict_t_cons hd tl predict x)

val wrap_weak
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (dom:arity_ok td)
    (#pre_rel:rel_gen_t c dom [] (prediction_pre_rel_t c))
    (#post_rel:rel_gen_t c dom [] (prediction_post_rel_t c num_b8_slots))
    (predict:prediction_t down_mem c num_b8_slots dom [] pre_rel post_rel)
  : as_lowstar_sig_t_weak down_mem c num_b8_slots dom [] pre_rel post_rel predict
