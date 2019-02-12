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

//let max_arity : nat = if IA.win then 4 else 6
let reg_nat (n:nat) = i:nat{i < n}
let arity_ok n 'a = l:list 'a { List.Tot.length l <= n }

unfold
let injective f = forall x y. f x == f y ==> x == y

noeq
type arg_reg_relation' (n:nat) =  
  | Rel: of_reg:(MS.reg -> option (reg_nat n)) ->
         of_arg:(reg_nat n -> MS.reg){
           // This function should be injective
           injective of_arg /\ 
           // Rsp is not a valid register to store paramters
           (forall (i:reg_nat n). of_arg i <> MS.Rsp) /\
           // of_reg should always return Some when the register corresponds to an of_arg 
           (forall (i:reg_nat n).
              Some? (of_reg (of_arg i)) /\ Some?.v (of_reg (of_arg i)) = i)} ->
         arg_reg_relation' n

unfold
let arg_reg_relation (n:nat) = (v:arg_reg_relation' n{
  // of_reg is a partial inverse of of_arg
  forall (r:MS.reg). Some? (v.of_reg r) ==> v.of_arg (Some?.v (v.of_reg r)) = r})

let registers = MS.reg -> MS.nat64

let upd_reg (n:nat) (arg_reg:arg_reg_relation n) (regs:registers) (i:nat) (v:_) : registers =
    fun (r:MS.reg) ->
      match arg_reg.of_reg r with
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
    let b:b8 = Buffer (x <: B.buffer UInt8.t) true in
    global_addrs_map b
  | TD_ImmBuffer _ _ -> global_addrs_map (imm_to_b8 x)

[@__reduce__]
let update_regs (n:nat)
                (arg_reg:arg_reg_relation n)
                (x:arg)
                (i:reg_nat n)
                (regs:registers)
  : GTot registers
  = upd_reg n arg_reg regs i (arg_as_nat64 x)

let max_slots = n:pos{UInt.size n UInt32.n /\ n % 8 == 0}

let stack_buffer (num_b8_slots:max_slots) =
  b:buf_t TUInt64{
    B.length b == num_b8_slots
  }

let regs_with_stack (regs:registers) (#num_b8_slots:_) (stack_b:stack_buffer num_b8_slots)
  : registers =
    fun r ->
      let open FStar.Mul in
      if r = MS.Rsp then
        global_addrs_map (Buffer stack_b true) + num_b8_slots
      else regs r

[@__reduce__]
let rec register_of_args (max_arity:nat)
                         (arg_reg:arg_reg_relation max_arity)
                         (n:nat{n <= max_arity})
                         (args:list arg{List.Tot.length args = n})
                         (regs:registers) : GTot registers =
    match args with
    | [] -> regs
    | hd::tl ->
      update_regs max_arity arg_reg hd (n - 1) (register_of_args max_arity arg_reg (n - 1) tl regs)

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
      upd_taint_map_b8 tm (Buffer x true) tnt
    | (| TD_ImmBuffer t {taint=tnt}, x |) ->
      upd_taint_map_b8 tm (imm_to_b8 x) tnt
    | (| TD_Base _, _ |) ->
      tm

let init_taint : taint_map = fun r -> MS.Public

[@__reduce__]
let mk_taint (as:list arg) (tm:taint_map) : GTot taint_map =
  List.fold_right_gtot as upd_taint_map_arg init_taint

let taint_of_arg (a:arg) =
  let (| tag, x |) = a in
  match tag with
  | TD_ImmBuffer TUInt64 {taint=tnt}
  | TD_ImmBuffer TUInt128 {taint=tnt}
  | TD_Buffer TUInt64 {taint=tnt}
  | TD_Buffer TUInt128 {taint=tnt} -> Some tnt
  | _ -> None

let taint_arg_b8 (a:arg{Some? (taint_of_arg a)}) : b8 =
  let (| tag, x |) = a in
  match tag with
  | TD_Buffer _ _ -> Buffer (x <: B.buffer UInt8.t) true
  | TD_ImmBuffer _ _ -> imm_to_b8 x

let rec taint_arg_args_b8_mem (args:list arg) (a:arg)
  : Lemma (List.memP a args /\ Some? (taint_of_arg a) ==>
           List.memP (taint_arg_b8 a) (args_b8 args))
  = match args with
    | [] -> ()
    | hd::tl ->
      taint_arg_args_b8_mem tl a

let rec mk_taint_equiv
     (args:list arg{disjoint_or_eq args})
     (a:arg)
   : Lemma (List.memP a args /\ Some? (taint_of_arg a) ==>
            Some?.v (taint_of_arg a) == (mk_taint args init_taint) (taint_arg_b8 a))
   = match args with
     | [] -> ()
     | hd::tl ->
       mk_taint_equiv tl a;
       let (| tag, x |) = hd in
       match tag with
       | TD_Base _ -> ()
       | TD_Buffer _ _ | TD_ImmBuffer _ _ ->
         disjoint_or_eq_cons hd tl;
         BigOps.big_and'_forall (disjoint_or_eq_1 hd) tl

////////////////////////////////////////////////////////////////////////////////

let state_builder_t (num_b8_slots:max_slots) (args:list arg) (codom:Type) =
    h0:HS.mem ->
    stack:stack_buffer num_b8_slots{mem_roots_p h0 (arg_of_sb stack::args)} ->
    GTot codom

// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let create_initial_trusted_state
      (n:nat)
      (arg_reg:arg_reg_relation n)
      (num_b8_slots:max_slots)
      (args:arity_ok n arg)
      (down_mem: down_mem_t)
  : state_builder_t num_b8_slots args (TS.traceState & mem) =
  fun h0 stack ->
    let open MS in
    let regs = register_of_args n arg_reg (List.Tot.length args) args IA.init_regs in
    let regs = FunctionalExtensionality.on reg (regs_with_stack regs stack) in
    let xmms = FunctionalExtensionality.on xmm IA.init_xmms in
    let args = arg_of_sb stack::args in
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
      TS.memTaint = create_memtaint mem (args_b8 args) (mk_taint args init_taint)
    },
    mem

////////////////////////////////////////////////////////////////////////////////
let prediction_pre_rel_t (n:nat) (c:TS.tainted_code) (args:arity_ok n arg) =
    h0:mem_roots args ->
    prop

let return_val_t (sn:TS.traceState) = r:UInt64.t{UInt64.v r == BS.eval_reg MS.Rax sn.TS.state}
let return_val (sn:TS.traceState) : return_val_t sn =
  UInt64.uint_to_t (BS.eval_reg MS.Rax sn.TS.state)

let prediction_post_rel_t (n:nat) (c:TS.tainted_code) (num_b8_slots:max_slots) (args:arity_ok n arg) =
    h0:mem_roots args ->
    s0:TS.traceState ->
    push_h0:mem_roots args ->
    alloc_push_h0:mem_roots args ->
    b:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::args)} ->
    (UInt64.t & nat & mem) ->
    sn:TS.traceState ->
    prop

[@__reduce__]
let prediction_pre
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok n arg)
    (pre_rel: prediction_pre_rel_t n c args)
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
  s0 == fst (create_initial_trusted_state n arg_reg num_b8_slots args down_mem alloc_push_h0 b)

[@__reduce__]
let prediction_post
    (n:nat)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok n arg)
    (post_rel: prediction_post_rel_t n c num_b8_slots args)
    (h0:mem_roots args)
    (s0:TS.traceState)
    (push_h0:mem_roots args)
    (alloc_push_h0:mem_roots args)
    (sb:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb sb::args)})
    (rax_fuel_mem:(UInt64.t & nat & mem)) =
  let s_args = arg_of_sb sb :: args in
  let rax, fuel, final_mem = rax_fuel_mem in
  Some? (TS.taint_eval_code c fuel s0) /\ (
    let s1 = Some?.v (TS.taint_eval_code c fuel s0) in
    let h1 = hs_of_mem final_mem in
    FStar.HyperStack.ST.equal_domains alloc_push_h0 h1 /\
    B.modifies (loc_modified_args s_args) alloc_push_h0 h1 /\
    mem_roots_p h1 s_args /\
    down_mem (mk_mem s_args h1) == s1.TS.state.BS.mem /\
    calling_conventions s0 s1 /\
    rax == return_val s1 /\
    post_rel h0 s0 push_h0 alloc_push_h0 sb rax_fuel_mem s1
  )

let prediction
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok n arg)
    (pre_rel:prediction_pre_rel_t n c args)
    (post_rel:prediction_post_rel_t n c num_b8_slots args) =
  h0:mem_roots args{pre_rel h0} ->
  s0:TS.traceState ->
  push_h0:mem_roots args ->
  alloc_push_h0:mem_roots args ->
  b:stack_buffer num_b8_slots{mem_roots_p h0 args /\ mem_roots_p alloc_push_h0 (arg_of_sb b::args)} ->
  Ghost (UInt64.t & nat & mem)
    (requires prediction_pre n arg_reg down_mem c num_b8_slots args pre_rel h0 s0 push_h0 alloc_push_h0 b)
    (ensures prediction_post n down_mem c num_b8_slots args post_rel h0 s0 push_h0 alloc_push_h0 b)

noeq
type as_lowstar_sig_ret =
  | As_lowstar_sig_ret :
      n:nat ->                 
      num_b8_slots:max_slots ->
      args:arity_ok n arg ->
      push_h0:mem_roots args ->
      alloc_push_h0:mem_roots args ->
      b:stack_buffer num_b8_slots{mem_roots_p alloc_push_h0 (arg_of_sb b::args)} ->
      fuel:nat ->
      final_mem:mem ->
      as_lowstar_sig_ret

let als_ret = UInt64.t & Ghost.erased as_lowstar_sig_ret

[@__reduce__]
let as_lowstar_sig_post
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok n arg)
    (h0:mem_roots args)
    (#pre_rel:_)
    (#post_rel: _)
    (predict:prediction n arg_reg down_mem c num_b8_slots args pre_rel post_rel)
    (ret:als_ret)
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
  let s0 = fst (create_initial_trusted_state n arg_reg num_b8_slots args down_mem alloc_push_h0 b) in
  let pre_pop = hs_of_mem final_mem in
  prediction_pre n arg_reg down_mem c num_b8_slots args pre_rel h0 s0 push_h0 alloc_push_h0 b /\
  (rax, fuel, final_mem) == predict h0 s0 push_h0 alloc_push_h0 b /\
  prediction_post n down_mem c num_b8_slots args post_rel h0 s0 push_h0 alloc_push_h0 b (rax, fuel, final_mem) /\
  FStar.HyperStack.ST.equal_domains alloc_push_h0 pre_pop /\
  HS.poppable pre_pop /\
  h1 == HS.pop pre_pop)

[@__reduce__]
let as_lowstar_sig_post_weak
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (args:arity_ok n arg)
    (h0:mem_roots args)
    (#pre_rel:_)
    (#post_rel: _)
    (predict:prediction n arg_reg down_mem c num_b8_slots args pre_rel post_rel)
    (ret:als_ret)
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
  let s0 = fst (create_initial_trusted_state n arg_reg num_b8_slots args down_mem alloc_push_h0 b) in
  let pre_pop = hs_of_mem final_mem in
  (exists fuel
     final_mem
     s1.
     let pre_pop = hs_of_mem final_mem in
     HS.poppable pre_pop /\
     h1 == HS.pop pre_pop /\
     rax == return_val s1 /\
     post_rel h0 s0 push_h0 alloc_push_h0 b (return_val s1, fuel, final_mem) s1))

[@__reduce__]
let as_lowstar_sig (c:TS.tainted_code) =
    n:nat ->
    arg_reg:arg_reg_relation n ->
    down_mem:down_mem_t ->
    num_b8_slots:max_slots ->
    args:arity_ok n arg ->
    #pre_rel:_ ->
    #post_rel:_ ->
    predict:prediction n arg_reg down_mem c num_b8_slots args pre_rel post_rel ->
    FStar.HyperStack.ST.Stack als_ret
        (requires (fun h0 -> mem_roots_p h0 args /\ pre_rel h0))
        (ensures fun h0 ret h1 -> as_lowstar_sig_post n arg_reg down_mem c num_b8_slots args h0 predict ret h1)

val wrap_variadic (c:TS.tainted_code) : as_lowstar_sig c

[@__reduce__]
let (++) (#t:td) (x:td_as_type t) (args:list arg) = (| t, x |) :: args

let arity_ok_2 (n:nat) (l:list 'a) (m:list 'b) = List.length l + List.length m <= n

[@__reduce__]
let rec rel_gen_t
      (n:nat)
      (c:TS.tainted_code)
      (td:list td)
      (args:list arg{arity_ok_2 n td args})
      (f: arity_ok n arg -> Type) =
    match td with
    | [] -> f args
    | hd::tl ->
      x:td_as_type hd ->
      rel_gen_t n c tl (x++args) f

[@__reduce__]
let elim_rel_gen_t_nil #n #c #args #f (x:rel_gen_t n c [] args f)
  : f args
  = x

[@__reduce__]
let elim_rel_gen_t_cons #n #c hd tl #args #f (p:rel_gen_t n c (hd::tl) args f)
  : (x:td_as_type hd ->
      rel_gen_t n c tl (x++args) f)
  = p

let rec prediction_t
      (n:nat)
      (arg_reg:arg_reg_relation n)
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:max_slots)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= n})
      (pre_rel:rel_gen_t n c dom args (prediction_pre_rel_t n c))
      (post_rel:rel_gen_t n c dom args (prediction_post_rel_t n c num_b8_slots))
    = match dom with
      | [] ->
        prediction n arg_reg down_mem c num_b8_slots args pre_rel post_rel

      | hd::tl ->
        x:td_as_type hd ->
        prediction_t
          n
          arg_reg
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)

[@__reduce__]
let elim_predict_t_nil
      (#n:nat)
      (#arg_reg:arg_reg_relation n)
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#num_b8_slots:max_slots)
      (#args:arity_ok n arg)
      (#pre_rel:_)
      (#post_rel:_)
      (p:prediction_t n arg_reg down_mem c num_b8_slots [] args pre_rel post_rel)
   : prediction n arg_reg down_mem c num_b8_slots args pre_rel post_rel
   = p

[@__reduce__]
let elim_predict_t_cons
      (#n:nat)
      (#arg_reg:arg_reg_relation n)
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#num_b8_slots:max_slots)
      (hd:td)
      (tl:list td)
      (#args:list arg{arity_ok_2 n (hd::tl) args})
      (#pre_rel:_)
      (#post_rel:_)
      (p:prediction_t n arg_reg down_mem c num_b8_slots (hd::tl) args pre_rel post_rel)
   : x:td_as_type hd ->
     prediction_t n arg_reg down_mem c num_b8_slots tl (x ++ args)
       (elim_rel_gen_t_cons hd tl pre_rel x)
       (elim_rel_gen_t_cons hd tl post_rel x)
   = p

[@__reduce__]
let rec as_lowstar_sig_t
      (n:nat)
      (arg_reg:arg_reg_relation n)
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:max_slots)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= n})
      (pre_rel:rel_gen_t n c dom args (prediction_pre_rel_t n c))
      (post_rel:rel_gen_t n c dom args (prediction_post_rel_t n c num_b8_slots))
      (predict:prediction_t n arg_reg down_mem c num_b8_slots dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack als_ret
           (requires (fun h0 ->
              mem_roots_p h0 args /\
              elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              as_lowstar_sig_post n arg_reg down_mem c num_b8_slots args h0
                #pre_rel #post_rel (elim_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type hd ->
        as_lowstar_sig_t
          n
          arg_reg
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)
          (elim_predict_t_cons hd tl predict x)

val wrap
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (dom:arity_ok n td)
    (#pre_rel:rel_gen_t n c dom [] (prediction_pre_rel_t n c))
    (#post_rel:rel_gen_t n c dom [] (prediction_post_rel_t n c num_b8_slots))
    (predict:prediction_t n arg_reg down_mem c num_b8_slots dom [] pre_rel post_rel)
  : as_lowstar_sig_t n arg_reg down_mem c num_b8_slots dom [] pre_rel post_rel predict

[@__reduce__]
let rec as_lowstar_sig_t_weak
      (n:nat)
      (arg_reg:arg_reg_relation n)
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (num_b8_slots:max_slots)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= n})
      (pre_rel:rel_gen_t n c dom args (prediction_pre_rel_t n c))
      (post_rel:rel_gen_t n c dom args (prediction_post_rel_t n c num_b8_slots))
      (predict:prediction_t n arg_reg down_mem c num_b8_slots dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack als_ret
           (requires (fun h0 ->
              mem_roots_p h0 args /\
              elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              as_lowstar_sig_post_weak n arg_reg down_mem c num_b8_slots args h0
                #pre_rel #post_rel (elim_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type hd ->
        as_lowstar_sig_t_weak
          n
          arg_reg
          down_mem
          c
          num_b8_slots
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)
          (elim_predict_t_cons hd tl predict x)

val wrap_weak
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (num_b8_slots:max_slots)
    (dom:arity_ok n td)
    (#pre_rel:rel_gen_t n c dom [] (prediction_pre_rel_t n c))
    (#post_rel:rel_gen_t n c dom [] (prediction_post_rel_t n c num_b8_slots))
    (predict:prediction_t n arg_reg down_mem c num_b8_slots dom [] pre_rel post_rel)
  : as_lowstar_sig_t_weak n arg_reg down_mem c num_b8_slots dom [] pre_rel post_rel predict

let register_of_arg_i (i:reg_nat (if IA.win then 4 else 6)) : MS.reg =
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
  : option (i:reg_nat (if IA.win then 4 else 6))
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

let max_stdcall : nat = if IA.win then 4 else 6
let arity_ok_stdcall = arity_ok max_stdcall

let arg_reg_stdcall : arg_reg_relation max_stdcall =
  Rel arg_of_register register_of_arg_i

[@__reduce__]
let as_lowstar_sig_t_weak_stdcall = as_lowstar_sig_t_weak max_stdcall arg_reg_stdcall

let wrap_weak_stdcall = wrap_weak max_stdcall arg_reg_stdcall
