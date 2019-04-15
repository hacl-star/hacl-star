module Interop.X64
open FStar.Mul
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module List = FStar.List.Tot

////////////////////////////////////////////////////////////////////////////////
//The calling convention w.r.t the register mapping
////////////////////////////////////////////////////////////////////////////////

let calling_conventions 
  (s0 s1:TS.traceState)
  (regs_modified: MS.reg -> bool)
  (xmms_modified: MS.xmm -> bool) =
  let s0 = s0.TS.state in
  let s1 = s1.TS.state in
  s1.BS.ok /\
  s0.BS.regs MS.Rsp == s1.BS.regs MS.Rsp /\
  (forall (r:MS.reg). {:pattern (s0.BS.regs r)}
    not (regs_modified r) ==> s0.BS.regs r == s1.BS.regs r) /\
  (forall (x:MS.xmm). {:pattern (s0.BS.xmms x)} 
    not (xmms_modified x) ==> s0.BS.xmms x == s1.BS.xmms x)

let reg_nat (n:nat) = i:nat{i < n}
let arity_ok n 'a = l:list 'a { List.Tot.length l <= n }

(* We limit the number of args we can pass through the interop wrappers to an arbitrary 20.
   This ensures first that the addr_map axiom is sound: Since the length of buffers is limited to 2^32, we can prove that addr_map is inhabited.
   for extra arguments + the extra slots needed.
   Note that this number can be increased if needed*)
let arg_list = l:list arg{List.Tot.length l <= 20}
let arg_list_sb = l:list arg{List.Tot.length l <= 21}

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
  | TD_Buffer src _ _ ->
    let b:b8 = Buffer (x <: B.buffer (base_typ_as_type src)) true in
    global_addrs_map b
  | TD_ImmBuffer src _ _ -> global_addrs_map (imm_to_b8 src x)

[@__reduce__]
let update_regs (n:nat)
                (arg_reg:arg_reg_relation n)
                (x:arg)
                (i:reg_nat n)
                (regs:registers)
  : GTot registers
  = upd_reg n arg_reg regs i (arg_as_nat64 x)

[@__reduce__]
let rec register_of_args (max_arity:nat)
                         (arg_reg:arg_reg_relation max_arity)
                         (n:nat)
                         (args:arg_list{List.Tot.length args = n})
                         (regs:registers) : GTot (regs':registers{regs MS.Rsp == regs' MS.Rsp}) =
    match args with
    | [] -> regs
    | hd::tl ->
      if n > max_arity then 
        // This arguments will be passed on the stack
        register_of_args max_arity arg_reg (n-1) tl regs
      else
        update_regs max_arity arg_reg hd (n - 1) (register_of_args max_arity arg_reg (n - 1) tl regs)

// Pass extra arguments on the stack. The arity_ok condition on inline wrappers ensures that
// this only happens for stdcalls
[@__reduce__]
let rec stack_of_args (max_arity:nat)
                      (n:nat)
                      (rsp:int)
                      (args:arg_list{List.Tot.length args = n})
                      (st:Map.t int Words_s.nat8)
                      : GTot (Map.t int Words_s.nat8) =
  match args with
  | [] -> st
  | hd::tl ->
    if n <= max_arity then st // We can pass the remaining args in registers
    else
      let ptr = ((n - max_arity) - 1) * 8 // Arguments on the stack are pushed from right to left
        + (if IA.win then 32 else 0) // The shadow space on Windows comes next
        + 8 // The return address is then pushed on the stack
        + rsp // And we then have all the extra slots required for the Vale procedure
      in
      let st1 = stack_of_args max_arity (n-1) rsp tl st in
      let v = arg_as_nat64 hd in // We will store the arg hd
      BS.update_heap64 ptr v st1

////////////////////////////////////////////////////////////////////////////////
let taint_map = b8 -> GTot MS.taint

let upd_taint_map_b8 (taint:taint_map) (x:b8) (tnt:MS.taint)  : taint_map =
   fun (y:b8) ->
     if StrongExcludedMiddle.strong_excluded_middle ((x <: b8) == y) then
        tnt
     else taint y

[@__reduce__]
let upd_taint_map_arg (a:arg) (tm:taint_map) : GTot taint_map =
    match a with
    | (| TD_Buffer _ _ {taint=tnt}, x |) ->
      upd_taint_map_b8 tm (Buffer x true) tnt
    | (| TD_ImmBuffer src _ {taint=tnt}, x |) ->
      upd_taint_map_b8 tm (imm_to_b8 src x) tnt
    | (| TD_Base _, _ |) ->
      tm

let init_taint : taint_map = fun r -> MS.Public

[@__reduce__]
let mk_taint (as:arg_list_sb) (tm:taint_map) : GTot taint_map =
  List.fold_right_gtot as upd_taint_map_arg init_taint

let taint_of_arg (a:arg) =
  let (| tag, x |) = a in
  match tag with
  | TD_ImmBuffer _ TUInt64 {taint=tnt}
  | TD_ImmBuffer _ TUInt128 {taint=tnt}
  | TD_Buffer _ TUInt64 {taint=tnt}
  | TD_Buffer _ TUInt128 {taint=tnt} -> Some tnt
  | _ -> None

let taint_arg_b8 (a:arg{Some? (taint_of_arg a)}) : GTot b8 =
  let (| tag, x |) = a in
  match tag with
  | TD_Buffer src _ _ -> Buffer (x <: B.buffer (base_typ_as_type src)) true
  | TD_ImmBuffer src _ _ -> imm_to_b8 src x

let rec taint_arg_args_b8_mem (args:arg_list) (a:arg)
  : Lemma (List.memP a args /\ Some? (taint_of_arg a) ==>
           List.memP (taint_arg_b8 a) (args_b8 args))
  = match args with
    | [] -> ()
    | hd::tl ->
      taint_arg_args_b8_mem tl a

let rec mk_taint_equiv
     (args:arg_list_sb{disjoint_or_eq args})
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
       | TD_Buffer _ _ _ | TD_ImmBuffer _ _ _ ->
         disjoint_or_eq_cons hd tl;
         BigOps.big_and'_forall (disjoint_or_eq_1 hd) tl

////////////////////////////////////////////////////////////////////////////////

let state_builder_t (max_arity:nat) (args:arg_list) (codom:Type) =
    h0:HS.mem{mem_roots_p h0 args} ->
    GTot codom

// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let create_initial_trusted_state
      (max_arity:nat)
      (arg_reg:arg_reg_relation max_arity)
      (args:arg_list)
      (down_mem: down_mem_t)
  : state_builder_t max_arity args (TS.traceState & mem) =
  fun h0 ->
    let open MS in
    let regs = register_of_args max_arity arg_reg (List.Tot.length args) args IA.init_regs in
    let regs = FunctionalExtensionality.on reg regs in
    let xmms = FunctionalExtensionality.on xmm IA.init_xmms in
    let init_rsp = regs Rsp in
    // Create an initial empty stack
    let stack = Map.const_on Set.empty 0 in
    // Spill additional arguments on the stack
    let stack = stack_of_args max_arity (List.Tot.length args) init_rsp args stack in
    let mem:mem = mk_mem args h0 in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = IA.init_flags;
      BS.mem = down_mem mem;
      BS.stack = BS.Vale_stack init_rsp stack;
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = create_memtaint mem (args_b8 args) (mk_taint args init_taint)
    },
    mem

////////////////////////////////////////////////////////////////////////////////
let prediction_pre_rel_t (c:TS.tainted_code) (args:arg_list) =
    h0:mem_roots args ->
    prop

let return_val_t (sn:TS.traceState) = r:UInt64.t{UInt64.v r == BS.eval_reg MS.Rax sn.TS.state}
let return_val (sn:TS.traceState) : return_val_t sn =
  UInt64.uint_to_t (BS.eval_reg MS.Rax sn.TS.state)

let prediction_post_rel_t (c:TS.tainted_code) (args:arg_list) =
    h0:mem_roots args ->
    s0:TS.traceState ->
    (UInt64.t & nat & mem) ->
    sn:TS.traceState ->
    prop

[@__reduce__]
let prediction_pre
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (args:arg_list)
    (pre_rel: prediction_pre_rel_t c args)
    (h0:mem_roots args)
    (s0:TS.traceState)
    =
  pre_rel h0 /\
  s0 == fst (create_initial_trusted_state n arg_reg args down_mem h0)

[@__reduce__]
let prediction_post
    (n:nat)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (args:arg_list)
    (post_rel: prediction_post_rel_t c args)
    (h0:mem_roots args)
    (s0:TS.traceState)
    (rax_fuel_mem:(UInt64.t & nat & mem)) =
  let rax, fuel, final_mem = rax_fuel_mem in
  Some? (TS.taint_eval_code c fuel s0) /\ (
    let s1 = Some?.v (TS.taint_eval_code c fuel s0) in
    let h1 = hs_of_mem final_mem in
    FStar.HyperStack.ST.equal_domains h0 h1 /\
    B.modifies (loc_modified_args args) h0 h1 /\
    mem_roots_p h1 args /\
    down_mem (mk_mem args h1) == s1.TS.state.BS.mem /\
    calling_conventions s0 s1 regs_modified xmms_modified /\
    rax == return_val s1 /\
    post_rel h0 s0 rax_fuel_mem s1
  )

let prediction
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (args:arg_list)
    (pre_rel:prediction_pre_rel_t c args)
    (post_rel:prediction_post_rel_t c args) =
  h0:mem_roots args{pre_rel h0} ->
  s0:TS.traceState ->
  Ghost (UInt64.t & nat & mem)
    (requires prediction_pre n arg_reg down_mem c args pre_rel h0 s0)
    (ensures prediction_post n regs_modified xmms_modified down_mem c args post_rel h0 s0)

noeq
type as_lowstar_sig_ret =
  | As_lowstar_sig_ret :
      n:nat ->                 
      args:arg_list ->
      fuel:nat ->
      final_mem:mem ->
      as_lowstar_sig_ret

let als_ret = UInt64.t & Ghost.erased as_lowstar_sig_ret

[@__reduce__]
let as_lowstar_sig_post
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (args:arg_list)
    (h0:mem_roots args)
    (#pre_rel:_)
    (#post_rel: _)
    (predict:prediction n arg_reg regs_modified xmms_modified down_mem c args pre_rel post_rel)
    (ret:als_ret)
    (h1:HS.mem) =
  (* write it this way to be reduction friendly *)
  let rax = fst ret in
  let ret = Ghost.reveal (snd ret) in
  args == As_lowstar_sig_ret?.args ret /\
  n == As_lowstar_sig_ret?.n ret /\
 (let fuel = As_lowstar_sig_ret?.fuel ret in
  let final_mem = As_lowstar_sig_ret?.final_mem ret in
  let s0 = fst (create_initial_trusted_state n arg_reg args down_mem h0) in
  h1 == hs_of_mem final_mem /\
  prediction_pre n arg_reg down_mem c args pre_rel h0 s0 /\
  (rax, fuel, final_mem) == predict h0 s0 /\
  prediction_post n regs_modified xmms_modified down_mem c args post_rel h0 s0 (rax, fuel, final_mem) /\
  FStar.HyperStack.ST.equal_domains h0 h1)

[@__reduce__]
let as_lowstar_sig_post_weak
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)    
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (args:arg_list)
    (h0:mem_roots args)
    (#pre_rel:_)
    (#post_rel: _)
    (predict:prediction n arg_reg regs_modified xmms_modified down_mem c args pre_rel post_rel)
    (ret:als_ret)
    (h1:HS.mem) =
  (* write it this way to be reduction friendly *)
  let rax = fst ret in
  let ret = Ghost.reveal (snd ret) in
  args == As_lowstar_sig_ret?.args ret /\
  n == As_lowstar_sig_ret?.n ret /\
 (let fuel = As_lowstar_sig_ret?.fuel ret in
  let final_mem = As_lowstar_sig_ret?.final_mem ret in
  let s0 = fst (create_initial_trusted_state n arg_reg args down_mem h0) in
  (exists fuel
     final_mem
     s1.
     h1 == hs_of_mem final_mem /\
     rax == return_val s1 /\
     post_rel h0 s0 (return_val s1, fuel, final_mem) s1))

[@__reduce__]
let as_lowstar_sig (c:TS.tainted_code) =
    n:nat ->
    arg_reg:arg_reg_relation n ->
    regs_modified:(MS.reg -> bool) ->
    xmms_modified:(MS.xmm -> bool) ->    
    down_mem:down_mem_t ->
    args:arg_list ->
    #pre_rel:_ ->
    #post_rel:_ ->
    predict:prediction n arg_reg regs_modified xmms_modified down_mem c args pre_rel post_rel ->
    FStar.HyperStack.ST.Stack als_ret
        (requires (fun h0 -> mem_roots_p h0 args /\ pre_rel h0))
        (ensures fun h0 ret h1 -> as_lowstar_sig_post n arg_reg regs_modified xmms_modified down_mem c args h0 predict ret h1)

val wrap_variadic (c:TS.tainted_code) : as_lowstar_sig c

[@__reduce__]
let (++) (#t:td) (x:td_as_type t) (args:list arg) = (| t, x |) :: args

[@__reduce__]
let rec rel_gen_t
      (c:TS.tainted_code)
      (td:list td)
      (args:arg_list{List.length args + List.length td <= 20})
      (f: arg_list -> Type) =
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
      (n:nat)
      (arg_reg:arg_reg_relation n)
      (regs_modified:MS.reg -> bool)
      (xmms_modified:MS.xmm -> bool)
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (dom:list td)
      (args:arg_list{List.length dom + List.length args <= 20})
      (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
      (post_rel:rel_gen_t c dom args (prediction_post_rel_t c))
    =
    match dom with
      | [] ->
        prediction n arg_reg regs_modified xmms_modified down_mem c args pre_rel post_rel

      | hd::tl ->
        x:td_as_type hd ->
        prediction_t
          n
          arg_reg
          regs_modified
          xmms_modified
          down_mem
          c
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)

[@__reduce__]
let elim_predict_t_nil
      (#n:nat)
      (#arg_reg:arg_reg_relation n)
      (#regs_modified:MS.reg -> bool)
      (#xmms_modified:MS.xmm -> bool)
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (#args:arg_list)
      (#pre_rel:_)
      (#post_rel:_)
      (p:prediction_t n arg_reg regs_modified xmms_modified down_mem c [] args pre_rel post_rel)
   : prediction n arg_reg regs_modified xmms_modified down_mem c args pre_rel post_rel
   = p

[@__reduce__]
let elim_predict_t_cons
      (#n:nat)
      (#arg_reg:arg_reg_relation n)
      (#regs_modified:MS.reg -> bool)
      (#xmms_modified:MS.xmm -> bool)
      (#down_mem:down_mem_t)
      (#c:TS.tainted_code)
      (hd:td)
      (tl:list td)
      (#args:arg_list{List.length args + List.length tl <= 19})
      (#pre_rel:_)
      (#post_rel:_)
      (p:prediction_t n arg_reg regs_modified xmms_modified down_mem c (hd::tl) args pre_rel post_rel)
   : x:td_as_type hd ->
     prediction_t n arg_reg regs_modified xmms_modified down_mem c tl (x ++ args)
       (elim_rel_gen_t_cons hd tl pre_rel x)
       (elim_rel_gen_t_cons hd tl post_rel x)
   = p

[@__reduce__]
let rec as_lowstar_sig_t
      (n:nat)
      (arg_reg:arg_reg_relation n)
      (regs_modified:MS.reg -> bool)
      (xmms_modified:MS.xmm -> bool)
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (dom:list td)
      (args:arg_list{List.length args + List.length dom <= 20})
      (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
      (post_rel:rel_gen_t c dom args (prediction_post_rel_t c))
      (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack als_ret
           (requires (fun h0 ->
              mem_roots_p h0 args /\
              elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              as_lowstar_sig_post n arg_reg regs_modified xmms_modified down_mem c args h0
                #pre_rel #post_rel (elim_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type hd ->
        as_lowstar_sig_t
          n
          arg_reg
          regs_modified
          xmms_modified
          down_mem
          c
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)
          (elim_predict_t_cons hd tl predict x)

private
val wrap'
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)    
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (dom:list td{List.length dom <= 20})
    (#pre_rel:rel_gen_t c dom [] (prediction_pre_rel_t c))
    (#post_rel:rel_gen_t c dom [] (prediction_post_rel_t c))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel)
  : as_lowstar_sig_t n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel predict

[@__reduce__]
private
let rec as_lowstar_sig_t_weak'
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
      (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel) =
      match dom with
      | [] ->
        (unit ->
         FStar.HyperStack.ST.Stack als_ret
           (requires (fun h0 ->
              mem_roots_p h0 args /\
              elim_rel_gen_t_nil pre_rel h0))
           (ensures fun h0 ret h1 ->
              as_lowstar_sig_post_weak n arg_reg regs_modified xmms_modified down_mem c args h0
                #pre_rel #post_rel (elim_predict_t_nil predict) ret h1))
      | hd::tl ->
        x:td_as_type hd ->
        as_lowstar_sig_t_weak'
          n
          arg_reg
          regs_modified
          xmms_modified
          down_mem
          c
          tl
          (x ++ args)
          (elim_rel_gen_t_cons hd tl pre_rel x)
          (elim_rel_gen_t_cons hd tl post_rel x)
          (elim_predict_t_cons hd tl predict x)

private
val wrap_weak'
    (n:nat)
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (dom:list td{List.length dom <= 20})
    (#pre_rel:rel_gen_t c dom [] (prediction_pre_rel_t c))
    (#post_rel:rel_gen_t c dom [] (prediction_post_rel_t c))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel)
  : as_lowstar_sig_t_weak' n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel predict
  
(* These two functions are the ones that are available from outside the module. The arity_ok restriction ensures that all arguments are passed in registers for inline assembly *)
[@__reduce__]
let as_lowstar_sig_t_weak
      (n:nat{n <= 20})
      (arg_reg:arg_reg_relation n)
      (regs_modified:MS.reg -> bool)
      (xmms_modified:MS.xmm -> bool)
      (down_mem:down_mem_t)
      (c:TS.tainted_code)
      (dom:list td)
      (args:list arg{List.length args + List.length dom <= n})
      (pre_rel:rel_gen_t c dom args (prediction_pre_rel_t c))
      (post_rel:rel_gen_t c dom args (prediction_post_rel_t c))
      (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel) =
      as_lowstar_sig_t_weak' n arg_reg regs_modified xmms_modified down_mem c dom args pre_rel post_rel predict

val wrap_weak
    (n:nat{n <= 20})
    (arg_reg:arg_reg_relation n)
    (regs_modified:MS.reg -> bool)
    (xmms_modified:MS.xmm -> bool)
    (down_mem:down_mem_t)
    (c:TS.tainted_code)
    (dom:arity_ok n td)
    (#pre_rel:rel_gen_t c dom [] (prediction_pre_rel_t c))
    (#post_rel:rel_gen_t c dom [] (prediction_post_rel_t c))
    (predict:prediction_t n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel)
  : as_lowstar_sig_t_weak n arg_reg regs_modified xmms_modified down_mem c dom [] pre_rel post_rel predict

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

let regs_modified_stdcall:MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if IA.win then (
    // These registers are callee-saved on Windows
    if r = Rbx || r = Rbp || r = Rdi || r = Rsi || r = Rsp || r = R12 || r = R13 || r = R14 || r = R15 then false
    // All the other ones may be modified
    else true
  ) else (
    // These registers are callee-saved on Linux
    if r = Rbx || r = Rbp || r = R12 || r = R13 || r = R14 || r = R15 then false
    // All the other ones may be modified
    else true
  )

let xmms_modified_stdcall:MS.xmm -> bool = fun (x:MS.xmm) ->
  let open MS in
  if IA.win then (
    // These xmms are callee-saved on Windows
    if x = 6 || x = 7 || x = 8 || x = 9 || x = 10 || x = 11 || x = 12 || x = 13 || x = 14 || x = 15 then false
    else true
  ) else
    // No xmm needs to be callee-saved on Linux
    true

(* For stdcalls, we do not have the arity_ok restriction: We can pass as many arguments as we want, the extra arguments will be passed on the stack *)
[@__reduce__]
let as_lowstar_sig_t_weak_stdcall = as_lowstar_sig_t_weak' max_stdcall arg_reg_stdcall regs_modified_stdcall xmms_modified_stdcall

let wrap_weak_stdcall = wrap_weak' max_stdcall arg_reg_stdcall regs_modified_stdcall xmms_modified_stdcall
