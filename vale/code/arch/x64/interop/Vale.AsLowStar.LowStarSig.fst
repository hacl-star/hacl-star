module Vale.AsLowStar.LowStarSig
open Vale.Arch.HeapImpl
open Vale.X64.MemoryAdapters
open Vale.Interop.Base
module B = LowStar.Buffer
module BS = Vale.X64.Machine_Semantics_s
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module SI = Vale.X64.Stack_i
module MS = Vale.X64.Machine_s
module IA = Vale.Interop.Assumptions
module V = Vale.X64.Decls
module VS = Vale.X64.State
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module Map16 = Vale.Lib.Map16
open FStar.Mul

[@__reduce__]
let nat_to_uint (t:ME.base_typ) (x:ME.base_typ_as_vale_type t)
  : base_typ_as_type t
  = let open ME in
    match t with
    | TUInt8   -> UInt8.uint_to_t x
    | TUInt16  -> UInt16.uint_to_t x
    | TUInt32  -> UInt32.uint_to_t x
    | TUInt64  -> UInt64.uint_to_t x
    | TUInt128 -> x


let uint_to_nat (t:ME.base_typ) (x:base_typ_as_type t)
  : ME.base_typ_as_vale_type t
  = let open ME in
    match t with
    | TUInt8   -> UInt8.v x
    | TUInt16  -> UInt16.v x
    | TUInt32  -> UInt32.v x
    | TUInt64  -> UInt64.v x
    | TUInt128 -> x

let nat_to_uint_seq_t
      (t:ME.base_typ)
      (b:Seq.seq (ME.base_typ_as_vale_type t))
    : Seq.seq (base_typ_as_type t)
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> nat_to_uint t (Seq.index b i))


let uint_to_nat_seq_t
      (t:ME.base_typ)
      (b:Seq.seq (base_typ_as_type t))
    : Seq.seq (ME.base_typ_as_vale_type t)
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> uint_to_nat t (Seq.index b i))


[@__reduce__]
let view_of_base_typ (t:ME.base_typ)
  : UV.view UInt8.t (base_typ_as_type t)
  = let open ME in
    match t with
    | TUInt8 -> Vale.Interop.Views.up_view8
    | TUInt16 -> Vale.Interop.Views.up_view16
    | TUInt32 -> Vale.Interop.Views.up_view32
    | TUInt64 -> Vale.Interop.Views.up_view64
    | TUInt128 -> Vale.Interop.Views.up_view128

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////
let hprop = HS.mem -> prop
let hsprop = HS.mem -> VS.vale_state -> prop
module IB = Vale.Interop.Base

[@__reduce__]
let mem_correspondence_1
      (src t:ME.base_typ)
      (x:IB.buf_t src t)
      (h:HS.mem)
      (s:VS.vale_state) =
  let y = as_vale_buffer x in
  let db = get_downview x in
  DV.length_eq db;
  Seq.equal
    (nat_to_uint_seq_t t (ME.buffer_as_seq (ME.get_vale_heap s.VS.vs_heap) y))
    (UV.as_seq h (UV.mk_buffer db (view_of_base_typ t)))

[@__reduce__]
let mem_imm_correspondence_1
      (src t:ME.base_typ)
      (x:IB.ibuf_t src t)
      (h:HS.mem)
      (s:VS.vale_state) =
  let y = as_vale_immbuffer x in
  let db = get_downview x in
  DV.length_eq db;
  Seq.equal
    (nat_to_uint_seq_t t (ME.buffer_as_seq (ME.get_vale_heap s.VS.vs_heap) y))
    (UV.as_seq h (UV.mk_buffer db (view_of_base_typ t)))

[@__reduce__]
let rec mem_correspondence (args:list arg) : hsprop =
  match args with
  | [] -> fun h s -> True
  | hd :: tl ->
    let (| tag, x |) = hd in
    match tag with
    | TD_Buffer src bt _ ->
      fun h s ->
        mem_correspondence_1 src bt x h s /\
        mem_correspondence tl h s
    | TD_ImmBuffer src bt _ ->
      fun h s ->
        mem_imm_correspondence_1 src bt x h s /\
        mem_correspondence tl h s
    | TD_Base _ ->
      mem_correspondence tl

[@__reduce__]
let arg_as_nat64 (a:arg) (s:VS.vale_state) : GTot ME.nat64 =
  let (| tag, x |) = a in
  let open ME in
  match tag with
  | TD_Base TUInt8 ->
     UInt8.v x
  | TD_Base TUInt16 ->
     UInt16.v x
  | TD_Base TUInt32 ->
     UInt32.v x
  | TD_Base TUInt64 ->
     UInt64.v x
  | TD_Buffer src bt _ ->
     buffer_addr_is_nat64 (as_vale_buffer #src #bt x) s;
     ME.buffer_addr (as_vale_buffer #src #bt x) (ME.get_vale_heap s.VS.vs_heap)
  | TD_ImmBuffer src bt _ ->
     buffer_addr_is_nat64 (as_vale_immbuffer #src #bt x) s;
     ME.buffer_addr (as_vale_immbuffer #src #bt x) (ME.get_vale_heap s.VS.vs_heap)


[@__reduce__]
let rec register_args (max_arity:nat)
                      (arg_reg:IX64.arg_reg_relation max_arity)
                      (n:nat)
                      (args:list arg{List.Tot.length args = n}) : VSig.sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      fun s ->
         register_args max_arity arg_reg (n - 1) tl s /\
        (if n > max_arity then True // This arg is passed on the stack
         else VS.eval_reg_64 (arg_reg.IX64.of_arg (n - 1)) s == arg_as_nat64 hd s)

[@__reduce__]
let rec stack_args (max_arity:nat)
                   (n:nat)
                   (args:list arg{List.Tot.length args = n})
                   : VSig.sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      fun s ->
        stack_args max_arity (n - 1) tl s /\
        (if n <= max_arity then True // This arg is passed in registers
         else
           let ptr = ((n - max_arity) - 1) * 8
             + (if IA.win then 32 else 0)
             + 8
             + VS.eval_reg_64 MS.rRsp s
           in
           SI.valid_stack_slot64 ptr s.VS.vs_stack MS.Public s.VS.vs_stackTaint /\
           SI.load_stack64 ptr s.VS.vs_stack == arg_as_nat64 hd s)

[@__reduce__]
let taint_hyp_arg (m:ME.vale_heap) (tm:MS.memTaint_t) (a:arg) =
   let (| tag, x |) = a in
    match tag with
    | TD_Buffer src TUInt64 {taint=tnt} ->
      ME.valid_taint_buf64
         (as_vale_buffer #src #TUInt64 x)
         m
         tm
         tnt
    | TD_Buffer src TUInt128 {taint=tnt} ->
      ME.valid_taint_buf128
         (as_vale_buffer #src #TUInt128 x)
         m
         tm
         tnt
    | TD_ImmBuffer src TUInt64 {taint=tnt} ->
      ME.valid_taint_buf64
         (as_vale_immbuffer #src #TUInt64 x)
         m
         tm
         tnt
    | TD_ImmBuffer src TUInt128 {taint=tnt} ->
      ME.valid_taint_buf128
         (as_vale_immbuffer #src #TUInt128 x)
         m
         tm
         tnt
    | _ ->
      True

[@__reduce__]
let taint_hyp (args:list arg) : VSig.sprop =
  fun s0 -> BigOps.big_and' (taint_hyp_arg (ME.get_vale_heap s0.VS.vs_heap) (full_heap_taint s0.VS.vs_heap)) args

[@__reduce__]
let vale_pre_hyp
  (#max_arity:nat)
  (#arg_reg:IX64.arg_reg_relation max_arity)
  (args:IX64.arg_list)
  : VSig.sprop =
    fun s0 ->
      V.state_inv s0 /\
      ME.is_initial_heap s0.VS.vs_heap.vf_layout s0.VS.vs_heap.vf_heap /\
      ME.get_heaplet_id s0.VS.vs_heap.vf_heap == None /\
      VSig.disjoint_or_eq args /\
      VSig.readable args (ME.get_vale_heap s0.VS.vs_heap) /\
      register_args max_arity arg_reg (List.length args) args s0 /\
      stack_args max_arity (List.length args) args s0 /\
      VS.eval_reg_64 MS.rRsp s0 == SI.init_rsp s0.VS.vs_stack /\
      taint_hyp args s0

[@__reduce__]
let to_low_pre
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (pre:VSig.vale_pre_tl [])
    (args:IX64.arg_list)
    (hs_mem:mem_roots args)
  : prop =
  (forall (s0:V.va_state).
    V.va_get_ok s0 /\
    vale_pre_hyp #max_arity #arg_reg args s0 /\
    mem_correspondence args hs_mem s0 ==>
    elim_nil pre s0)

[@__reduce__]
let to_low_post
    (post:VSig.vale_post_tl [])
    (args:list arg)
    (hs_mem0:mem_roots args)
    (res:UInt64.t)
    (hs_mem1:mem_roots args)
  : prop =
  let open V in
  B.modifies (loc_modified_args args) hs_mem0 hs_mem1 /\
  (exists
    (s0:va_state)
    (s1:va_state)
    (f:va_fuel).
       mem_correspondence args hs_mem0 s0 /\
       mem_correspondence args hs_mem1 s1 /\
       UInt64.v res == VS.eval_reg_64 MS.rRax s1 /\
       elim_nil post s0 s1 f)

[@__reduce__]
let create_initial_vale_state
       (#max_arity:nat)
       (#arg_reg:IX64.arg_reg_relation max_arity)
       (args:IX64.arg_list)
  : IX64.state_builder_t max_arity args V.vale_state_with_inv =
  fun h0 ->
    let (t_state, mem) = IX64.create_initial_trusted_state max_arity arg_reg args h0 in
    let open VS in
    { vs_ok = true;
      vs_regs = Vale.X64.Regs.of_fun t_state.BS.ms_regs;
      vs_flags = Vale.X64.Flags.of_fun IA.init_flags;
      vs_heap = create_initial_vale_full_heap mem (heap_taint t_state.BS.ms_heap);
      vs_stack = as_vale_stack t_state.BS.ms_stack;
      vs_stackTaint = t_state.BS.ms_stackTaint;
    }
