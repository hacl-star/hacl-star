module Vale.AsLowStar.LowStarSig
open X64.MemoryAdapters
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig

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

let nat_to_uint_seq_t
      (t:ME.base_typ)
      (b:Seq.seq (ME.base_typ_as_vale_type t))
    : Seq.seq (base_typ_as_type t)
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> nat_to_uint t (Seq.index b i))

[@__reduce__]
let view_of_base_typ (t:ME.base_typ)
  : BV.view UInt8.t (base_typ_as_type t)
  = let open ME in
    match t with
    | TUInt8 -> Views.view8
    | TUInt16 -> Views.view16
    | TUInt32 -> Views.view32
    | TUInt64 -> Views.view64
    | TUInt128 -> Views.view128

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////
let hprop = HS.mem -> prop
let hsprop = HS.mem -> VS.state -> prop
module IB = Interop.Base

[@__reduce__]
let mem_correspondence_1
      (t:ME.base_typ)
      (x:IB.buf_t t)
      (h:HS.mem)
      (s:VS.state) =
  let y = as_vale_buffer x in
  Seq.equal
    (nat_to_uint_seq_t t (ME.buffer_as_seq s.VS.mem y))
    (BV.as_seq h (BV.mk_buffer_view x (view_of_base_typ t)))

[@__reduce__]
let rec mem_correspondence (args:list arg) : hsprop =
  match args with
  | [] -> fun h s -> True
  | hd :: tl ->
    let (| tag, x |) = hd in
    match tag with
    | TD_Buffer bt _ ->
      fun h s ->
        mem_correspondence_1 bt x h s /\
        mem_correspondence tl h s
    | _ ->
      mem_correspondence tl

let buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.state) :
  Lemma (0 <= ME.buffer_addr x VS.(s.mem) /\ ME.buffer_addr x VS.(s.mem) < pow2 64) = admit()

[@__reduce__]
let arg_as_nat64 (a:arg) (s:VS.state) : GTot ME.nat64 =
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
  | TD_Buffer bt _ ->
     buffer_addr_is_nat64 (as_vale_buffer #bt x) s;
     ME.buffer_addr (as_vale_buffer #bt x) VS.(s.mem)

[@__reduce__]
let rec register_args (n:nat)
                      (args:IX64.arity_ok arg{List.length args = n}) : VSig.sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      fun s ->
        register_args (n - 1) tl s /\
        VS.eval_reg (IX64.register_of_arg_i (n - 1)) s == arg_as_nat64 hd s

[@__reduce__]
let rec taint_hyp (args:list arg) : VSig.sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      let (| tag, x |) = hd in
      match tag with
      | TD_Buffer TUInt64 _ ->
        fun s0 ->
          ME.valid_taint_buf64
            (as_vale_buffer #TUInt64 x)
            s0.VS.mem
            s0.VS.memTaint MS.Secret /\
          taint_hyp tl s0
      | TD_Buffer TUInt128 _ ->
        fun s0 ->
          ME.valid_taint_buf128
            (as_vale_buffer #TUInt128 x)
            s0.VS.mem
            s0.VS.memTaint MS.Secret /\
          taint_hyp tl s0
      | _ ->
        taint_hyp tl

[@__reduce__]
let vale_pre_hyp #n (sb:IX64.stack_buffer n) (args:IX64.arity_ok arg) : VSig.sprop =
    fun s0 ->
      let s_args = arg_of_sb sb :: args in
      VSig.disjoint_or_eq s_args /\
      VSig.readable s_args VS.(s0.mem) /\
      register_args (List.length args) args s0 /\
      taint_hyp args s0

[@__reduce__]
let to_low_pre
    (#n:IX64.max_slots)
    (pre:VSig.vale_pre_tl n [])
    (args:IX64.arity_ok arg)
    (hs_mem:mem_roots args)
  : prop =
  (forall (s0:V.va_state)
     (sb:IX64.stack_buffer n).
    V.va_get_ok s0 /\
    vale_pre_hyp sb args s0 /\
    mem_correspondence args hs_mem s0 /\
    V.valid_stack_slots s0.VS.mem (VS.eval_reg MS.Rsp s0) (as_vale_buffer sb) (n / 8) s0.VS.memTaint ==>
    elim_nil pre s0 sb)

[@__reduce__]
let to_low_post
    (#n:IX64.max_slots)
    (post:VSig.vale_post_tl n [])
    (args:list arg)
    (hs_mem0:mem_roots args)
    (_:unit)
    (hs_mem1:mem_roots args)
  : prop =
  let open V in
  B.modifies (loc_modified_args args) hs_mem0 hs_mem1 /\
  (exists
    (s0:va_state)
    (sb:IX64.stack_buffer n)
    (s1:va_state)
    (f:va_fuel).
       mem_correspondence args hs_mem0 s0 /\
       mem_correspondence args hs_mem1 s1 /\
       elim_nil post s0 sb s1 f)
