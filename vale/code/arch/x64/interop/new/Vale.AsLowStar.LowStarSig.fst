module Vale.AsLowStar.LowStarSig
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module IM = Interop.Mem
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig

assume //TODO: UInt128
val quad32_to_nat : ME.quad32 -> UInt.uint_t UInt128.n

assume //TODO: UInt128
val view128 : LowStar.BufferView.view UInt8.t UInt128.t

let nat_to_uint (t:ME.base_typ) (x:ME.type_of_typ (ME.TBase t))
  : base_typ_as_type t
  = let open ME in
    match t with
    | TUInt8   -> UInt8.uint_to_t x
    | TUInt16  -> UInt16.uint_to_t x
    | TUInt32  -> UInt32.uint_to_t x
    | TUInt64  -> UInt64.uint_to_t x
    | TUInt128  -> UInt128.uint_to_t (quad32_to_nat x)

let nat_to_uint_seq_t
      (t:ME.base_typ)
      (b:Seq.seq (ME.type_of_typ (ME.TBase t)))
    : Seq.seq (base_typ_as_type t)
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> nat_to_uint t (Seq.index b i))

let view_of_base_typ (t:ME.base_typ)
  : BV.view UInt8.t (base_typ_as_type t)
  = let open ME in
    match t with
    | TUInt8 -> Views.view8
    | TUInt16 -> Views.view16
    | TUInt32 -> Views.view32
    | TUInt64 -> Views.view64
    | TUInt128 -> view128

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////
let sprop = VS.state -> prop
let hprop = HS.mem -> prop
let hsprop = HS.mem -> VS.state -> prop

[@__reduce__]
let mem_correspondence_1
      (t:ME.base_typ)
      (x:lowstar_buffer (ME.TBase t))
      (h:HS.mem)
      (s:VS.state) =
  let y = as_vale_buffer x in
  assume (t <> ME.TUInt128); //TODO: UInt128
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
    | TD_Buffer bt ->
      fun h s ->
        mem_correspondence_1 bt x h s /\
        mem_correspondence tl h s
    | _ ->
      mem_correspondence tl

[@__reduce__]
let mk_vale_disjointness (args:list arg) : prop =
  let rec aux (args:list arg) : GTot (list ME.loc) =
    match args with
    | [] -> []
    | hd::tl ->
      match hd with
      | (| TD_Buffer bt, x |) ->
        ME.loc_buffer (as_vale_buffer #(ME.TBase bt) x) :: aux tl
      | _ -> aux tl
  in
  ME.locs_disjoint (aux args)

[@__reduce__]
let mk_readable (args:list arg) : sprop =
  let rec aux (args:list arg) (out:sprop) : sprop =
    match args with
    | [] -> out
    | hd::tl ->
      match hd with
      | (| TD_Buffer bt, x |) ->
        let out : sprop =
          fun s0 ->
            out s0 /\
            ME.buffer_readable VS.(s0.mem) (as_vale_buffer #(ME.TBase bt) x)
        in
        aux tl out
      | _ ->
        aux tl out
  in
  aux [] (fun h -> True)

[@__reduce__]
let rec register_args (n:nat)
                      (args:IX64.arity_ok arg{List.length args = n}) : sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      fun s ->
        register_args (n - 1) tl s /\
        VS.eval_reg (IX64.register_of_arg_i n) s == IX64.arg_as_nat64 hd

[@__reduce__]
let rec taint_hyp (args:list arg) : sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      let (| tag, x |) = hd in
      match tag with
      | TD_Buffer ME.TUInt64 ->
        fun s0 ->
          ME.valid_taint_buf64
            (as_vale_buffer #ME.(TBase TUInt64) x)
            s0.VS.mem
            s0.VS.memTaint MS.Secret /\
          taint_hyp tl s0
      | TD_Buffer ME.TUInt128 ->
        fun s0 ->
          ME.valid_taint_buf128
            (as_vale_buffer #ME.(TBase TUInt128) x)
            s0.VS.mem
            s0.VS.memTaint MS.Secret /\
          taint_hyp tl s0
      | _ ->
        taint_hyp tl

[@__reduce__]
let rec mk_modifies_loc (args:list arg) : GTot B.loc =
    match args with
    | [] -> B.loc_none
    | hd::tl ->
      match hd with
      | (| TD_Buffer bt, x |) ->
        (B.loc_buffer x) `B.loc_union` (mk_modifies_loc tl)
      | _ ->
        mk_modifies_loc tl

[@__reduce__]
let vale_pre_hyp (args:IX64.arity_ok arg) : sprop =
    fun s0 ->
      mk_vale_disjointness args /\
      mk_readable args s0 /\
      register_args (List.length args) args s0 /\
      taint_hyp args s0

[@__reduce__]
let to_low_pre
    (pre:VSig.vale_pre_tl [])
    (args:IX64.arity_ok arg)
    (num_stack_slots:nat)
    (hs_mem:mem_roots args)
  : prop =
  (forall (s0:V.va_state)
     (sb:IX64.stack_buffer).
    s0.VS.ok /\
    vale_pre_hyp args s0 /\
    mem_correspondence args hs_mem s0 /\
    V.valid_stack_slots s0.VS.mem (VS.eval_reg MS.Rsp s0) (as_vale_buffer sb) num_stack_slots s0.VS.memTaint ==>
    elim_nil pre s0 sb)

[@__reduce__]
let to_low_post
    (post:VSig.vale_post_tl [])
    (args:list arg)
    (hs_mem0:mem_roots args)
    (_:unit)
    (hs_mem1:mem_roots args)
  : prop =
  let open V in
  // REVIEW: it would be more flexible to let low_assumptions/post take care of modifies:
  B.modifies (loc_args args) hs_mem0 hs_mem1 /\
  (exists
    (s0:va_state)
    (sb:IX64.stack_buffer)
    (s1:va_state)
    (f:va_fuel).
       mem_correspondence args hs_mem0 s0 /\
       mem_correspondence args hs_mem1 s1 /\
       elim_nil post s0 sb s1 f)
