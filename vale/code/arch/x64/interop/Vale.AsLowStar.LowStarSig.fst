module Vale.AsLowStar.LowStarSig
open Vale.AsLowStar.Signature
open Vale.AsLowStar.Util
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module IA = Interop_assumptions
module IS = X64.Interop_s
module ME = X64.Memory
module MS = X64.Machine_s
module V = X64.Vale.Decls
module VS = X64.Vale.State
module VSig = Vale.AsLowStar.ValeSig


[@IS.reduce]
let vale_type_as_lowstar_type (t:IS.vale_type) =
  match t with
  | IS.VT_Buffer t -> lowstar_buffer (ME.TBase t)
  | _ -> IS.vale_type_as_type t

[@IS.reduce]
let lowstar_to_vale (#t:IS.vale_type) (x:vale_type_as_lowstar_type t)
  : IS.vale_type_as_type t
  = match t with
    | IS.VT_Buffer t -> as_vale_buffer #(ME.TBase t) x
    | _ -> x

let lowstar_arg = t:IS.vale_type & vale_type_as_lowstar_type t
let lowstar_args = i:list lowstar_arg{List.length i < IS.max_arity IA.win}

let arg_as_nat64 (a:lowstar_arg) (s:VS.state) : GTot ME.nat64 =
  let (| tag, x |) = a in
  let open ME in
  match tag with
  | IS.VT_Base TUInt8 ->
     UInt8.v x
  | IS.VT_Base TUInt16 ->
     UInt16.v x
  | IS.VT_Base TUInt32 ->
     UInt32.v x
  | IS.VT_Base TUInt64 ->
     UInt64.v x
  | IS.VT_Buffer bt ->
    let x = as_vale_buffer #(TBase bt) x in
    buffer_addr_is_nat64 x s;
    ME.buffer_addr x VS.(s.mem)

let nat_to_uint (t:ME.base_typ{t <> ME.TUInt128}) (x:ME.type_of_typ (ME.TBase t))
  : IS.base_type_as_type t
  = let open ME in
    match t with
    | TUInt8   -> UInt8.uint_to_t x
    | TUInt16  -> UInt16.uint_to_t x
    | TUInt32  -> UInt32.uint_to_t x
    | TUInt64  -> UInt64.uint_to_t x

let nat_to_uint_seq_t
      (t:ME.base_typ{t <> ME.TUInt128})
      (b:Seq.seq (ME.type_of_typ (ME.TBase t)))
    : Seq.seq (IS.base_type_as_type t)
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> nat_to_uint t (Seq.index b i))

let view_of_base_typ (t:ME.base_typ{t <> ME.TUInt128})
  : BV.view UInt8.t (IS.base_type_as_type t)
  = let open ME in
    match t with
    | TUInt8 -> Views.view8
    | TUInt16 -> Views.view16
    | TUInt32 -> Views.view32
    | TUInt64 -> Views.view64

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////
let sprop = VS.state -> prop
let hprop = HS.mem -> prop
let hsprop = HS.mem -> VS.state -> prop

[@IS.reduce]
let to_low_pre
    (pre:VSig.vale_pre_tl [])
    (args_disjointness:prop)
    (args_liveness:hprop)
    (arg_pre_hyp:sprop)
    (mem_correspondence:hsprop)
    (num_stack_slots:nat)
    (hs_mem:HS.mem)
  : prop =
  args_disjointness /\
  args_liveness hs_mem /\
  (forall (s0:V.va_state)
     (sb:IS.stack_buffer).
    s0.VS.ok /\
    arg_pre_hyp s0 /\
    mem_correspondence hs_mem s0 /\
    V.valid_stack_slots s0.VS.mem (VS.eval_reg MS.Rsp s0) sb num_stack_slots s0.VS.memTaint ==>
    IS.elim_nil pre s0 sb)

[@IS.reduce]
let to_low_post
    (post:VSig.vale_post_tl [])
    (args_fp:B.loc)
    (args_liveness:hprop)
    (mem_correspondence: hsprop)
    (hs_mem0:HS.mem)
    (_:unit)
    (hs_mem1:HS.mem)
  : prop =
  let open V in
  // REVIEW: it would be more flexible to let low_assumptions/post take care of modifies:
  B.modifies args_fp hs_mem0 hs_mem0 /\
  args_liveness hs_mem1 /\
  (exists
    (s0:va_state)
    (sb:IS.stack_buffer)
    (s1:va_state)
    (f:va_fuel).
       mem_correspondence hs_mem0 s0 /\
       mem_correspondence hs_mem1 s1 /\
       IS.elim_nil post s0 sb s1 f)

[@IS.reduce]
let mk_disjointness_pre (args:lowstar_args) =
  let rec aux (args:lowstar_args) (out:list B.loc) : prop =
    match args with
    | [] -> all_disjoint out
    | hd::tl ->
      match hd with
      | (| IS.VT_Buffer bt, x |) ->
        aux tl (B.loc_buffer x::out)
      | _ -> aux tl out
  in
  aux [] []

[@IS.reduce]
let mk_liveness_pre (args:lowstar_args) : hprop =
  let rec aux (args:lowstar_args) (out:hprop) : hprop =
    match args with
    | [] -> out
    | hd::tl ->
      match hd with
      | (| IS.VT_Buffer bt, x |) ->
        let out : hprop =
          fun h0 ->
            out h0 /\
            B.live h0 x
        in
        aux tl out
      | _ ->
        aux tl out
  in
  aux [] (fun h -> True)

[@IS.reduce]
let mem_correspondence_1
      (t:ME.base_typ{t <> ME.TUInt128})
      (x:lowstar_buffer (ME.TBase t))
      (h:HS.mem)
      (s:VS.state) =
  let y = as_vale_buffer x in
  Seq.equal
    (nat_to_uint_seq_t t (ME.buffer_as_seq s.VS.mem y))
    (BV.as_seq h (BV.mk_buffer_view x (view_of_base_typ t)))

[@IS.reduce]
let rec mem_correspondence (args:lowstar_args) : hsprop =
  match args with
  | [] -> fun h s -> True
  | hd :: tl ->
    let (| tag, x |) = hd in
    match tag with
    | IS.VT_Buffer bt ->
      assume (bt <> ME.TUInt128);
      fun h s ->
        mem_correspondence_1 bt x h s /\
        mem_correspondence tl h s
    | _ ->
      mem_correspondence tl

[@IS.reduce]
let mk_vale_disjointness (args:lowstar_args) : prop =
  let rec aux (args:lowstar_args) : GTot (list ME.loc) =
    match args with
    | [] -> []
    | hd::tl ->
      match hd with
      | (| IS.VT_Buffer bt, x |) ->
        ME.loc_buffer (as_vale_buffer #(ME.TBase bt) x) :: aux tl
      | _ -> aux tl
  in
  ME.locs_disjoint (aux args)

[@IS.reduce]
let mk_readable (args:lowstar_args) : sprop =
  let rec aux (args:lowstar_args) (out:sprop) : sprop =
    match args with
    | [] -> out
    | hd::tl ->
      match hd with
      | (| IS.VT_Buffer bt, x |) ->
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

[@IS.reduce]
let rec register_args (n:nat)
                      (args:lowstar_args{List.length args = n}) : sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      fun s ->
        register_args (n - 1) tl s /\
        VS.eval_reg (IS.register_of_arg_i IA.win n) s == arg_as_nat64 hd s

[@IS.reduce]
let rec taint_hyp (args:lowstar_args) : sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      let (| tag, x |) = hd in
      match tag with
      | IS.VT_Buffer ME.TUInt64 ->
        fun s0 ->
          ME.valid_taint_buf64
            (as_vale_buffer #ME.(TBase TUInt64) x)
            s0.VS.mem
            s0.VS.memTaint MS.Secret /\
          taint_hyp tl s0
      | IS.VT_Buffer ME.TUInt128 ->
        fun s0 ->
          ME.valid_taint_buf128
            (as_vale_buffer #ME.(TBase TUInt128) x)
            s0.VS.mem
            s0.VS.memTaint MS.Secret /\
          taint_hyp tl s0
      | _ ->
        taint_hyp tl

[@IS.reduce]
let rec mk_modifies_loc (args:lowstar_args) : GTot B.loc =
    match args with
    | [] -> B.loc_none
    | hd::tl ->
      match hd with
      | (| IS.VT_Buffer bt, x |) ->
        (B.loc_buffer x) `B.loc_union` (mk_modifies_loc tl)
      | _ ->
        mk_modifies_loc tl

[@IS.reduce]
let vale_pre_hyp (args:lowstar_args) : sprop =
    fun s0 ->
      mk_vale_disjointness args /\
      mk_readable args s0 /\
      register_args (List.length args) args s0 /\
      taint_hyp args s0

[@IS.reduce]
let rec as_lowstar_sig_tl
          (#dom:list IS.vale_type)
          (args:lowstar_args{List.length args + List.length dom < IS.max_arity IA.win})
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl dom)
          (post:VSig.vale_post_tl dom)
    : Type =
    let open FStar.HyperStack.ST in
    match dom with
    | [] ->
      let liveness = mk_liveness_pre args in
      let mem_corr = mem_correspondence args in
      unit ->
      Stack unit
        (requires (to_low_pre pre (mk_disjointness_pre args) liveness (vale_pre_hyp args) mem_corr num_stack_slots))
        (ensures (to_low_post post (mk_modifies_loc args) liveness mem_corr))

    | hd::tl ->
      x:vale_type_as_lowstar_type hd ->
      as_lowstar_sig_tl
        #tl
        ((| hd, x |)::args)
        num_stack_slots
        (IS.elim_1 pre (lowstar_to_vale x))
        (IS.elim_1 post (lowstar_to_vale x))

[@IS.reduce]
let as_lowstar_sig
       (c:V.va_code)
       (dom:sig_arity_ok)
       (num_stack_slots:nat)
       (pre: VSig.vale_pre dom)
       (post: VSig.vale_post dom) =
    as_lowstar_sig_tl
      #dom
      []
      num_stack_slots
      (pre c IA.win)
      (post c IA.win)
