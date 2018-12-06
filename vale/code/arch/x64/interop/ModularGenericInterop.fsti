module GenericInterop2

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
open X64.Vale.StateLemmas
open X64.Vale.Lemmas
module TS = X64.Taint_Semantics_s
module ME = X64.Memory
module BS = X64.Bytes_Semantics_s
module IS = X64.Interop_s
module MM = X64.Memory
open X64.Interop_s

val get_hs (m:X64.Memory.mem) : HS.mem
val to_mem (m:ME.mem) : m':MM.mem{m === m'}
val to_memtaint (m:X64.Machine_s.memTaint_t) : m':MM.memtaint{m === m'}

[@reduce]
let initial_vale_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc va_state

[@reduce]
let create_initial_vale_state_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : GTot va_state =
  let t_state, mem = create_initial_trusted_state_core acc regs xmms taint h0 stack in
  { ok = true;
    regs = X64.Vale.Regs.of_fun (regs_with_stack regs stack);
    xmms = X64.Vale.Xmms.of_fun xmms;
    flags = 0; // REVIEW
    mem = to_mem mem;
    memTaint = to_memtaint TS.(t_state.memTaint) }

val lemma_create_initial_vale_state_core
    (acc:list b8)
    (regs:registers)
    (xmms:xmms_t)
    (taint:taint_map)
    (h0:HS.mem)
    (stack:b8{mem_roots_p h0 (stack::acc)})
  : Lemma
      (requires True)
      (ensures (
        let s = create_initial_vale_state_core acc regs xmms taint h0 stack in
        get_hs s.mem == h0
      ))
      [SMTPat (create_initial_vale_state_core acc regs xmms taint h0 stack)]

[@reduce]
let create_vale_initial_state_t (dom:list vale_type)
                                (acc:list b8)
    = n_dep_arrow
          dom
          (initial_vale_state_t dom acc)


[@reduce]
let elim_down_1 (hd:vale_type)
                (acc:list b8)
                (down:create_vale_initial_state_t [hd] acc)
                (x:vale_type_as_type hd)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::maybe_cons_buffer hd x acc)} -> GTot va_state =
    down x

[@reduce]
let elim_down_nil (acc:list b8)
                  (down:create_vale_initial_state_t [] acc)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::acc)} -> GTot va_state =
    down

[@reduce]
let elim_down_cons (hd:vale_type)
                   (tl:list vale_type)
                   (acc:list b8)
                   (down:create_vale_initial_state_t (hd::tl) acc)
                   (x:vale_type_as_type hd)
    : create_vale_initial_state_t tl (maybe_cons_buffer hd x acc) =
    elim_dep_arrow_cons hd tl down x

//////////////////////////////////////////////////////////////////////////////////////////
//vale_sig pre post: a template for a top-level signature provided by a vale function
//////////////////////////////////////////////////////////////////////////////////////////

[@reduce]
let vale_pre_tl (dom:list vale_type) =
    n_arrow dom (va_state -> stack_buffer -> prop)

[@reduce]
let vale_pre (dom:list vale_type) =
    code:va_code ->
    win:bool ->
    vale_pre_tl dom

[@reduce]
let vale_post_tl (dom:list vale_type) =
    n_arrow dom
            (s0:va_state -> sb:stack_buffer -> s1:va_state -> f:va_fuel -> prop)

[@reduce]
let vale_post (dom:list vale_type) =
    code:va_code ->
    win:bool ->
    vale_post_tl dom

let vale_save_reg (r:reg) (s0 s1:va_state) =
  eval_reg r s0 == eval_reg r s1

let vale_save_xmm (r:xmm) (s0 s1:va_state) =
  eval_xmm r s0 == eval_xmm r s1

let vale_calling_conventions (win:bool) (s0 s1:va_state) =
  vale_save_reg Rbx s0 s1 /\
  (win ==> vale_save_reg Rsi s0 s1) /\
  (win ==> vale_save_reg Rdi s0 s1) /\
  vale_save_reg Rbp s0 s1 /\
  (win ==> vale_save_reg Rsp s0 s1) /\ // TODO: also needed for !win
  vale_save_reg R12 s0 s1 /\
  vale_save_reg R13 s0 s1 /\
  vale_save_reg R14 s0 s1 /\
  vale_save_reg R15 s0 s1 /\
  (win ==>
    vale_save_xmm 6 s0 s1 /\
    vale_save_xmm 7 s0 s1 /\
    vale_save_xmm 8 s0 s1 /\
    vale_save_xmm 9 s0 s1 /\
    vale_save_xmm 10 s0 s1 /\
    vale_save_xmm 11 s0 s1 /\
    vale_save_xmm 12 s0 s1 /\
    vale_save_xmm 13 s0 s1 /\
    vale_save_xmm 14 s0 s1 /\
    vale_save_xmm 15 s0 s1
  ) /\
  s1.ok

let maybe_cons_buffer_fp
       (#t:vale_type)
       (x:vale_type_as_type t)
       (loc: ME.loc) =
    match t with
    | VT_Base _ -> loc
    | VT_Buffer bt -> ME.loc_union (ME.loc_buffer #(TBase bt) x) loc

[@reduce]
let rec vale_sig_tl (#dom:list vale_type)
                    (fp:ME.loc)
                    (code:va_code)
                    (win:bool)
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [] ->
      va_s0:va_state ->
      stack_b:stack_buffer ->
      Ghost (va_state & va_fuel)
            (requires (elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) ->
                       X64.Vale.Decls.eval_code code va_s0 f va_s1 /\
                       vale_calling_conventions win va_s0 va_s1 /\
                       elim_nil post va_s0 stack_b va_s1 f /\
                       ME.modifies fp va_s0.mem va_s1.mem))

    | hd::tl ->
      x:vale_type_as_type hd ->
      vale_sig_tl #tl (maybe_cons_buffer_fp x fp) code win (elim_1 pre x) (elim_1 post x)

[@reduce]
let elim_vale_sig_cons #code
                       (hd:vale_type)
                       (tl:list vale_type)
                       (fp:ME.loc)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl fp code win pre post)
    : x:vale_type_as_type hd
    -> vale_sig_tl (maybe_cons_buffer_fp x fp) code win (elim_1 pre x) (elim_1 post x)
    = v

[@reduce]
let vale_sig (#dom:list vale_type)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    code:va_code ->
    win:bool ->
    vale_sig_tl
      ME.loc_none
      code
      win
      (pre code win)
      (post code win)

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////

unfold let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%reduce];
     delta_only [`%VT_Buffer?;
                 `%Mkstate?.ok;
                 `%Mkstate?.regs;
                 `%Mkstate?.xmms;
                 `%Mkstate?.flags;
                 `%Mkstate?.mem;
                 `%BS.Mkstate?.ok;
                 `%BS.Mkstate?.regs;
                 `%BS.Mkstate?.xmms;
                 `%BS.Mkstate?.flags;
                 `%BS.Mkstate?.mem;
                 `%TS.MktraceState?.state;
                 `%TS.MktraceState?.trace;
                 `%TS.MktraceState?.memTaint;
                 `%FStar.FunctionalExtensionality.on_dom;
                 `%FStar.FunctionalExtensionality.on;
                 `%Interop.list_disjoint_or_eq;
                 `%Interop.list_live
                 ];
     primops;
     simplify]
     x

[@reduce]
unfold
let prestate_hyp
    (h0:HS.mem)
    (acc:list b8{disjoint_or_eq_l acc /\ live_l h0 acc})
    (push_h0:HS.mem)
    (alloc_push_h0:HS.mem)
    (b:b8)
  : Type0 =
  HS.fresh_frame h0 push_h0 /\
  M.modifies M.loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  normal (mem_roots_p alloc_push_h0 (b::acc))

module V = X64.Vale.Decls
module IA = Interop_assumptions
module VS = X64.Vale.State
let sprop = VS.state -> prop
let hprop = HS.mem -> prop
let hsprop = HS.mem -> VS.state -> prop

[@reduce]
let to_low_pre
    (pre:vale_pre_tl [])
    (args_disjointness:prop)
    (args_liveness:hprop)
    (arg_pre_hyp:sprop)
    (mem_correspondence:hsprop)
    (num_stack_slots:nat)
    (hs_mem:HS.mem)
  : prop =
  args_disjointness /\
  args_liveness hs_mem /\
  // LB.live hs_mem (to_b8 x0) /\ ok
  // LB.live hs_mem (to_b8 x1) /\ ok
  (forall
    (s0:V.va_state)
    (sb:stack_buffer).
    ( let open V in
      s0.ok /\
      arg_pre_hyp s0 /\
      mem_correspondence hs_mem s0 /\
//       low_assumptions hs_mem s0.VS.mem x0 x1 /\   length assumptions ok; but nat64 vs uint64 etc. to be resolved
//       M.buffer_readable s0.VS.mem x0 /\                       ok
//       M.buffer_readable s0.VS.mem x1 /\                       ok
// //      M.buffer_length sb >= num_stack_slots /\
//       M.locs_disjoint ([M.loc_buffer sb; M.loc_buffer x0; M.loc_buffer x1]) /\ ok
//       VS.eval_reg (register_of_arg_i IA.win 0) s0 == M.buffer_addr x0 s0.VS.mem /\ ok
//       VS.eval_reg (register_of_arg_i IA.win 1) s0 == M.buffer_addr x1 s0.VS.mem /\ ok
//       M.valid_taint_buf64 x0 s0.VS.mem s0.VS.memTaint Secret /\ // TODO: generalize this ok
//       M.valid_taint_buf64 x1 s0.VS.mem s0.VS.memTaint Secret /\ // TODO: generalize this ok
      V.valid_stack_slots s0.VS.mem (VS.eval_reg Rsp s0) sb num_stack_slots s0.VS.memTaint
      ) ==>
    elim_nil pre s0 sb)

[@reduce]
let to_low_post
    (post:vale_post_tl [])
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
    (sb:stack_buffer)
    (s1:va_state)
    (f:va_fuel).
       mem_correspondence hs_mem0 s0 /\
       mem_correspondence hs_mem1 s1 /\
       elim_nil post s0 sb s1 f)

//--------------------------------------------------------------------------------
/// Several internal forms that are also supposed to be normalized away during typechecking
/// DO NOT USE THESE DIRECTLY: use their counterparts marked "unfold" below
[@reduce]
let rec all_disjoint_from (a:B.loc) (l:list B.loc) =
  match l with
  | [] -> True
  | hd::tl -> B.loc_disjoint a hd /\ all_disjoint_from a tl

[@reduce]
let rec pairwise_disjoint (l:list B.loc) =
  match l with
  | [] -> True
  | hd::tl -> all_disjoint_from hd tl /\ pairwise_disjoint tl

let buf_t = a:Type & B.buffer a
module HS = FStar.HyperStack
[@reduce]
let rec all_live_buf (h:HS.mem) (l:list buf_t) =
  match l with
  | [] -> True
  | (|_, b|)::tl -> B.live h b /\ all_live_buf h tl

[@reduce]
let buf (#a:Type) (b:B.buffer a) : buf_t = (|a, b|)

[@reduce]
let rec loc_union_l' (l:list B.loc) : GTot B.loc =
  match l with
  | [] -> B.loc_none
  | hd::tl -> B.loc_union hd (loc_union_l' tl)

/// USE THESE WRAPPERS TO ENABLE NORMALIZATION AT TYPECHECKING TME
unfold
let all_live (h:HS.mem) (l:list buf_t) :GTot Type0 = normal (all_live_buf h l)

unfold
let all_disjoint (l:list B.loc) = normal (pairwise_disjoint l)

unfold
let loc_union_l (l:list B.loc) = normal (loc_union_l' l)

let view_n = function
  | TBase TUInt8 -> 1
  | TBase TUInt16 -> 2
  | TBase TUInt32 -> 4
  | TBase TUInt64 -> 8
  | TBase TUInt128 -> 16

let lowstar_buffer (t:typ) = b:B.buffer UInt8.t{B.length b % view_n t == 0}

let buffer_equiv (t:typ)
  : Lemma (ME.buffer t == lowstar_buffer t)
  = admit()

[@reduce]
let coerce (x:'a{'a == 'b}) : 'b = x

[@reduce]
let as_lowstar_buffer (#t:typ) (x:ME.buffer t)
  : Tot (lowstar_buffer t)
  = buffer_equiv t;
    coerce x

[@reduce]
let as_vale_buffer (#t:typ) (x:lowstar_buffer t)
  : Tot (b:ME.buffer t)
  = buffer_equiv t;
    coerce x

let vale_type_as_lowstar_type (t:vale_type) =
  match t with
  | VT_Buffer t -> lowstar_buffer (TBase t)
  | _ -> vale_type_as_type t

[@reduce]
let lowstar_to_vale (#t:vale_type) (x:vale_type_as_lowstar_type t)
  : vale_type_as_type t
  = match t with
    | VT_Buffer t -> as_vale_buffer #(TBase t) x
    | _ -> x

let lowstar_arg = (t:vale_type & vale_type_as_lowstar_type t)
let lowstar_args = i:list lowstar_arg{List.length i < max_arity IA.win}

[@reduce]
let mk_disjointness_pre (args:lowstar_args) =
  let rec aux (args:lowstar_args) (out:list B.loc) : prop =
    match args with
    | [] -> all_disjoint out
    | hd::tl ->
      match hd with
      | (| VT_Buffer bt, x |) ->
        aux tl (B.loc_buffer x::out)
      | _ -> aux tl out
  in
  aux [] []


[@reduce]
let mk_liveness_pre (args:lowstar_args) : hprop =
  let rec aux (args:lowstar_args) (out:hprop) : hprop =
    match args with
    | [] -> out
    | hd::tl ->
      match hd with
      | (| VT_Buffer bt, x |) ->
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

////////////////////////////////////////////////////////////////////////////////
// Vale analogs
////////////////////////////////////////////////////////////////////////////////

let nat_to_uint (t:base_typ{t <> TUInt128}) (x:ME.type_of_typ (TBase t))
  : IS.base_type_as_type t
  = match t with
    | TUInt8   -> UInt8.uint_to_t x
    | TUInt16  -> UInt16.uint_to_t x
    | TUInt32  -> UInt32.uint_to_t x
    | TUInt64  -> UInt64.uint_to_t x

let nat_to_uint_seq_t
      (t:base_typ{t <> TUInt128})
      (b:Seq.seq (ME.type_of_typ (TBase t)))
    : Seq.seq (IS.base_type_as_type t)
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> nat_to_uint t (Seq.index b i))
module LBV = LowStar.BufferView
let view_of_base_typ (t:base_typ{t <> TUInt128})
  : LBV.view UInt8.t (IS.base_type_as_type t)
  = match t with
    | TUInt8 -> Views.view8
    | TUInt16 -> Views.view16
    | TUInt32 -> Views.view32
    | TUInt64 -> Views.view64

let mem_correspondence_1
      (t:base_typ{t <> TUInt128})
      (x:lowstar_buffer (TBase t))
      (h:HS.mem)
      (s:VS.state) =
  let y = as_vale_buffer x in
  Seq.equal
    (nat_to_uint_seq_t t (ME.buffer_as_seq s.VS.mem y))
    (LBV.as_seq h (LBV.mk_buffer_view x (view_of_base_typ t)))

let rec mem_correspondence (args:lowstar_args) : hsprop =
  match args with
  | [] -> fun h s -> True
  | hd :: tl ->
    let (| tag, x |) = hd in
    match tag with
    | VT_Buffer bt ->
      assume (bt <> TUInt128);
      fun h s ->
        mem_correspondence_1 bt x h s /\
        mem_correspondence tl h s
    | _ ->
      mem_correspondence tl

[@reduce]
let mk_vale_disjointness (args:lowstar_args) : prop =
  let rec aux (args:lowstar_args) : GTot (list ME.loc) =
    match args with
    | [] -> []
    | hd::tl ->
      match hd with
      | (| VT_Buffer bt, x |) ->
        ME.loc_buffer (as_vale_buffer #(TBase bt) x) :: aux tl
      | _ -> aux tl
  in
  ME.locs_disjoint (aux args)

[@reduce]
let mk_readable (args:lowstar_args) : sprop =
  let rec aux (args:lowstar_args) (out:sprop) : sprop =
    match args with
    | [] -> out
    | hd::tl ->
      match hd with
      | (| VT_Buffer bt, x |) ->
        let out : sprop =
          fun s0 ->
            out s0 /\
            ME.buffer_readable VS.(s0.mem) (as_vale_buffer #(TBase bt) x)
        in
        aux tl out
      | _ ->
        aux tl out
  in
  aux [] (fun h -> True)

let buffer_addr_is_nat64 (#t:typ) (x:ME.buffer t) (s:VS.state) :
  Lemma (0 <= ME.buffer_addr x VS.(s.mem) /\ ME.buffer_addr x VS.(s.mem) < pow2 64) = admit()

let arg_as_nat64 (a:lowstar_arg) (s:VS.state) : GTot nat64 =
  let (| tag, x |) = a in
  match tag with
  | VT_Base TUInt8 ->
     UInt8.v x
  | VT_Base TUInt16 ->
     UInt16.v x
  | VT_Base TUInt32 ->
     UInt32.v x
  | VT_Base TUInt64 ->
     UInt64.v x
  | VT_Buffer bt ->
    let x = as_vale_buffer #(TBase bt) x in
    buffer_addr_is_nat64 x s;
    ME.buffer_addr x VS.(s.mem)

[@reduce]
let rec register_args (n:nat)
                      (args:lowstar_args{List.length args = n}) : sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      fun s ->
        register_args (n - 1) tl s /\
        VS.eval_reg (IS.register_of_arg_i IA.win n) s == arg_as_nat64 hd s

[@reduce]
let rec taint_hyp (args:lowstar_args) : sprop =
    match args with
    | [] -> (fun s -> True)
    | hd::tl ->
      let (| tag, x |) = hd in
      match tag with
      | VT_Buffer TUInt64 ->
        fun s0 ->
          ME.valid_taint_buf64
            (as_vale_buffer #(TBase TUInt64) x)
            s0.VS.mem
            s0.VS.memTaint Secret /\
          taint_hyp tl s0
      | VT_Buffer TUInt128 ->
        fun s0 ->
          ME.valid_taint_buf128
            (as_vale_buffer #(TBase TUInt128) x)
            s0.VS.mem
            s0.VS.memTaint Secret /\
          taint_hyp tl s0
      | _ ->
        taint_hyp tl

[@reduce]
let vale_pre_hyp (args:lowstar_args) : sprop =
    fun s0 ->
      mk_vale_disjointness args /\
      mk_readable args s0 /\
      register_args (List.length args) args s0 /\
      taint_hyp args s0

[@reduce]
let rec mk_modifies_loc (args:lowstar_args) : GTot B.loc =
    match args with
    | [] -> B.loc_none
    | hd::tl ->
      match hd with
      | (| VT_Buffer bt, x |) ->
        (B.loc_buffer x) `B.loc_union` (mk_modifies_loc tl)
      | _ ->
        mk_modifies_loc tl


[@reduce]
let rec as_lowstar_sig_tl
          (#dom:list vale_type)
          (args:lowstar_args{List.length args + List.length dom < max_arity IA.win})
          (num_stack_slots:nat)
          (pre:vale_pre_tl dom)
          (post:vale_post_tl dom)
    : Type =
    match dom with
    | [] ->
      let disjointness = mk_disjointness_pre args in
      let liveness = mk_liveness_pre args in
      let vale_pre_hyp = vale_pre_hyp args in
      let mem_corr = mem_correspondence args in
      unit ->
      Stack unit
        (requires (to_low_pre pre disjointness liveness vale_pre_hyp mem_corr num_stack_slots))
        (ensures (to_low_post post (mk_modifies_loc args) liveness mem_corr))

    | hd::tl ->
      x:vale_type_as_lowstar_type hd ->
      as_lowstar_sig_tl
        #tl
        ((| hd, x |)::args)
        num_stack_slots
        (elim_1 pre (lowstar_to_vale x))
        (elim_1 post (lowstar_to_vale x))


[@reduce]
let as_lowstar_sig
       (c:va_code)
       (dom:list vale_type{List.length dom < max_arity IA.win})
       (num_stack_slots:nat)
       (pre: vale_pre dom)
       (post: vale_post dom) =
    as_lowstar_sig_tl
      #dom
      []
      num_stack_slots
      (pre c win)
      (post c win)

val wrap
    (code:V.va_code)
    (dom:list vale_type{List.length dom < max_arity IA.win})
    (num_stack_slots:nat)
    (pre:vale_pre dom)
    (post:vale_post dom)
    (v:vale_sig pre post)
  : as_lowstar_sig code dom num_stack_slots pre post
