module Vale.Interop.Base
open Vale.Arch.HeapTypes_s
include Vale.Interop.Types
include Vale.Interop.Heap_s
module MB = LowStar.Monotonic.Buffer
module DV = LowStar.BufferView.Down
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
include Vale.Arch.Heap
module BS = Vale.X64.Machine_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module MS = Vale.X64.Machine_s
module P = Vale.Def.Prop_s
module HS = FStar.HyperStack
module W = Vale.Def.Words_s
module L = FStar.List.Tot
open FStar.Mul

[@__reduce__]
let buf_t src t = b:B.buffer (base_typ_as_type src){(B.length b * view_n_unfold src) % view_n_unfold t = 0}

[@__reduce__]
let ibuf_t src t = b:IB.ibuffer (base_typ_as_type src){(B.length b * view_n_unfold src) % view_n_unfold t = 0}

let lemma_seq_neq_intro (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a)
 : Lemma (requires (Seq.length s1 =!= Seq.length s2))
         (ensures  (~ (Seq.equal s1 s2)))
 = ()

let default_v_of_typ (t:base_typ) : (base_typ_as_type t) = match t with
  | TUInt8 -> UInt8.uint_to_t 0
  | TUInt16 -> UInt16.uint_to_t 0
  | TUInt32 -> UInt32.uint_to_t 0
  | TUInt64 -> UInt64.uint_to_t 0
  | TUInt128 -> Vale.Def.Words_s.Mkfour #W.nat32 0 0 0 0


let imm_to_b8 (src:base_typ) (b:IB.ibuffer (base_typ_as_type src)) : GTot b8 =
  Buffer false b

let mut_to_b8 (src:base_typ) (b:B.buffer (base_typ_as_type src)) : GTot b8 =
  Buffer true b

[@__reduce__]
let coerce (x:'a{'a == 'b}) : 'b = x

////////////////////////////////////////////////////////////////////////////////

type buffer_qualifiers = {
  modified:bool;
  taint:taint;
  strict_disjointness:bool
}

[@__reduce__]
let default_bq = {
  modified = true;
  taint = Secret;
  strict_disjointness = false
}

[@__reduce__]
let stack_bq = {
  modified = true;
  taint = Public;
  strict_disjointness = true
}

let valid_base_type = x:base_typ{x <> TUInt128}

//type descriptors
type td =
  | TD_Base of valid_base_type
  // The initial type of the buffer, and the final type we want in Vale
  | TD_Buffer : base_typ -> base_typ -> buffer_qualifiers -> td
  | TD_ImmBuffer : base_typ -> base_typ -> buffer_qualifiers -> td

unfold
let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%__reduce__; `%BigOps.__reduce__];
     delta_only [`%TD_Buffer?;
                 `%BS.Mkmachine_state?.ms_ok;
                 `%BS.Mkmachine_state?.ms_regs;
                 `%BS.Mkmachine_state?.ms_flags;
                 `%BS.Mkmachine_state?.ms_heap;
                 `%BS.Mkmachine_state?.ms_stack;
                 `%BS.Mkmachine_state?.ms_stackTaint;
                 `%BS.Mkmachine_state?.ms_trace;
                 `%FStar.FunctionalExtensionality.on_dom;
                 `%FStar.FunctionalExtensionality.on;
                 `%List.Tot.fold_right_gtot;
                 `%List.Tot.map_gtot;
                 `%List.Tot.length;
                 `%fst;
                 `%snd;
                 `%Mktuple2?._1;
                 `%Mktuple2?._2
                 ];
     primops;
     simplify]
     x

////////////////////////////////////////////////////////////////////////////////
#set-options "--initial_ifuel 1"

[@__reduce__]
let td_as_type : td -> Type =
  function
  | TD_Base bt -> base_typ_as_type bt
  | TD_Buffer src bt _ -> buf_t src bt
  | TD_ImmBuffer src bt _ -> ibuf_t src bt

let arg = t:td & td_as_type t

////////////////////////////////////////////////////////////////////////////////
// n_arrow: Arrows with a generic number of vale types as the domain
//          and a result type `codom` that does not depend on the domain
////////////////////////////////////////////////////////////////////////////////
[@(unifier_hint_injective) (__reduce__)]
let rec n_arrow (dom:list td) (codom:Type) =
  match dom with
  | [] -> codom
  | hd::tl -> td_as_type hd -> n_arrow tl codom

[@(unifier_hint_injective) (__reduce__)]
let arr (dom:Type) (codom:Type) = dom -> codom

[@__reduce__]
let elim_1 (#dom:list td{Cons? dom})
           (#r:Type)
           (f:n_arrow dom r)
    : td_as_type (Cons?.hd dom) -> n_arrow (Cons?.tl dom) r =
    f

[@__reduce__]
let elim_nil (#dom:list td{Nil? dom})
           (#r:Type)
           (f:n_arrow dom r)
    : r =
    f

[@__reduce__]
let intro_n_arrow_nil (a:Type) (x:a)
  : n_arrow [] a
  = x

[@__reduce__]
let intro_n_arrow_cons (hd:td) (b:Type) (tl:list td)
                       (x:td_as_type hd -> n_arrow tl b)
  : n_arrow (hd::tl) b
  = x

////////////////////////////////////////////////////////////////////////////////
// n_dep_arrow: Arrows with a generic number of vale types as the domain
//              and a result type codom that depends on the domain
////////////////////////////////////////////////////////////////////////////////
[@(unifier_hint_injective) (__reduce__)]
let rec n_dep_arrow (dom:list td) (codom: n_arrow dom Type) =
  match dom with
  | [] -> codom
  | hd::tl -> x:td_as_type hd -> n_dep_arrow tl (elim_1 codom x)

[@__reduce__]
let intro_dep_arrow_nil (b:Type)
                        (f:b)
  : n_dep_arrow [] b
  = f

[@__reduce__]
let intro_dep_arrow_1 (a:td)
                      (b:n_arrow [a] Type)
                      (f:(x:td_as_type a -> elim_1 b x))
  : n_dep_arrow [a] b
  = f

[@__reduce__]
let intro_dep_arrow_cons (hd:td)
                         (tl:list td)
                         (b: n_arrow (hd::tl) Type)
                         (f: (x:td_as_type hd -> n_dep_arrow tl (elim_1 b x)))
  : n_dep_arrow (hd::tl) b
  = f

[@__reduce__]
let elim_dep_arrow_nil (#codom:n_arrow [] Type)
                       (f:n_dep_arrow [] codom)
    : elim_nil codom
   = f

[@__reduce__]
let elim_dep_arrow_cons (hd:td)
                        (tl:list td)
                        (#codom:n_arrow (hd::tl) Type)
                        (f:n_dep_arrow (hd::tl) codom)
    : x:td_as_type hd ->
      n_dep_arrow tl (elim_1 codom x)
   = f

//Just a small test function to see how these coercions work
let __test : n_dep_arrow [TD_Base TUInt8] (fun (x:UInt8.t) -> y:UInt8.t{x == y}) =
  fun (x:UInt8.t) -> intro_dep_arrow_nil (y:UInt8.t{x == y}) x
////////////////////////////////////////////////////////////////////////////////

[@__reduce__]
let disjoint_not_eq
  (#src1 #src2:base_typ)
  (#rel1 #rrel1:MB.srel (base_typ_as_type src1))
  (#rel2 #rrel2:MB.srel (base_typ_as_type src2))
  (x:MB.mbuffer (base_typ_as_type src1) rel1 rrel1)
  (y:MB.mbuffer (base_typ_as_type src2) rel2 rrel2) =
    B.loc_disjoint (B.loc_buffer x) (B.loc_buffer y) /\
    ~ (src1 == src2 /\ rel1 == rel2 /\ rrel1 == rrel2 /\ x == y)

[@__reduce__]
let disjoint_or_eq_1 (a:arg) (b:arg) =
    match a, b with
    | (| TD_Buffer _ _ {strict_disjointness=true}, xb |), (| TD_Buffer _ _ _, yb |)
    | (| TD_ImmBuffer _ _ {strict_disjointness=true}, xb |), (| TD_ImmBuffer _ _ _, yb |)
    | (| TD_Buffer _ _ _, xb |), (| TD_Buffer _ _ {strict_disjointness=true}, yb |)
    | (| TD_ImmBuffer _ _ _, xb |), (| TD_ImmBuffer _ _ {strict_disjointness=true}, yb |)
    // An immutable buffer and a trivial buffer should not be equal
    | (| TD_ImmBuffer _ _ _, xb |), (| TD_Buffer _ _ _, yb |)
    | (| TD_Buffer _ _ _, xb |), (| TD_ImmBuffer _ _ _, yb |) ->
      disjoint_not_eq xb yb
    | (| TD_Buffer srcx tx {taint=tntx}, xb |), (| TD_Buffer srcy ty {taint=tnty}, yb |)
    | (| TD_ImmBuffer srcx tx {taint=tntx}, xb |), (| TD_ImmBuffer srcy ty {taint=tnty}, yb |) ->
      disjoint_not_eq xb yb \/ (eq3 xb yb /\ tntx == tnty /\ tx == ty /\ srcx == srcy)
    | _ -> True

[@__reduce__]
let disjoint_or_eq (l:list arg) =
  BigOps.pairwise_and' disjoint_or_eq_1  l

[@__reduce__]
let live_arg (h:HS.mem) (x:arg) =
    match x with
    | (|TD_Buffer _ _ _, x|)
    | (|TD_ImmBuffer _ _ _, x|) -> B.live h x
    | (|TD_Base _, _ |) -> True

[@__reduce__]
let all_live (h:HS.mem) (bs:list arg) =
  BigOps.big_and' (live_arg h) bs

[@__reduce__]
let mem_roots_p (h0:HS.mem) (args:list arg) =
  disjoint_or_eq args /\
  all_live h0 args

[@__reduce__]
let mem_roots (args:list arg) =
    h0:HS.mem{ mem_roots_p h0 args }

[@__reduce__]
let args_b8 (args:list arg) : GTot (list b8) =
  let maybe_cons_buffer (x:arg) (args:list b8) : GTot (list b8) =
      match x with
      | (|TD_Buffer src _ _, x|) -> mut_to_b8 src x :: args
      | (|TD_ImmBuffer src _ _, x|) -> imm_to_b8 src x :: args
      | (|TD_Base _, _ |) -> args
  in
  List.Tot.fold_right_gtot args maybe_cons_buffer []

[@__reduce__]
let modified_arg_loc (x:arg) : GTot B.loc =
    match x with
    | (|TD_Buffer _ _ {modified=true}, x|) -> B.loc_buffer x
    | _ -> B.loc_none

[@__reduce__]
let loc_modified_args (args:list arg) : GTot B.loc =
    let maybe_union_loc (x:arg) l =
      match x with
      | (|TD_Buffer _ _ {modified=true}, x|) -> B.loc_union (B.loc_buffer x) l
      | _ -> l
    in
    List.Tot.fold_right_gtot args maybe_union_loc B.loc_none

[@__reduce__]
let arg_loc (x:arg) : GTot B.loc =
    match x with
    | (|TD_Buffer _ _ _, x|) -> B.loc_buffer x
    | (|TD_ImmBuffer _ _ _, x|) -> B.loc_buffer x
    | (|TD_Base _, _|) -> B.loc_none

[@__reduce__]
let loc_all_args (args:list arg) : GTot B.loc =
    let l = List.Tot.map_gtot arg_loc args in
    List.Tot.fold_right_gtot l B.loc_union B.loc_none

let all_live_cons (hd:arg) (tl:list arg) (h0:HS.mem)
  : Lemma
    (all_live h0 (hd :: tl) <==> (live_arg h0 hd /\ all_live h0 tl))
  = ()

let disjoint_or_eq_def (l:list arg)
  : Lemma (disjoint_or_eq l == BigOps.pairwise_and' disjoint_or_eq_1 l)
  = ()

let disjoint_or_eq_cons (hd:arg) (tl:list arg)
  : Lemma (disjoint_or_eq (hd::tl) <==> (BigOps.big_and' (disjoint_or_eq_1 hd) tl /\ disjoint_or_eq tl))
  = BigOps.pairwise_and'_cons disjoint_or_eq_1 hd tl

#set-options "--initial_ifuel 2 --max_fuel 2"

let rec args_b8_mem (l:list arg) (y:b8)
  : Lemma (L.memP y (args_b8 l) <==>
          (exists (a:arg). {:pattern L.memP a l}
             L.memP a l /\
             (match a with
              | (| TD_Base _, _|) -> False
              | (| TD_Buffer src _ _, x|) -> mut_to_b8 src x == y
              | (| TD_ImmBuffer src _ _, x|) -> imm_to_b8 src x == y)))
  = let goal (l:list arg) (a:arg) =
        L.memP a l /\
        (match a with
         | (| TD_Base _, _|) -> False
         | (| TD_Buffer src _ _, x|) -> mut_to_b8 src x == y
         | (| TD_ImmBuffer src _ _, x|) -> imm_to_b8 src x == y)
    in
    match l with
    | [] -> ()
    | hd::tl ->
      match hd with
      | (| TD_Base _, _ |) ->
        args_b8_mem tl y;
        assert ((exists a. goal tl a) ==> (exists a. goal l a))
      | (| TD_Buffer bt _ q, x |) ->
        let aux_1 ()
          : Lemma (requires (y == mut_to_b8 bt x))
                  (ensures (exists a. goal l a)) =
          FStar.Classical.exists_intro (goal l) hd
        in
        let aux_2 ()
          : Lemma (requires (mut_to_b8 bt x =!= y))
                  (ensures (L.memP y (args_b8 l) <==> (exists a. goal l a))) =
          args_b8_mem tl y
        in
        FStar.Classical.move_requires aux_1 ();
        FStar.Classical.move_requires aux_2 ()
      | (| TD_ImmBuffer bt _ q, x |) ->
        let aux_1 ()
          : Lemma (requires (y == imm_to_b8 bt x))
                  (ensures (exists a. goal l a)) =
          FStar.Classical.exists_intro (goal l) hd
        in
        let aux_2 ()
          : Lemma (requires (imm_to_b8 bt x =!= y))
                  (ensures (L.memP y (args_b8 l) <==> (exists a. goal l a))) =
          args_b8_mem tl y
        in
        FStar.Classical.move_requires aux_1 ();
        FStar.Classical.move_requires aux_2 ()

let rec args_b8_disjoint_or_eq (args:list arg)
  : Lemma
      (requires (disjoint_or_eq args))
      (ensures (list_disjoint_or_eq (args_b8 args)))
  =
  list_disjoint_or_eq_reveal ();
  match args with
    | [] -> ()
    | hd::tl ->
      disjoint_or_eq_cons hd tl;
      args_b8_disjoint_or_eq tl;
      BigOps.big_and'_forall (disjoint_or_eq_1 hd) tl;
      FStar.Classical.forall_intro (args_b8_mem tl)

let rec args_b8_live (hs:HS.mem) (args:list arg{all_live hs args})
  : Lemma (list_live hs (args_b8 args))
  = match args with
    | [] -> ()
    | hd::tl ->
      all_live_cons hd tl hs;
      assert (live_arg hs hd);
      assert (all_live hs tl);
      args_b8_live hs tl;
      match hd with
      | (| TD_Base _ , _ |) ->
        assert (args_b8 args == args_b8 tl)
      | (| TD_Buffer t _ _, x |) ->
        assert (B.live hs x);
        assert (args_b8 args == Buffer true x :: args_b8 tl)
      | (| TD_ImmBuffer t _ _, x |) ->
        assert (B.live hs x);
        assert (args_b8 args == imm_to_b8 t x :: args_b8 tl)

let liveness_disjointness (args:list arg) (h:mem_roots args)
  : Lemma (list_disjoint_or_eq (args_b8 args) /\
           list_live h (args_b8 args))
  = args_b8_disjoint_or_eq args;
    args_b8_live h args

let mk_mem (args:list arg) (h:mem_roots args) : GTot interop_heap =
  liveness_disjointness args h;
  mem_of_hs_roots (args_b8 args) h

let mk_mem_injective (args:list arg) (h:mem_roots args)
  : Lemma (hs_of_mem (mk_mem args h) == h /\
           ptrs_of_mem (mk_mem args h) == args_b8 args)
  = ()

let rec mem_roots_p_modifies_none (args:list arg) (h0:HS.mem) (h1:HS.mem)
  : Lemma
    (requires
      mem_roots_p h0 args /\
      B.modifies B.loc_none h0 h1)
    (ensures
      mem_roots_p h1 args)
  = match args with
    | [] -> ()
    | hd::tl ->
      all_live_cons hd tl h0;
      mem_roots_p_modifies_none tl h0 h1;
      match hd with
      | (| TD_Base _, _ |) -> ()
      | (| TD_Buffer _ _ _, x |)
      | (| TD_ImmBuffer _ _ _, x |) -> assert (B.live h1 x)

[@__reduce__]
let arg_of_lb #src #t (x:buf_t src t) : arg = (| TD_Buffer src t default_bq, x |)

[@__reduce__]
let arg_of_sb #t (x:buf_t TUInt64 t) :arg = (| TD_Buffer TUInt64 t stack_bq, x |)

let rec disjoint_or_eq_fresh
       #t
       (x:buf_t TUInt64 t)
       (args:list arg)
       (h0:HS.mem)
  : Lemma
    (requires
      all_live h0 args /\
      x `B.unused_in` h0)
    (ensures
      BigOps.big_and' (disjoint_or_eq_1 (arg_of_sb x)) args)
  = match args with
    | [] -> ()
    | hd::tl ->
      all_live_cons hd tl h0;
      disjoint_or_eq_fresh x tl h0;
      match hd with
      | (|TD_ImmBuffer _ _ _, y|) -> ()
      | _ -> ()

// Everything here should be expressed in terms of the downview, which can be considered as a buffer of bytes

let rec write_taint
    (i:nat)
    (mem:interop_heap)
    (ts:b8 -> GTot taint)
    (b:b8{i <= DV.length (get_downview b.bsrc)})
    (accu:MS.memTaint_t)
  : GTot MS.memTaint_t
        (decreases %[DV.length (get_downview b.bsrc) - i]) =
  if i = DV.length (get_downview b.bsrc) then accu
  else write_taint (i + 1) mem ts b (Map.upd accu (InteropHeap?.addrs mem b + i) (ts b))

let create_memtaint
    (mem:interop_heap)
    (ps:list b8)
    (ts:b8 -> GTot taint)
  : GTot MS.memTaint_t
  = List.Tot.fold_right_gtot ps (write_taint 0 mem ts) (FStar.Map.const Public)

