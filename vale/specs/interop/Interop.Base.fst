module Interop.Base
include Interop.Types
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module P = Prop_s
module HS = FStar.HyperStack
module W = Words_s
module L = FStar.List.Tot

let base_typ_as_type (t:base_typ) : Tot eqtype =
  let open W in
  let open Types_s in
  match t with
  | TUInt8 -> UInt8.t
  | TUInt16 -> UInt16.t
  | TUInt32 -> UInt32.t
  | TUInt64 -> UInt64.t
  | TUInt128 -> quad32

[@__reduce__]
let buf_t t = b:B.buffer UInt8.t{B.length b % view_n t == 0}

[@__reduce__]
let ibuf_t t = b:IB.ibuffer UInt8.t{B.length b % view_n t == 0}

let lemma_seq_neq_intro (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a)
 : Lemma (requires (Seq.length s1 =!= Seq.length s2))
         (ensures  (~ (Seq.equal s1 s2)))
 = ()

let imm_to_b8 (b:IB.ibuffer UInt8.t) : b8 = 
  let x:b8' = Buffer b false in
  let s1 = Seq.create 1 (UInt8.uint_to_t 0) in
  lemma_seq_neq_intro s1 Seq.empty;
  Classical.exists_intro (fun s -> ~ (x.rel s Seq.empty)) s1;
  x


[@__reduce__]
let disjoint_or_eq_b8 (ptr1 ptr2:b8) =
  B.loc_disjoint (B.loc_buffer ptr1.b) (B.loc_buffer ptr2.b) \/
  ptr1 == ptr2

let list_disjoint_or_eq (ptrs:list b8) =
  forall (p1 p2:b8). {:pattern (L.memP p1 ptrs); (L.memP p2 ptrs)}
    L.memP p1 ptrs /\
    L.memP p2 ptrs ==> disjoint_or_eq_b8 p1 p2

unfold
let list_live mem (ptrs:list b8) =
  forall p . {:pattern (L.memP p ptrs)} L.memP p ptrs ==> B.live mem p.b

assume val global_addrs_map : addr_map

let mk_addr_map (ptrs : list b8 { list_disjoint_or_eq ptrs }) : GTot addr_map =
  global_addrs_map

noeq
type mem =
  | Mem : ptrs : list b8 { list_disjoint_or_eq ptrs } ->
          addrs : addr_map { addrs  == mk_addr_map ptrs } ->
          hs : HS.mem{ list_live hs ptrs } ->
          mem

[@__reduce__]
let coerce (x:'a{'a == 'b}) : 'b = x

////////////////////////////////////////////////////////////////////////////////

type buffer_qualifiers = {
  modified:bool;
  taint:MS.taint;
  strict_disjointness:bool
}

[@__reduce__]
let default_bq = {
  modified=true;
  taint=MS.Secret;
  strict_disjointness=false
}

[@__reduce__]
let stack_bq = {
  modified=true;
  taint=MS.Public;
  strict_disjointness=true
}

let valid_base_type = x:base_typ{x <> TUInt128}

//type descriptors
type td =
  | TD_Base of valid_base_type
  | TD_Buffer : base_typ -> buffer_qualifiers -> td
  | TD_ImmBuffer : base_typ -> buffer_qualifiers -> td

unfold
let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%__reduce__; `%BigOps.__reduce__];
     delta_only [`%TD_Buffer?;
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
  | TD_Buffer bt _ -> buf_t bt
  | TD_ImmBuffer bt _ -> ibuf_t bt

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
  (#rel1 #rel2 #rrel1 #rrel2:MB.srel UInt8.t) 
  (x:MB.mbuffer UInt8.t rel1 rrel1) 
  (y:MB.mbuffer UInt8.t rel2 rrel2) =
    B.disjoint #UInt8.t x y /\
    ~ (eq3 #(MB.mbuffer UInt8.t rel1 rrel1) #(MB.mbuffer UInt8.t rel2 rrel2) x y)

[@__reduce__]
let disjoint_or_eq_1 (a:arg) (b:arg) =
    match a, b with
    | (| TD_Buffer tx {strict_disjointness=true}, xb |), (| TD_Buffer ty _, yb |)
    | (| TD_ImmBuffer tx {strict_disjointness=true}, xb |), (| TD_ImmBuffer ty _, yb |)     
    | (| TD_Buffer tx _, xb |), (| TD_Buffer ty {strict_disjointness=true}, yb |)
    | (| TD_ImmBuffer tx _, xb |), (| TD_ImmBuffer ty {strict_disjointness=true}, yb |)
    // An immutable buffer and a trivial buffer should not be equal
    | (| TD_ImmBuffer tx _, xb |), (| TD_Buffer ty _, yb |)
    | (| TD_Buffer tx _, xb |), (| TD_ImmBuffer ty _, yb |) ->
      disjoint_not_eq xb yb
    | (| TD_Buffer tx {taint=tntx}, xb |), (| TD_Buffer ty {taint=tnty}, yb |)
    | (| TD_ImmBuffer tx {taint=tntx}, xb |), (| TD_ImmBuffer ty {taint=tnty}, yb |) ->
      disjoint_not_eq xb yb \/ (eq3 xb yb /\ tntx == tnty)
    | _ -> True

[@__reduce__]
let disjoint_or_eq (l:list arg) =
  BigOps.pairwise_and' disjoint_or_eq_1  l

[@__reduce__]
let live_arg (h:HS.mem) (x:arg) =
    match x with
    | (|TD_Buffer tx _, x|)
    | (|TD_ImmBuffer tx _, x|) -> B.live h x
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
  let maybe_cons_buffer (x:arg) (args:list b8) : list b8 =
      match x with
      | (|TD_Buffer _ _, x|) -> (Buffer x true) :: args
      | (|TD_ImmBuffer _ _, x|) -> imm_to_b8 x :: args
      | (|TD_Base _, _ |) -> args
  in
  List.Tot.fold_right_gtot args maybe_cons_buffer []

[@__reduce__]
let modified_arg_loc (x:arg) : GTot B.loc =
    match x with
    | (|TD_Buffer _ {modified=true}, x|) -> B.loc_buffer x
    | _ -> B.loc_none

[@__reduce__]
let loc_modified_args (args:list arg) : GTot B.loc =
    let maybe_union_loc (x:arg) l =
      match x with
      | (|TD_Buffer _ {modified=true}, x|) -> B.loc_union (B.loc_buffer x) l
      | _ -> l
    in
    List.Tot.fold_right_gtot args maybe_union_loc B.loc_none

[@__reduce__]
let arg_loc (x:arg) : GTot B.loc =
    match x with
    | (|TD_Buffer _ _, x|) -> B.loc_buffer x
    | (|TD_ImmBuffer _ _, x|) -> B.loc_buffer x
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
              | (| TD_Buffer _ _, x|) -> Buffer x true == y
              | (| TD_ImmBuffer _ _, x|) -> imm_to_b8 x == y)))
  = let goal (l:list arg) (a:arg) =
        L.memP a l /\
        (match a with
         | (| TD_Base _, _|) -> False
         | (| TD_Buffer _ _, x|) -> Buffer x true == y
         | (| TD_ImmBuffer _ _, x|) -> imm_to_b8 x == y)
    in
    match l with
    | [] -> ()
    | hd::tl ->
      match hd with
      | (| TD_Base _, _ |) ->
        args_b8_mem tl y;
        assert ((exists a. goal tl a) ==> (exists a. goal l a))
      | (| TD_Buffer bt q, x |) ->  
        let aux_1 ()
          : Lemma (requires (y == Buffer x true))
                  (ensures (exists a. goal l a)) =
          FStar.Classical.exists_intro (goal l) hd
        in
        let aux_2 ()
          : Lemma (requires (Buffer x true =!= y))
                  (ensures (L.memP y (args_b8 l) <==> (exists a. goal l a))) =
          args_b8_mem tl y
        in            
        FStar.Classical.move_requires aux_1 ();
        FStar.Classical.move_requires aux_2 ()
      | (| TD_ImmBuffer bt q, x |) ->  
        let aux_1 ()
          : Lemma (requires (y == imm_to_b8 x))
                  (ensures (exists a. goal l a)) =
          FStar.Classical.exists_intro (goal l) hd
        in
        let aux_2 ()
          : Lemma (requires (imm_to_b8 x =!= y))
                  (ensures (L.memP y (args_b8 l) <==> (exists a. goal l a))) =
          args_b8_mem tl y
        in            
        FStar.Classical.move_requires aux_1 ();
        FStar.Classical.move_requires aux_2 ()        

let rec args_b8_disjoint_or_eq (args:list arg)
  : Lemma
      (requires (disjoint_or_eq args))
      (ensures (list_disjoint_or_eq (args_b8 args)))
  = match args with
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
      | (| TD_Buffer t _, x |) ->
        assert (B.live hs x);
        assert (args_b8 args == Buffer x true :: args_b8 tl)
      | (| TD_ImmBuffer t _, x |) ->
        assert (B.live hs x);
        assert (args_b8 args == imm_to_b8 x :: args_b8 tl)        

let liveness_disjointness (args:list arg) (h:mem_roots args)
  : Lemma (list_disjoint_or_eq (args_b8 args) /\
           list_live h (args_b8 args))
  = args_b8_disjoint_or_eq args;
    args_b8_live h args

let mem_of_hs_roots (ptrs:list b8{list_disjoint_or_eq ptrs})
                    (h:HS.mem{list_live h ptrs})
  : GTot mem
  = Mem ptrs (mk_addr_map ptrs) h

let mk_mem (args:list arg) (h:mem_roots args) : GTot mem =
  liveness_disjointness args h;
  mem_of_hs_roots (args_b8 args) h

unfold
let hs_of_mem (m:mem) : HS.mem = Mem?.hs m
unfold
let ptrs_of_mem (m:mem) : l:list b8{list_disjoint_or_eq l} = Mem?.ptrs m
unfold
let addrs_of_mem (m:mem) : addr_map = Mem?.addrs m

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
      mem_roots_p_modifies_none tl h0 h1

[@__reduce__]
let arg_of_lb #t (x:buf_t t) : arg = (| TD_Buffer t default_bq, x |)

[@__reduce__]
let arg_of_sb #t (x:buf_t t) :arg = (| TD_Buffer t stack_bq, x |)

let rec disjoint_or_eq_fresh
       #t
       (x:buf_t t)
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
      | (|TD_ImmBuffer _ _, y|) -> Vale.LowStarHelpers.lemma_different_preorders_different_buffers x y
      | _ -> ()

let rec write_taint
    (i:nat)
    (mem:mem)
    (ts:b8 -> GTot MS.taint)
    (b:b8{i <= B.length b.b})
    (accu:MS.memTaint_t)
  : GTot MS.memTaint_t
        (decreases %[B.length b.b - i]) =
  if i = B.length b.b then accu
  else write_taint (i + 1) mem ts b (Map.upd accu (Mem?.addrs mem b + i) (ts b))

let create_memtaint
    (mem:mem)
    (ps:list b8)
    (ts:b8 -> GTot MS.taint)
  : GTot MS.memTaint_t
  = List.Tot.fold_right_gtot ps (write_taint 0 mem ts) (FStar.Map.const MS.Public)

let correct_down_p (mem:mem) (h:BS.heap) (p:b8) =
  let length = B.length p.b in
  let contents = B.as_seq (hs_of_mem mem) p.b in
  let addr = addrs_of_mem mem p in
  let open BS in
  (forall i.{:pattern (Seq.index contents i)}  0 <= i /\ i < length ==> h.[addr + i] == UInt8.v (FStar.Seq.index contents i))

let rec addrs_ptr (i:nat) (addrs:addr_map) (ptr:b8{i <= B.length ptr.b}) (acc:Set.set int)
  : GTot (Set.set int)
         (decreases (B.length ptr.b - i))
  = if i = B.length ptr.b then acc
    else addrs_ptr (i + 1) addrs ptr (Set.union (Set.singleton (addrs ptr + i)) acc)

let addrs_set (mem:mem) : GTot (Set.set int) =
  L.fold_right_gtot (ptrs_of_mem mem) (addrs_ptr 0 (addrs_of_mem mem)) Set.empty

let correct_down (mem:mem) (h:BS.heap) =
  Set.equal (addrs_set mem) (Map.domain h) /\
  (forall p.{:pattern (L.memP p (ptrs_of_mem mem))}
    L.memP p (ptrs_of_mem mem) ==> correct_down_p mem h p)

let down_mem_t = m:mem -> GTot (h:BS.heap {correct_down m h})
