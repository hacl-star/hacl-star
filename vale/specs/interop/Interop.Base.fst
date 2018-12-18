module Interop.Base

module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
let __reduce__ = ()

[@__reduce__]
let view_n (x:ME.typ) =
  let open ME in
  match x with
  | TBase TUInt8 -> 1
  | TBase TUInt16 -> 2
  | TBase TUInt32 -> 4
  | TBase TUInt64 -> 8
  | TBase TUInt128 -> 16

let b8 = B.buffer UInt8.t

[@__reduce__]
let lowstar_buffer (t:ME.typ) = b:b8{B.length b % view_n t == 0}

//TODO: This should be provided by X64.Memory
let buffer_equiv (t:ME.typ)
  : Lemma (ME.buffer t == lowstar_buffer t)
  = admit()

[@__reduce__]
let coerce (x:'a{'a == 'b}) : 'b = x

[@__reduce__]
let as_lowstar_buffer (#t:ME.typ) (x:ME.buffer t)
  : Tot (lowstar_buffer t)
  = buffer_equiv t;
    coerce x

[@__reduce__]
let as_vale_buffer (#t:ME.typ) (x:lowstar_buffer t)
  : Tot (b:ME.buffer t)
  = buffer_equiv t;
    coerce x

////////////////////////////////////////////////////////////////////////////////

//type descriptors
type td =
  | TD_Base of ME.base_typ
  | TD_Buffer of ME.base_typ

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
                 // `%Interop.list_disjoint_or_eq;
                 // `%Interop.list_live
                 ];
     primops;
     simplify]
     x

////////////////////////////////////////////////////////////////////////////////

#set-options "--initial_ifuel 1"
[@__reduce__]
let base_typ_as_type : X64.Memory.base_typ -> Type =
  let open ME in
  function
  | TUInt8 -> UInt8.t
  | TUInt16 -> UInt16.t
  | TUInt32 -> UInt32.t
  | TUInt64 -> UInt64.t
  | TUInt128 -> UInt128.t

[@__reduce__]
let td_as_type : td -> Type =
  let open ME in
  function
  | TD_Base bt -> base_typ_as_type bt
  | TD_Buffer bt -> lowstar_buffer (TBase bt)

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
let __test : n_dep_arrow [TD_Base ME.TUInt8] (fun (x:UInt8.t) -> y:UInt8.t{x == y}) =
  fun (x:UInt8.t) -> intro_dep_arrow_nil (y:UInt8.t{x == y}) x
////////////////////////////////////////////////////////////////////////////////

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 ||
  addr2 + length2 < addr1

type addr_map = m:(b8 -> ME.nat64){
  (forall (buf1 buf2:b8).{:pattern (m buf1); (m buf2)} 
    B.disjoint buf1 buf2 ==> 
    disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)) /\
  (forall (b:b8).{:pattern (m b)} m b + B.length b < MS.pow2_64)}

////////////////////////////////////////////////////////////////////////////////

[@__reduce__]
let disjoint_or_eq_1 (a:arg) (b:arg) =
    match a, b with
    | (| TD_Buffer tx, xb |), (| TD_Buffer ty, yb |) ->
      B.disjoint #UInt8.t xb yb \/ eq2 #b8 xb yb
    | _ -> True

[@__reduce__]
let disjoint_or_eq (l:list arg) =
  BigOps.pairwise_and disjoint_or_eq_1  l

[@__reduce__]
let live_arg (h:HS.mem) (x:arg) =
    match x with
    | (|TD_Buffer _, x|) -> B.live h x
    | _ -> True

[@__reduce__]
let all_live (h:HS.mem) (bs:list arg) =
  BigOps.big_and (live_arg h) bs

[@__reduce__]
let mem_roots_p (h0:HS.mem) (args:list arg) =
  disjoint_or_eq args /\
  all_live h0 args

[@__reduce__]
let mem_roots (args:list arg) =
    h0:HS.mem{ mem_roots_p h0 args }

[@__reduce__]
let arg_loc (x:arg) : GTot B.loc =
    match x with
    | (|TD_Buffer _, x|) -> B.loc_buffer x
    | _ -> B.loc_none

[@__reduce__]
let loc_args (args:list arg) : GTot B.loc =
    B.loc_union_l (List.Tot.map_gtot arg_loc args)

let all_live_cons (hd:arg) (tl:list arg) (h0:HS.mem)
  : Lemma 
    (all_live h0 (hd :: tl) <==> (live_arg h0 hd /\ all_live h0 tl))
  = ()

let disjoint_or_eq_def (l:list arg)
   : Lemma (disjoint_or_eq l == BigOps.pairwise_and disjoint_or_eq_1 l)
   = ()

let disjoint_or_eq_cons (hd:arg) (tl:list arg)
  : Lemma (disjoint_or_eq (hd::tl) <==> (BigOps.big_and (disjoint_or_eq_1 hd) tl /\ disjoint_or_eq tl))
  = BigOps.pairwise_and'_cons disjoint_or_eq_1 hd tl;
    BigOps.normal_eq (BigOps.big_and' (disjoint_or_eq_1 hd) tl);
    disjoint_or_eq_def (hd::tl)

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
      disjoint_or_eq_cons hd tl;
      mem_roots_p_modifies_none tl h0 h1

[@__reduce__]
let arg_of_lb #t (x:lowstar_buffer (ME.TBase t)) : arg = (| TD_Buffer t, x |)

let rec disjoint_or_eq_fresh
       #t
       (x:lowstar_buffer (ME.TBase t))
       (args:list arg)
       (h0:HS.mem)
  : Lemma 
    (requires 
      all_live h0 args /\
      x `B.unused_in` h0)
    (ensures
      BigOps.big_and (disjoint_or_eq_1 (arg_of_lb x)) args)
  = match args with
    | [] -> ()
    | hd::tl ->
      all_live_cons hd tl h0;
      disjoint_or_eq_fresh x tl h0
