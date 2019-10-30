module Vale.Interop.Types
open FStar.Mul
include Vale.Arch.HeapTypes_s
module MB = LowStar.Monotonic.Buffer
module DV = LowStar.BufferView.Down
module W = Vale.Def.Words_s
module L = FStar.List.Tot

[@__reduce__]
let base_typ_as_type (t:base_typ) : eqtype =
  let open W in
  let open Vale.Def.Types_s in
  match t with
  | TUInt8 -> UInt8.t
  | TUInt16 -> UInt16.t
  | TUInt32 -> UInt32.t
  | TUInt64 -> UInt64.t
  | TUInt128 -> quad32

[@__reduce__]
unfold // without the unfold, "% view_n t" leads to very slow Z3 performance
let view_n_unfold (t:base_typ) : pos =
  match t with
  | TUInt8 -> 1
  | TUInt16 -> 2
  | TUInt32 -> 4
  | TUInt64 -> 8
  | TUInt128 -> 16

let view_n (t:base_typ) : pos = view_n_unfold t

[@__reduce__]
let down_view (t:base_typ) : DV.view (base_typ_as_type t) UInt8.t = match t with
  | TUInt8 -> Vale.Interop.Views.down_view8
  | TUInt16 -> Vale.Interop.Views.down_view16
  | TUInt32 -> Vale.Interop.Views.down_view32
  | TUInt64 -> Vale.Interop.Views.down_view64
  | TUInt128 -> Vale.Interop.Views.down_view128

[@__reduce__]
noeq
type b8' =
| Buffer:
  #src:base_typ ->
  #rrel:MB.srel (base_typ_as_type src) ->
  #rel:MB.srel (base_typ_as_type src) ->
  bsrc:MB.mbuffer (base_typ_as_type src) rrel rel ->
  writeable:bool ->
  b8'

// A buffer is considered writeable iff the preorders are trivial
type b8 = (b:b8'{b.writeable <==> (forall s1 s2. b.rrel s1 s2 /\ b.rel s1 s2)})

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 ||
  addr2 + length2 < addr1

let get_downview
  (#src:base_typ)
  (#rrel #rel:MB.srel (base_typ_as_type src))
  (b:MB.mbuffer (base_typ_as_type src) rrel rel) =
  DV.mk_buffer_view b (down_view src)

type addr_map = m:(b8 -> W.nat64){
  (forall (buf1 buf2:b8).{:pattern (m buf1); (m buf2)}
    MB.disjoint buf1.bsrc buf2.bsrc ==>
    disjoint_addr (m buf1) (DV.length (get_downview buf1.bsrc)) (m buf2) (DV.length (get_downview buf2.bsrc))) /\
  (forall (b:b8).{:pattern (m b)} m b + DV.length (get_downview b.bsrc) < W.pow2_64)}
