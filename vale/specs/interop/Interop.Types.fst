module Interop.Types
module MB = LowStar.Monotonic.Buffer
module W = Words_s
module L = FStar.List.Tot

let __reduce__ = ()

type base_typ:eqtype =
  | TUInt8
  | TUInt16
  | TUInt32
  | TUInt64
  | TUInt128

[@__reduce__]
let view_n = function
  | TUInt8 -> 1
  | TUInt16 -> 2
  | TUInt32 -> 4
  | TUInt64 -> 8
  | TUInt128 -> 16

[@__reduce__]
noeq
type b8' =
| Buffer: 
  #rrel:MB.srel UInt8.t -> 
  #rel:MB.srel UInt8.t -> 
  b:MB.mbuffer UInt8.t rrel rel ->
  writeable:bool ->
  b8'

// A buffer is considered writeable iff the preorders are trivial
type b8 = (b:b8'{b.writeable <==> (forall s1 s2. b.rrel s1 s2 /\ b.rel s1 s2)})

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 ||
  addr2 + length2 < addr1

type addr_map = m:(b8 -> W.nat64){
  (forall (buf1 buf2:b8).{:pattern (m buf1); (m buf2)}
    MB.disjoint buf1.b buf2.b ==>
    disjoint_addr (m buf1) (MB.length buf1.b) (m buf2) (MB.length buf2.b)) /\
  (forall (b:b8).{:pattern (m b)} m b + MB.length b.b < W.pow2_64)}
