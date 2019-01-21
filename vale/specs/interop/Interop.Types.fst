module Interop.Types
module B = LowStar.Buffer
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

let b8 = B.buffer UInt8.t

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 ||
  addr2 + length2 < addr1

type addr_map = m:(b8 -> W.nat64){
  (forall (buf1 buf2:b8).{:pattern (m buf1); (m buf2)}
    B.disjoint buf1 buf2 ==>
    disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)) /\
  (forall (b:b8).{:pattern (m b)} m b + B.length b < W.pow2_64)}
