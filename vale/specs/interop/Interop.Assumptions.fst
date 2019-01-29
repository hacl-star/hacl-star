module Interop.Assumptions
open Interop.Base
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module MS = X64.Machine_s

assume
val st_put
      (#a:Type)
      (p:HS.mem -> Type0)
      (f:(h0:HS.mem{p h0} ->
           GTot (x:(a & HS.mem){ST.equal_domains h0 (snd x)})))
  : ST.Stack a
    (requires p)
    (ensures fun h0 x h1 -> f h0 == (x,h1))

(*
let ptrs = l:list b8{
  list_disjoint_or_eq l /\
  List.Tot.length l < MS.pow2_64
}
let ptr (l:ptrs) = b:b8{List.Tot.memP b l}

module B = LowStar.Buffer

// let addr_map (l:ptrs) = m:(ptr l -> MS.nat64){
//   (forall (buf1:ptr l) (buf2:ptr l).
//     B.disjoint buf1 buf2 ==>
//     disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)) /\
//   (forall (b:ptr l). m b + B.length b < MS.pow2_64)}

// let find (hd:b8) (tl:list b8{ list_disjoint_or_eq (hd::tl) })
//   : b:bool{b ==> List.Tot.memP hd tl }
//   = admit()

let addrs (l:ptrs) : (f:addr_map l & i:MS.nat64 { forall x. f x <= i }) =
  match l with
  | [] ->
    (| (fun x -> 0), 0 |)
  | hd::tl ->
    admit()

    let m_tl = addrs tl in

    admit()
*)

//The initial registers, xmms and flags
assume
val init_regs: MS.reg -> MS.nat64

assume
val init_xmms: MS.xmm -> MS.quad32

assume
val init_flags: MS.nat64

// Abstract current operating system from Low*
assume
val win: bool
