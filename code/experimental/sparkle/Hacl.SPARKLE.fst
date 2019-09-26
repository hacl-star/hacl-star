module Hacl.SPARKLE

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

#set-options "--max_fuel 0 --max_ifuel 0"

module Spec = Spec.SPARKLE

type branch = lbuffer uint32 (size 2)
let branch_to_spec (b: branch) (h : mem) : GTot Spec.branch =
  let b_values = as_seq h b in
  (Seq.index b_values 0, Seq.index b_values 1)


val arx: c:uint32 -> b:branch -> Stack unit
  (requires (fun h0 ->
    live h0 b
  ))
  (ensures (fun h0 new_b h1 ->
    branch_to_spec b h1 == Spec.arx c (branch_to_spec b h0) /\
    modifies1 b h0 h1
  ))
let arx c b =
  let x = index b (size 0) in
  let y = index b (size 1) in
  let x, y = Spec.arx c (x,y) in
  upd b (size 0) x;
  upd b (size 1) y
