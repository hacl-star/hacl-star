module Hacl.Poly1305
open Hacl.Impl.Poly1305.Fields
open Lib.IntTypes

let poly1305_mac o t l k = Hacl.Impl.Poly1305.poly1305_mac #M64 o t l k
(*

let mask44 = u64 0xfffffffffff

inline_for_extraction
val carry44: u1:uint64 -> cin:uint64 ->  (r:uint64 * cout:uint64)
inline_for_extraction
let carry44 u1 cin = 
    let u1 = u1 +. cin in
    let r0 = u1 &. mask44 in
    let r1 = u1 >>. u32 44 in
    (r0,r1)

let test_tuple () = 
  let (x,y) = carry44 (u64 0) (u64 0) in
  x +. y

*)
