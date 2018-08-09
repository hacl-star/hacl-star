module Hacl.SHA2Again

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2Again.Constants
module S = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

friend Spec.SHA2Again

// 20180809 bug: need to start interactive mode with nothing beyond this line, then load the rest
module Spec = Spec.SHA2Again

let h224 = B.gcmalloc_of_list HS.root C.h224_l
let h256 = B.gcmalloc_of_list HS.root C.h256_l
let h384 = B.gcmalloc_of_list HS.root C.h384_l
let h512 = B.gcmalloc_of_list HS.root C.h512_l

let k224_256 = B.gcmalloc_of_list HS.root C.k224_256_l
let k384_512 = B.gcmalloc_of_list HS.root C.k384_512_l

let hashes a s l =
  Spec.hashes a s l

let init a =
  C.h224_reveal ();
  C.h256_reveal ();
  C.h384_reveal ();
  C.h512_reveal ();
  let l: list (word a) = Spec.(match a with
    | SHA2_224 -> C.h224_l
    | SHA2_256 -> C.h256_l
    | SHA2_384 -> C.h384_l
    | SHA2_512 -> C.h512_l) in
  B.alloca_of_list l
