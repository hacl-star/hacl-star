module Hacl.SHA2Again

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2Again.Constants
module S = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module T = FStar.Tactics

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

let alloca a () =
  [@ inline_let ]
  let l: list (word a) = Spec.(match a with
    | SHA2_224 -> C.h224_l
    | SHA2_256 -> C.h256_l
    | SHA2_384 -> C.h384_l
    | SHA2_512 -> C.h512_l) in
  B.alloca_of_list l

let alloca_224: alloca_t Spec.SHA2_224 =
  T.(synth_by_tactic (specialize (alloca Spec.SHA2_224) [`%alloca]))
let alloca_256: alloca_t Spec.SHA2_256 =
  T.(synth_by_tactic (specialize (alloca Spec.SHA2_256) [`%alloca]))
let alloca_384: alloca_t Spec.SHA2_384 =
  T.(synth_by_tactic (specialize (alloca Spec.SHA2_384) [`%alloca]))
let alloca_512: alloca_t Spec.SHA2_512 =
  T.(synth_by_tactic (specialize (alloca Spec.SHA2_512) [`%alloca]))

let assign_224: B.assign_list_t C.h224_l =
  T.(synth_by_tactic (specialize (B.assign_list C.h224_l) [`%B.assign_list]))
let assign_256: B.assign_list_t C.h256_l =
  T.(synth_by_tactic (specialize (B.assign_list C.h256_l) [`%B.assign_list]))
let assign_384: B.assign_list_t C.h384_l =
  T.(synth_by_tactic (specialize (B.assign_list C.h384_l) [`%B.assign_list]))
let assign_512: B.assign_list_t C.h512_l =
  T.(synth_by_tactic (specialize (B.assign_list C.h512_l) [`%B.assign_list]))

let init a s =
  let open Spec in
  match a with
  | SHA2_224 -> assign_224 s
  | SHA2_256 -> assign_256 s
  | SHA2_384 -> assign_384 s
  | SHA2_512 -> assign_512 s

let init_224: init_t Spec.SHA2_224 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_224) [`%init]))
let init_256: init_t Spec.SHA2_256 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_256) [`%init]))
let init_384: init_t Spec.SHA2_384 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_384) [`%init]))
let init_512: init_t Spec.SHA2_512 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_512) [`%init]))

