module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

let zqelem_t q = x:nat{x < q}
let zqvector_t q n = lseq (zqelem_t q) n
let zqmatrix_t q n m = lseq (zqvector_t q n) m

let zqelem #q x = x % q
let zqadd #q a b = zqelem (a + b)
let zqsub #q a b = zqelem (a + q - b)
let zqmul #q a b = zqelem (a * b)

let zqvector_add #q #n a b =
  let c:zqvector_t q n = create n (zqelem #q 0) in
  repeati n
  (fun i c ->
    c.[i] <- zqadd a.[i] b.[i]
  ) c

let zqvector_sub #q #n a b =
  let c:zqvector_t q n = create n (zqelem #q 0) in
  repeati n
  (fun i c ->
    c.[i] <- zqsub a.[i] b.[i]
  ) c

let zqmatrix_zero #q #n #m = create m (create n (zqelem #q 0))

let zqmatrix_add #q #n #m a b =
  let c:zqmatrix_t q n m = create m (create n (zqelem #q 0)) in
  repeati m
  (fun i c ->
    c.[i] <- zqvector_add a.[i] b.[i]
  ) c

let zqmatrix_sub #q #n #m a b =
  let c:zqmatrix_t q n m = create m (create n (zqelem #q 0)) in
  repeati m
  (fun i c ->
    c.[i] <- zqvector_sub a.[i] b.[i]
  ) c

let zqmatrix_mul #q #n1 #n2 #n3 a b =
  let c:zqmatrix_t q n1 n3 = create n3 (create n1 (zqelem #q 0)) in
  repeati n3
  (fun i c ->
    c.[i] <- repeati n1 (fun k ci ->
      ci.[k] <- repeati n2 (fun j tmp -> zqadd tmp (zqmul ((a.[j]).[k]) ((b.[i]).[j]))) 0
    ) c.[i]
  ) c

(* Lemmas *)
let matrix_distributivity_add_right #q #n1 #n2 #n3 a b c = admit()
let matrix_distributivity_add_left #q #n1 #n2 #n3 a b c = admit()
let matrix_associativity_mul #q #n1 #n2 #n3 #n4 a b c = admit()
let matrix_associativity_add #q #n1 #n2 a b c = admit()
let matrix_commutativity_add #q #n1 #n2 a b = admit()
let matrix_sub_zero #q #n1 #n2 a = admit()
let matrix_add_zero #q #n1 #n2 a = admit()
