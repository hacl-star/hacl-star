module Hacl.Frodo.Random

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Frodo.Random

(* Stub stateless implementation on top of Lib.RandomBuffer.System.
   Intended to be replaced for KATs with include/rng.c *)

friend Lib.IntTypes

let state = gcmalloc HyperStack.root 0uy 48ul

let randombytes_init_ entropy_input =
  let h0 = HyperStack.ST.get () in
  assume (as_seq h0 state == S.randombytes_init_ (as_seq h0 entropy_input))  

let randombytes_ len res =
  let h0 = HyperStack.ST.get () in
  let b = Lib.RandomBuffer.System.randombytes res len in
  let h1 = HyperStack.ST.get () in
  assume (let r, st = S.randombytes_ (as_seq h0 state) (v len) in
          r == as_seq h1 res /\ st == as_seq h1 state)
