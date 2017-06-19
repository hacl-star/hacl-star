module Seq.Lib

open FStar.Seq
open FStar.UInt32

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5 --initial_ifuel 0 --max_ifuel 0"

abstract
val seq_4: #a:Type -> a0:a -> a1:a -> a2:a -> a3:a -> Tot (s:seq a{length s = 4
  /\ Seq.index s 0 == a0 /\ Seq.index s 1 == a1 /\ Seq.index s 2 == a2 /\ Seq.index s 3 == a3})
let seq_4 #a s0 s1 s2 s3 =
  let s = create 4 s0 in
  let s = upd s 1 s1 in
  let s = upd s 2 s2 in
  upd s 3 s3

val lemma_slice048: #a:Type -> s:seq a{length s = 8} -> Lemma (slice s 0 4 @| slice s 4 8 == s)
let lemma_slice048 #a s =
  lemma_eq_intro s (slice s 0 4 @| slice s 4 8)


let idx = i:nat{i < 4}

val lemma_upd_0: #a:Type -> s:seq a{length s = 4} -> v:a -> Lemma (
  let s' = upd s 0 v in
  index s' 1 == index s 1 /\ index s' 2 == index s 2 /\ index s' 3 == index s 3
  /\ index s' 0 == v)
let lemma_upd_0 #a s v = ()

val lemma_upd_1: #a:Type -> s:seq a{length s = 4} -> v:a -> Lemma (
  let s' = upd s 1 v in
  index s' 0 == index s 0 /\ index s' 2 == index s 2 /\ index s' 3 == index s 3
  /\ index s' 1 == v)
let lemma_upd_1 #a s v = ()

val lemma_upd_2: #a:Type -> s:seq a{length s = 4} -> v:a -> Lemma (
  let s' = upd s 2 v in
  index s' 0 == index s 0 /\ index s' 1 == index s 1 /\ index s' 3 == index s 3
  /\ index s' 2 == v)
let lemma_upd_2 #a s v = ()

val lemma_upd_3: #a:Type -> s:seq a{length s = 4} -> v:a -> Lemma (
  let s' = upd s 3 v in
  index s' 0 == index s 0 /\ index s' 2 == index s 2 /\ index s' 1 == index s 1
  /\ index s' 3 == v)
let lemma_upd_3 #a s v = ()

val line: #t:Type -> a:nat{a < 4} -> b:nat{b < 4} -> c:nat{c < 4} -> n:UInt32.t {v n < 32} -> s:seq t{length s = 4} -> (f:t -> n:UInt32.t{v n < 32} -> Tot t) -> Tot (s':seq t{length s' = 4})
(* let line #t a b d s m f = *)
(*   let m = upd m a (index m a +%^ index m b) in *)
(*   let m = upd m d (f (index m d ^^  index m a) s) in *)
(*   m *)
