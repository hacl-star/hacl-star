module Hacl.Spec.Lib

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators

///
///  TODO: move the following functions to Lib.Sequence?
///

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let generate_elem_a (t:Type0) (a:Type0) (max:nat) (i:nat{i <= max}) = a & s:seq t{length s == i}

val generate_elem_f:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> f:(i:nat{i < max} -> a -> a & t)
  -> i:nat{i < max}
  -> acc:generate_elem_a t a max i ->
  generate_elem_a t a max (i + 1)

let generate_elem_f #t #a max f i (c, res) =
  let c', e = f i c in
  let res' = Seq.snoc res e in
  c', res'


val generate_elems:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Tot (a & s:seq t{length s == n})

let generate_elems #t #a max n f init =
  let init2 : generate_elem_a t a max 0 = (init, Seq.empty) in
  Loops.repeat_gen n (generate_elem_a t a max) (generate_elem_f max f) init2


val eq_generate_elems0:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Lemma (generate_elems #t #a max 0 f init == (init, Seq.empty))

let eq_generate_elems0 #t #a max n f init =
  let init2 : generate_elem_a t a max 0 = (init, Seq.empty) in
  Loops.eq_repeat_gen0 n (generate_elem_a t a max) (generate_elem_f max f) init2


val generate_elems_unfold:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a
  -> i:nat{i < n} -> Lemma
  (generate_elems #t #a max (i + 1) f init ==
   generate_elem_f max f i (generate_elems #t #a max i f init))

let generate_elems_unfold #t #a max n f init i =
  let init2 : generate_elem_a t a max 0 = (init, Seq.empty) in
  Loops.unfold_repeat_gen (i + 1) (generate_elem_a t a max) (generate_elem_f max f) init2 i
