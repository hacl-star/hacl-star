module Hacl.Spec.Lib

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators
module VecLemmas = Lib.Vec.Lemmas

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


let generate_elems4_a (t:Type0) (a:Type0) (max:nat) (i:nat{i <= max / 4}) = a & s:seq t{length s == 4 * i}

val generate_elems4_f:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> f:(i:nat{i < max} -> a -> a & t)
  -> i:nat{i < max / 4}
  -> acc:generate_elems4_a t a max i ->
  generate_elems4_a t a max (i + 1)

let generate_elems4_f #t #a max f i (c, res) =
  let c0, e0 = f (4 * i) c in
  let c1, e1 = f (4 * i + 1) c0 in
  let c2, e2 = f (4 * i + 2) c1 in
  let c3, e3 = f (4 * i + 3) c2 in

  let res0 = Seq.snoc res e0 in
  let res1 = Seq.snoc res0 e1 in
  let res2 = Seq.snoc res1 e2 in
  let res3 = Seq.snoc res2 e3 in
  c3, res3


val generate_elems_unroll4:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Tot (a & s:seq t{length s == n})

let generate_elems_unroll4 #t #a max n f init =
  let (c0, res0) = Loops.repeat_gen (n / 4) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in
  let (c1, res1) = Loops.repeat_right (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f) (c0, res0) in
  (c1, res1)


val lemma_generate_elems4:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max /\ n % 4 = 0}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Lemma
   (let (c0, res0) = Loops.repeat_gen (n / 4) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in
    let (c1, res1) = Loops.repeat_gen n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty) in
    c0 == c1 /\ res0 == res1)

let lemma_generate_elems4 #t #a max n f init =
  let acc_v = Loops.repeat_gen (n / 4) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in
  let acc = Loops.repeat_gen n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty) in

  let normalize_v (i:nat{i <= n / 4}) (acc_v:generate_elems4_a t a max i) : generate_elem_a t a max (4 * i) =
    let (c, res) = acc_v in
    (c, res) in

  let aux (i:nat{i < n / 4}) (acc_v:generate_elems4_a t a max i) : Lemma
    (normalize_v (i + 1) (generate_elems4_f max f i acc_v) ==
     Loops.repeat_right (4 * i) (4 * i + 4)
      (generate_elem_a t a max) (generate_elem_f max f) (normalize_v i acc_v)) =

    let acc0 = normalize_v i acc_v in
    let acc = Loops.repeat_right (4 * i) (4 * i + 4) (generate_elem_a t a max) (generate_elem_f max f) acc0 in
    Loops.unfold_repeat_right (4 * i) (4 * i + 4) (generate_elem_a t a max) (generate_elem_f max f) acc0 (4 * i + 3);
    Loops.unfold_repeat_right (4 * i) (4 * i + 3) (generate_elem_a t a max) (generate_elem_f max f) acc0 (4 * i + 2);
    Loops.unfold_repeat_right (4 * i) (4 * i + 2) (generate_elem_a t a max) (generate_elem_f max f) acc0 (4 * i + 1);
    Loops.unfold_repeat_right (4 * i) (4 * i + 1) (generate_elem_a t a max) (generate_elem_f max f) acc0 (4 * i);
    Loops.eq_repeat_right (4 * i) (4 * i) (generate_elem_a t a max) (generate_elem_f max f) acc0;
    assert (normalize_v (i + 1) (generate_elems4_f max f i acc_v) == acc);
    () in

  Classical.forall_intro_2 aux;
  VecLemmas.lemma_repeat_gen_vec 4 (n / 4) (generate_elem_a t a max) (generate_elems4_a t a max) normalize_v
     (generate_elem_f max f) (generate_elems4_f max f) (init, Seq.empty);

  Loops.repeat_gen_def (n / 4) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty);
  Loops.repeat_gen_def n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty)


val lemma_generate_elems_unroll4:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Lemma (generate_elems_unroll4 #t #a max n f init == generate_elems #t #a max n f init)

let lemma_generate_elems_unroll4 #t #a max n f init =
  let (c0, res0) = Loops.repeat_gen (n / 4) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in
  let (c1, res1) = Loops.repeat_right (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f) (c0, res0) in
  let (c2, res2) = Loops.repeat_gen n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty) in
  let (c3, res3) = Loops.repeat_gen (n / 4 * 4) (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty) in

  Loops.repeat_gen_def n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty);
  //assert ((c2, res2) == Loops.repeat_right 0 n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty));
  Loops.repeat_right_plus 0 (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty);
  //assert ((c2, res2) == Loops.repeat_right (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f)
    //(Loops.repeat_right 0 (n / 4 * 4) (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty)));
  Loops.repeat_gen_def (n / 4 * 4) (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty);
  //assert ((c2, res2) == Loops.repeat_right (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f)
    //(Loops.repeat_gen (n / 4 * 4) (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty)));

  lemma_generate_elems4 #t #a max (n / 4 * 4) f init;
  assert (c3 == c0 /\ res3 == res0);
  assert ((c2, res2) == Loops.repeat_right (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f) (c0, res0));
  assert (c1 == c2 /\ res1 == res2)
