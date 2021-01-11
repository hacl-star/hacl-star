module Hacl.Spec.Lib

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators
module VecLemmas = Lib.Vec.Lemmas

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


val lemma_generate_elems_unroll4_loop:
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

let lemma_generate_elems_unroll4_loop #t #a max n f init =
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
  Loops.repeat_right_plus 0 (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty);
  Loops.repeat_gen_def (n / 4 * 4) (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty);
  lemma_generate_elems_unroll4_loop #t #a max (n / 4 * 4) f init


val generate_blocks4_f:
    #t:Type0
  -> #a:Type0
  -> k:nat
  -> f:(i:nat{i < 4 * k} -> a -> a & t)
  -> i:nat{i < k}
  -> c:a
  -> tuple2 a (lseq t 4)

let generate_blocks4_f #t #a max f i c =
  let c0, e0 = f (4 * i) c in
  let c1, e1 = f (4 * i + 1) c0 in
  let c2, e2 = f (4 * i + 2) c1 in
  let c3, e3 = f (4 * i + 3) c2 in
  c3, Lib.IntVector.create4 e0 e1 e2 e3


val lemma_generate_elems4_loop_step:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> k:nat{4 * k <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> i:nat{i < k}
  -> c:a
  -> s:seq t{length s == 4 * i} ->
  Lemma
  (let (c1, res1) = generate_elems4_f #t #a max f i (c, s) in
   let (c2, res2) = generate_blocks4_f #t #a k f i c in
   c1 == c2 /\ Seq.append s res2 == res1)

let lemma_generate_elems4_loop_step #t #a max k f i c s =
  let (c1, res1) = generate_elems4_f #t #a max f i (c, s) in
  let (c2, res2) = generate_blocks4_f #t #a k f i c in

  let c0, e0 = f (4 * i) c in
  let c1, e1 = f (4 * i + 1) c0 in
  let c2, e2 = f (4 * i + 2) c1 in
  let c3, e3 = f (4 * i + 3) c2 in
  let res = Lib.IntVector.create4 e0 e1 e2 e3 in
  let res0 = Seq.snoc s e0 in
  let res1 = Seq.snoc res0 e1 in
  let res2 = Seq.snoc res1 e2 in
  let res3 = Seq.snoc res2 e3 in

  Seq.lemma_eq_intro (Seq.append s res) res3


val lemma_generate_elems4_loop:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a -> Lemma
  (let (c1, res1) = generate_blocks 4 (max / 4) (n / 4) (Loops.fixed_a a) (generate_blocks4_f #t #a (max / 4) f) init in
   let (c2, res2) = Loops.repeat_gen (n / 4) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in
   c1 == c2 /\ res1 == res2)

let rec lemma_generate_elems4_loop #t #a max n f init =
  let k = n / 4 in
  let (c1, res1) = generate_blocks 4 (max / 4) k (Loops.fixed_a a) (generate_blocks4_f #t #a (max / 4) f) init in
  let (c2, res2) = Loops.repeat_gen k (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in

  if k = 0 then begin
    eq_generate_blocks0 4 (max / 4) (Loops.fixed_a a) (generate_blocks4_f #t #a (max / 4) f) init;
    Loops.eq_repeat_gen0 k (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) end
  else begin
    lemma_generate_elems4_loop #t #a max (n - 4) f init;
    let (c3, res3) = generate_blocks 4 (max / 4) (k - 1) (Loops.fixed_a a) (generate_blocks4_f #t #a (max / 4) f) init in
    let (c4, res4) = Loops.repeat_gen (k - 1) (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) in
    //assert (c3 == c4 /\ res3 == res4);
    unfold_generate_blocks 4 (max / 4) (Loops.fixed_a a) (generate_blocks4_f #t #a (max / 4) f) init (k - 1);
    Loops.unfold_repeat_gen k (generate_elems4_a t a max) (generate_elems4_f max f) (init, Seq.empty) (k - 1);
    //let (acc', s') = generate_blocks4_f #t #a (max / 4) f (k - 1) c3 in
    //assert (res1 == Seq.append res3 s');
    lemma_generate_elems4_loop_step #t #a max k f (k - 1) c3 res3;
    () end


val lemma_generate_elems4:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a -> Lemma
  (let (c, res) = generate_elems #t #a max n f init in
   let (c1, res1) = generate_blocks 4 (max / 4) (n / 4) (Loops.fixed_a a) (generate_blocks4_f #t #a (max / 4) f) init in
   let (c2, res2) = Loops.repeat_right (n / 4 * 4) n (generate_elem_a t a max) (generate_elem_f max f) (c1, res1) in
   c == c2 /\ res == res2)

let lemma_generate_elems4 #t #a max n f init =
  lemma_generate_elems4_loop #t #a max n f init;
  lemma_generate_elems_unroll4 #t #a max n f init
