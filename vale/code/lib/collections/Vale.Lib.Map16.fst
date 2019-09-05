module Vale.Lib.Map16
open FStar.Mul

let lemma_self16 (#a:Type0) (m:map16 a) (n:int) (v:a) = ()
let lemma_other16 (#a:Type0) (m:map16 a) (n1 n2:int) (v:a) = ()

#reset-options "--initial_ifuel 5 --max_ifuel 5"
let lemma_equal16 (#a:Type0) (m1 m2:map16 a) =
  assert (sel16 m1  0 == sel16 m2  0);
  assert (sel16 m1  1 == sel16 m2  1);
  assert (sel16 m1  2 == sel16 m2  2);
  assert (sel16 m1  3 == sel16 m2  3);
  assert (sel16 m1  4 == sel16 m2  4);
  assert (sel16 m1  5 == sel16 m2  5);
  assert (sel16 m1  6 == sel16 m2  6);
  assert (sel16 m1  7 == sel16 m2  7);
  assert (sel16 m1  8 == sel16 m2  8);
  assert (sel16 m1  9 == sel16 m2  9);
  assert (sel16 m1 10 == sel16 m2 10);
  assert (sel16 m1 11 == sel16 m2 11);
  assert (sel16 m1 12 == sel16 m2 12);
  assert (sel16 m1 13 == sel16 m2 13);
  assert (sel16 m1 14 == sel16 m2 14);
  assert (sel16 m1 15 == sel16 m2 15);
  ()
#reset-options

let lemma_self (#a:Type0) (m:map16 a) (n:int) (v:a) =
  assert_norm (sel (upd m n v) n == sel16 (upd16 m n v) n);
  lemma_self16 m n v

let lemma_other (#a:Type0) (m:map16 a) (n1 n2:int) (v:a) =
  assert_norm (sel (upd m n1 v) n2 == sel16 (upd16 m n1 v) n2);
  assert_norm (sel m n2 == sel16 m n2);
  lemma_other16 m n1 n2 v

let lemma_equal (#a:Type0) (m1 m2:map16 a) =
  assert_norm (forall (i:int). sel m1 i == sel16 m1 i);
  assert_norm (forall (i:int). sel m2 i == sel16 m2 i);
  lemma_equal16 m1 m2

let lemma_eta16 (#a:Type0) (m:map16 a) =
  let m1 = m in
  let m2 = eta16 m in
  assert_norm (get m1  0 == get m2  0);
  assert_norm (get m1  1 == get m2  1);
  assert_norm (get m1  2 == get m2  2);
  assert_norm (get m1  3 == get m2  3);
  assert_norm (get m1  4 == get m2  4);
  assert_norm (get m1  5 == get m2  5);
  assert_norm (get m1  6 == get m2  6);
  assert_norm (get m1  7 == get m2  7);
  assert_norm (get m1  8 == get m2  8);
  assert_norm (get m1  9 == get m2  9);
  assert_norm (get m1 10 == get m2 10);
  assert_norm (get m1 11 == get m2 11);
  assert_norm (get m1 12 == get m2 12);
  assert_norm (get m1 13 == get m2 13);
  assert_norm (get m1 14 == get m2 14);
  assert_norm (get m1 15 == get m2 15);
  lemma_equal m (eta16 m)

let lemma_eta (#a:Type0) (m:map16 a) =
  assert_norm (eta m == eta16 m);
  lemma_eta16 m

