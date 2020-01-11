module Vale.Lib.Map16
open FStar.Mul

let lemma_self16 (#a:Type) (m:map16 a) (n:int) (v:a) = ()
let lemma_other16 (#a:Type) (m:map16 a) (n1 n2:int) (v:a) = ()

#reset-options "--initial_ifuel 5 --max_ifuel 5"
let lemma_equal16 (#a:Type) (m1 m2:map16 a) =
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

let lemma_self (#a:Type) (m:map16 a) (n:int) (v:a) =
  assert_norm (sel (upd m n v) n == sel16 (upd16 m n v) n);
  lemma_self16 m n v

let lemma_other (#a:Type) (m:map16 a) (n1 n2:int) (v:a) =
  assert_norm (sel (upd m n1 v) n2 == sel16 (upd16 m n1 v) n2);
  assert_norm (sel m n2 == sel16 m n2);
  lemma_other16 m n1 n2 v

let lemma_equal (#a:Type) (m1 m2:map16 a) =
  assert_norm (forall (i:int). sel m1 i == sel16 m1 i);
  assert_norm (forall (i:int). sel m2 i == sel16 m2 i);
  lemma_equal16 m1 m2

let lemma_eta16 (#a:Type) (m:map16 a) =
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

let lemma_eta (#a:Type) (m:map16 a) =
  assert_norm (eta m == eta16 m);
  lemma_eta16 m

let equal #a m1 m2 = m1 == m2

let lemma_equal_intro #a m1 m2 =
  lemma_equal m1 m2;
  ()

let lemma_equal_elim #a m1 m2 =
  ()

let rec init_rec (a:Type) (f:(i:nat{i < 16}) -> a) (n:nat) : Pure (map16 a)
  (requires n <= 16)
  (ensures fun m -> forall (i:nat).{:pattern sel m i} i < n ==> sel m i == f i)
  =
  if n = 0 then
    let m1 = f 0 in
    let m4 = ((m1, m1), (m1, m1)) in
    ((m4, m4), (m4, m4))
  else
    upd (init_rec a f (n - 1)) (n - 1) (f (n - 1))

let init a f =
  init_rec a f 16

let rec init_ghost_rec (a:Type) (f:(i:nat{i < 16}) -> GTot a) (n:nat) : Ghost (map16 a)
  (requires n <= 16)
  (ensures fun m -> forall (i:nat).{:pattern sel m i} i < n ==> sel m i == f i)
  =
  if n = 0 then
    let m1 = f 0 in
    let m4 = ((m1, m1), (m1, m1)) in
    ((m4, m4), (m4, m4))
  else
    upd (init_ghost_rec a f (n - 1)) (n - 1) (f (n - 1))

let init_ghost a f =
  init_ghost_rec a f 16

