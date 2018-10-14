module X64.Vale.Xmms
open X64.Machine_s

let lemma_upd_eq r v m =
  assert_norm (sel r (upd r v m) == v)

let lemma_upd_ne r r' v m =
  assert_norm (sel r (upd r' v m) == sel r m)

let equal m1 m2 = m1 == m2

let lemma_equal_intro m1 m2 =
  assert_norm (forall (r:xmm). sel r m1 == Map16.sel m1 r);
  assert_norm (forall (r:xmm). sel r m2 == Map16.sel m2 r);
  Map16.lemma_equal m1 m2

let lemma_equal_elim m1 m2 = ()

let lemma_eta m =
  let m1 = m in
  let m2 = eta m in
  assert_norm (sel  0 m1 == sel  0 m2);
  assert_norm (sel  1 m1 == sel  1 m2);
  assert_norm (sel  2 m1 == sel  2 m2);
  assert_norm (sel  3 m1 == sel  3 m2);
  assert_norm (sel  4 m1 == sel  4 m2);
  assert_norm (sel  5 m1 == sel  5 m2);
  assert_norm (sel  6 m1 == sel  6 m2);
  assert_norm (sel  7 m1 == sel  7 m2);
  assert_norm (sel  8 m1 == sel  8 m2);
  assert_norm (sel  9 m1 == sel  9 m2);
  assert_norm (sel 10 m1 == sel 10 m2);
  assert_norm (sel 11 m1 == sel 11 m2);
  assert_norm (sel 12 m1 == sel 12 m2);
  assert_norm (sel 13 m1 == sel 13 m2);
  assert_norm (sel 14 m1 == sel 14 m2);
  assert_norm (sel 15 m1 == sel 15 m2);
  lemma_equal_intro m1 m2
