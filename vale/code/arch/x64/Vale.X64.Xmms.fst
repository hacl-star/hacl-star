module Vale.X64.Xmms
open FStar.Mul
open Vale.X64.Machine_s
(*
let of_fun m =
  let m0_3 = ((m 0, m 1), (m 2, m 3)) in
  let m4_7 = ((m 4, m 5), (m 6, m 7)) in
  let m8_11 = ((m 8, m 9), (m 10, m 11)) in
  let m12_15 = ((m 12, m 13), (m 14, m 15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m  0 == sel  0 m');
  assert_norm (m  1 == sel  1 m');
  assert_norm (m  2 == sel  2 m');
  assert_norm (m  3 == sel  3 m');
  assert_norm (m  4 == sel  4 m');
  assert_norm (m  5 == sel  5 m');
  assert_norm (m  6 == sel  6 m');
  assert_norm (m  7 == sel  7 m');
  assert_norm (m  8 == sel  8 m');
  assert_norm (m  9 == sel  9 m');
  assert_norm (m 10 == sel 10 m');
  assert_norm (m 11 == sel 11 m');
  assert_norm (m 12 == sel 12 m');
  assert_norm (m 13 == sel 13 m');
  assert_norm (m 14 == sel 14 m');
  assert_norm (m 15 == sel 15 m');
  m'

let lemma_upd_eq r v m =
  assert_norm (sel r (upd r v m) == v)

let lemma_upd_ne r r' v m =
  assert_norm (sel r (upd r' v m) == sel r m)

let equal m1 m2 = m1 == m2

let lemma_equal_intro m1 m2 =
  assert_norm (forall (r:xmm). sel r m1 == Vale.Lib.Map16.sel m1 r);
  assert_norm (forall (r:xmm). sel r m2 == Vale.Lib.Map16.sel m2 r);
  Vale.Lib.Map16.lemma_equal m1 m2

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
*)
