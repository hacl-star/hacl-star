module Vale.X64.Flags
open Vale.X64.Machine_s

let of_fun m =
  let m0_3 = ((m rRax, m rRbx), (m rRcx, m rRdx)) in
  let m4_7 = ((m rRsi, m rRdi), (m rRbp, m rRsp)) in
  let m8_11 = ((m rR8, m rR9), (m rR10, m rR11)) in
  let m12_15 = ((m rR12, m rR13), (m rR14, m rR15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m rRax == sel rRax m');
  assert_norm (m rRbx == sel rRbx m');
  assert_norm (m rRcx == sel rRcx m');
  assert_norm (m rRdx == sel rRdx m');
  assert_norm (m rRsi == sel rRsi m');
  assert_norm (m rRdi == sel rRdi m');
  assert_norm (m rRbp == sel rRbp m');
  assert_norm (m rRsp == sel rRsp m');
  assert_norm (m rR8  == sel rR8  m');
  assert_norm (m rR9  == sel rR9  m');
  assert_norm (m rR10 == sel rR10 m');
  assert_norm (m rR11 == sel rR11 m');
  assert_norm (m rR12 == sel rR12 m');
  assert_norm (m rR13 == sel rR13 m');
  assert_norm (m rR14 == sel rR14 m');
  assert_norm (m rR15 == sel rR15 m');
  m'

let lemma_upd_eq r v m =
  assert_norm (sel r (upd r v m) == v)

let lemma_upd_ne r r' v m =
  assert_norm (sel r (upd r' v m) == sel r m)

let equal m1 m2 = m1 == m2

let lemma_equal_intro m1 m2 =
  assert_norm (forall (r:flag). sel r m1 == Vale.Lib.Map16.sel m1 r);
  assert_norm (forall (r:flag). sel r m2 == Vale.Lib.Map16.sel m2 r);
  Vale.Lib.Map16.lemma_equal m1 m2

let lemma_equal_elim m1 m2 = ()

let lemma_eta m =
  let m1 = m in
  let m2 = eta m in
  assert_norm (sel rRax m1 == sel rRax m2);
  assert_norm (sel rRbx m1 == sel rRbx m2);
  assert_norm (sel rRcx m1 == sel rRcx m2);
  assert_norm (sel rRdx m1 == sel rRdx m2);
  assert_norm (sel rRsi m1 == sel rRsi m2);
  assert_norm (sel rRdi m1 == sel rRdi m2);
  assert_norm (sel rRbp m1 == sel rRbp m2);
  assert_norm (sel rRsp m1 == sel rRsp m2);
  assert_norm (sel rR8  m1 == sel rR8  m2);
  assert_norm (sel rR9  m1 == sel rR9  m2);
  assert_norm (sel rR10 m1 == sel rR10 m2);
  assert_norm (sel rR11 m1 == sel rR11 m2);
  assert_norm (sel rR12 m1 == sel rR12 m2);
  assert_norm (sel rR13 m1 == sel rR13 m2);
  assert_norm (sel rR14 m1 == sel rR14 m2);
  assert_norm (sel rR15 m1 == sel rR15 m2);
  lemma_equal_intro m1 m2
