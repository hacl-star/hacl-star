module X64.Vale.Regs
open X64.Machine_s

let of_fun m =
  let m0_3 = ((m Rax, m Rbx), (m Rcx, m Rdx)) in
  let m4_7 = ((m Rsi, m Rdi), (m Rbp, m Rsp)) in
  let m8_11 = ((m R8, m R9), (m R10, m R11)) in
  let m12_15 = ((m R12, m R13), (m R14, m R15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m Rax == sel Rax m');
  assert_norm (m Rbx == sel Rbx m');
  assert_norm (m Rcx == sel Rcx m');
  assert_norm (m Rdx == sel Rdx m');
  assert_norm (m Rsi == sel Rsi m');
  assert_norm (m Rdi == sel Rdi m');
  assert_norm (m Rbp == sel Rbp m');
  assert_norm (m Rsp == sel Rsp m');
  assert_norm (m R8  == sel R8  m');
  assert_norm (m R9  == sel R9  m');
  assert_norm (m R10 == sel R10 m');
  assert_norm (m R11 == sel R11 m');
  assert_norm (m R12 == sel R12 m');
  assert_norm (m R13 == sel R13 m');
  assert_norm (m R14 == sel R14 m');
  assert_norm (m R15 == sel R15 m');
  m'

let lemma_upd_eq r v m =
  assert_norm (sel r (upd r v m) == v)

let lemma_upd_ne r r' v m =
  assert_norm (sel r (upd r' v m) == sel r m)

let equal m1 m2 = m1 == m2

let lemma_equal_intro m1 m2 =
  assert_norm (forall (r:reg). sel r m1 == Map16.sel m1 (reg_to_int r));
  assert_norm (forall (r:reg). sel r m2 == Map16.sel m2 (reg_to_int r));
  Map16.lemma_equal m1 m2

let lemma_equal_elim m1 m2 = ()

let lemma_eta m =
  let m1 = m in
  let m2 = eta m in
  assert_norm (sel Rax m1 == sel Rax m2);
  assert_norm (sel Rbx m1 == sel Rbx m2);
  assert_norm (sel Rcx m1 == sel Rcx m2);
  assert_norm (sel Rdx m1 == sel Rdx m2);
  assert_norm (sel Rsi m1 == sel Rsi m2);
  assert_norm (sel Rdi m1 == sel Rdi m2);
  assert_norm (sel Rbp m1 == sel Rbp m2);
  assert_norm (sel Rsp m1 == sel Rsp m2);
  assert_norm (sel R8  m1 == sel R8  m2);
  assert_norm (sel R9  m1 == sel R9  m2);
  assert_norm (sel R10 m1 == sel R10 m2);
  assert_norm (sel R11 m1 == sel R11 m2);
  assert_norm (sel R12 m1 == sel R12 m2);
  assert_norm (sel R13 m1 == sel R13 m2);
  assert_norm (sel R14 m1 == sel R14 m2);
  assert_norm (sel R15 m1 == sel R15 m2);
  lemma_equal_intro m1 m2
