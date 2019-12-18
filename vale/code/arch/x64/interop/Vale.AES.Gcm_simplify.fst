module Vale.AES.Gcm_simplify

open FStar.Mul
open Vale.SHA.Simplify_Sha

let le_bytes_to_seq_quad32_uint8_to_nat8_length s =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32

let gcm_simplify1 b h n =
  let db = get_downview b in
  DV.length_eq db;
  let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
  UV.length_eq ub;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b h

let gcm_simplify2 b h =
  let view = Vale.Interop.Views.up_view128 in
  let s_init = B.as_seq h b in
  let db = get_downview b in
  let s_down = DV.as_seq h db in
  DV.length_eq db;
  assert (DV.length (get_downview b) / 16 = 1);
  let b_v = UV.mk_buffer db view in
  UV.length_eq b_v;
  UV.get_sel h b_v 0;
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index s_init i == Seq.index s_down i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Vale.Interop.Views.get8_reveal ()
  in Classical.forall_intro aux;
  assert (Seq.equal (DV.as_seq h db) (B.as_seq h b));
  Vale.Interop.Views.get128_reveal ();
  le_quad32_to_bytes_to_quad32 (seq_uint8_to_seq_nat8 s_init)

open Vale.Lib.Seqs_s
open Vale.Def.Words.Four_s

val be_quad32_to_bytes_sel (q : quad32) (i:nat{i < 16}) :
    Lemma(let Mkfour q0 q1 q2 q3 = q in
              (i < 4 ==> Seq.index (be_quad32_to_bytes q) i = four_select (nat_to_four 8 q3) (3 - i % 4)) /\
              (4 <= i /\ i < 8 ==> Seq.index (be_quad32_to_bytes q) i = four_select (nat_to_four 8 q2) (3 - i % 4)) /\
               (8 <= i /\ i < 12  ==> Seq.index (be_quad32_to_bytes q) i = four_select (nat_to_four 8 q1) (3 - i % 4)) /\
              (12 <= i /\ i < 16 ==> Seq.index (be_quad32_to_bytes q) i = four_select (nat_to_four 8 q0) (3 - i % 4)))

open FStar.Tactics

#push-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=true --max_fuel 2 --initial_fuel 2 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.nl_arith_repr native --z3rlimit 10"

let be_quad32_to_bytes_sel q i =
  reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes;
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat8);
  let Mkfour q0 q1 q2 q3 = q in
  assert (Seq.index (Vale.Def.Words.Seq_s.four_to_seq_BE q) 0 == q3);
  assert (Seq.index (Vale.Def.Words.Seq_s.four_to_seq_BE q) 1 == q2);
  assert (Seq.index (Vale.Def.Words.Seq_s.four_to_seq_BE q) 2 == q1);
  assert (Seq.index (Vale.Def.Words.Seq_s.four_to_seq_BE q) 3 == q0);
  let Mkfour q00 q01 q02 q03 = nat_to_four 8 q0 in
  let Mkfour q10 q11 q12 q13 = nat_to_four 8 q1 in
  let Mkfour q20 q21 q22 q23 = nat_to_four 8 q2 in
  let Mkfour q30 q31 q32 q33 = nat_to_four 8 q3 in
  assert_by_tactic (four_select (nat_to_four 8 q0) 0 == q00)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q0) 1 == q01)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q0) 2 == q02)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q0) 3 == q03)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);

  assert_by_tactic (four_select (nat_to_four 8 q1) 0 == q10)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q1) 1 == q11)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q1) 2 == q12)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q1) 3 == q13)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);

  assert_by_tactic (four_select (nat_to_four 8 q2) 0 == q20)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q2) 1 == q21)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q2) 2 == q22)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q2) 3 == q23)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);

  assert_by_tactic (four_select (nat_to_four 8 q3) 0 == q30)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q3) 1 == q31)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q3) 2 == q32)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);
  assert_by_tactic (four_select (nat_to_four 8 q3) 3 == q33)
    (fun () -> norm[delta_only [`%Vale.Def.Words.Four_s.four_select]]);

  assert(i < 4 ==> (fun n ->
    four_select (Seq.index (Seq.init (Seq.length (four_to_seq_BE q))
                       (fun x -> nat_to_four 8 (Seq.index (four_to_seq_BE q) x)))
                            (n / 4))
                       (n % 4)) i == four_select (nat_to_four 8 q3) i);
  assert(4 <= i /\ i < 8 ==> (fun n ->
    four_select (Seq.index (Seq.init (Seq.length (four_to_seq_BE q))
                (fun x -> nat_to_four 8 (Seq.index (four_to_seq_BE q) x)))
                (n / 4))
                   (n % 4)) i == four_select (nat_to_four 8 q2) (i % 4));
  assert(8 <= i /\ i < 12 ==> (fun n ->
    four_select (Seq.index (Seq.init (Seq.length (four_to_seq_BE q))
                (fun x -> nat_to_four 8 (Seq.index (four_to_seq_BE q) x)))
                (n / 4))
                   (n % 4)) i == four_select (nat_to_four 8 q1) (i % 4));
  assert(12 <= i /\ i < 16 ==> (fun n ->
    four_select (Seq.index (Seq.init (Seq.length (four_to_seq_BE q))
                (fun x -> nat_to_four 8 (Seq.index (four_to_seq_BE q) x)))
                (n / 4))
                   (n % 4)) i == four_select (nat_to_four 8 q0) (i % 4));
  assert_by_tactic (i < 16 ==> Seq.index (be_quad32_to_bytes q) i =
                   (Seq.index (Seq.init (Seq.length (Seq.init (Seq.length (four_to_seq_BE q))
                          (fun x -> nat_to_four 8 (Seq.index (four_to_seq_BE q) x))) *
                                                                      4)
                          (fun n ->
                            four_select (Seq.index (Seq.init (Seq.length (four_to_seq_BE q))
                                        (fun x -> nat_to_four 8 (Seq.index (four_to_seq_BE q) x)))
                            (n / 4))
                          (3 - n % 4))) i))
                       (fun () -> norm[primops; delta_only [`%Vale.Def.Types_s.le_quad32_to_bytes;
                          `%Vale.Lib.Seqs_s.seq_map; `%Vale.Lib.Seqs_s.compose;
                            `%Vale.Def.Words.Seq_s.seq_four_to_seq_LE]]);
  assert(i < 4 ==> Seq.index (be_quad32_to_bytes q) i == four_select (nat_to_four 8 q3) (3 - i));
  assert(4 <= i /\ i < 8 ==> Seq.index (be_quad32_to_bytes q) i == four_select (nat_to_four 8 q2) (3 - i % 4));
  assert(8 <= i /\ i < 12 ==> Seq.index (be_quad32_to_bytes q) i == four_select (nat_to_four 8 q1) (3 - i % 4));
  assert(12 <= i /\ i < 16 ==> Seq.index (be_quad32_to_bytes q) i == four_select (nat_to_four 8 q0) (3 - i % 4))

#pop-options


let reverse_nat32_four_to_nat (n:nat32) (i:nat{i < 4}) : Lemma
  (four_select (nat_to_four 8 n) i == four_select (nat_to_four 8 (reverse_bytes_nat32 n)) (3 - i))
  = reverse_bytes_nat32_reveal ()

val reverse_bytes_four_select (q:quad32) (i:nat{i < 4}) : Lemma
  (let Mkfour q0 q1 q2 q3 = q in
   let Mkfour q0' q1' q2' q3' = reverse_bytes_quad32 q in
   four_select (nat_to_four 8 q3') (3 - i) = four_select (nat_to_four 8 q0) i /\
   four_select (nat_to_four 8 q2') (3 - i) = four_select (nat_to_four 8 q1) i /\
   four_select (nat_to_four 8 q1') (3 - i) = four_select (nat_to_four 8 q2) i /\
   four_select (nat_to_four 8 q0') (3 - i) = four_select (nat_to_four 8 q3) i)


let reverse_bytes_four_select q i =
  let Mkfour q0 q1 q2 q3 = q in
  let Mkfour q0' q1' q2' q3' = reverse_bytes_quad32 q in
  reveal_reverse_bytes_quad32 q;
  Classical.forall_intro (reverse_nat32_four_to_nat q0);
  Classical.forall_intro (reverse_nat32_four_to_nat q1);
  Classical.forall_intro (reverse_nat32_four_to_nat q2);
  Classical.forall_intro (reverse_nat32_four_to_nat q3)

let simplify_be_quad32 (q:quad32) : Lemma
  (be_quad32_to_bytes (reverse_bytes_quad32 q) == le_quad32_to_bytes q)
  = reveal_reverse_bytes_quad32 q;
  let q_rev = reverse_bytes_quad32 q in
  let q_f = be_quad32_to_bytes q_rev in
 let aux (i:nat{i < 16}) : Lemma (Seq.index q_f i == Seq.index (le_quad32_to_bytes q) i) =
   Vale.AES.GCM_helpers.le_quad32_to_bytes_sel q i;
   be_quad32_to_bytes_sel q_rev i;
   reverse_bytes_four_select q (i % 4)
  in Classical.forall_intro aux;
  assert (Seq.equal q_f (le_quad32_to_bytes q))

let gcm_simplify3 b h =
  let db = get_downview b in
  DV.length_eq db;
  assert (DV.length (get_downview b) / 16 = 1);
  simplify_be_quad32 (low_buffer_read TUInt8 TUInt128 h b 0);
  gcm_simplify2 b h

let lemma_same_seq_dv (h:HS.mem) (b:B.buffer UInt8.t) : Lemma
  (Seq.equal (B.as_seq h b) (DV.as_seq h (get_downview b))) =
  let db = get_downview b in
  DV.length_eq db;
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index (B.as_seq h b) i == Seq.index (DV.as_seq h db) i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Vale.Interop.Views.put8_reveal ()
  in Classical.forall_intro aux

#reset-options "--z3rlimit 250 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

let aes_simplify_aux (s:seq16 nat8) : Lemma
  (seq_nat8_to_seq_nat32_LE s == quad32_to_seq (le_bytes_to_quad32 s))
  = le_bytes_to_quad32_reveal ();
    assert (Seq.equal (seq_nat8_to_seq_nat32_LE s) (quad32_to_seq (le_bytes_to_quad32 s)))

#push-options "--z3cliopt smt.arith.nl=true"
let aes_simplify1 b h =
  let view = Vale.Interop.Views.up_view128 in
  let s_init = B.as_seq h b in
  let db = get_downview b in
  let s_down = DV.as_seq h db in
  DV.length_eq db;
  assert (DV.length (get_downview b) / 16 = 1);
  let b_v = UV.mk_buffer db view in
  UV.length_eq b_v;
  UV.get_sel h b_v 0;
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index s_init i == Seq.index s_down i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Vale.Interop.Views.get8_reveal ()
  in Classical.forall_intro aux;
  assert (Seq.equal (DV.as_seq h db) (B.as_seq h b));
  assert (quad32_to_seq (low_buffer_read TUInt8 TUInt128 h b 0) ==
    four_to_seq_LE (Vale.Interop.Views.get128 (B.as_seq h b)));
  Vale.Interop.Views.get128_reveal ();
  aes_simplify_aux (seq_uint8_to_seq_nat8 s_init)
#pop-options

#push-options "--z3cliopt smt.arith.nl=true"
let aes_simplify2 b h =
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
  let view = Vale.Interop.Views.up_view128 in
  let s_init = B.as_seq h b in
  let db = get_downview b in
  let s_down = DV.as_seq h db in
  DV.length_eq db;
  assert (DV.length (get_downview b) / 16 = 2);
  let b_v = UV.mk_buffer db view in
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index s_init i == Seq.index s_down i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Vale.Interop.Views.get8_reveal ()
  in Classical.forall_intro aux;
  assert (Seq.equal (DV.as_seq h db) (B.as_seq h b));
  UV.length_eq b_v;
  UV.get_sel h b_v 0;
  UV.get_sel h b_v 1;
  Vale.Interop.Views.get128_reveal ();
  aes_simplify_aux (seq_uint8_to_seq_nat8 (Seq.slice s_init 0 16));
  aes_simplify_aux (seq_uint8_to_seq_nat8 (Seq.slice s_init 16 32));
  assert (Seq.equal
    (make_AES256_key  (low_buffer_read TUInt8 TUInt128 h b 0) (low_buffer_read TUInt8 TUInt128 h b 1))
    (Seq.append
      (seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (Seq.slice s_init 0 16)))
      (seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (Seq.slice s_init 16 32)))
    ))
#pop-options

let aes_simplify3 b h s =
  let db = get_downview b in
  DV.length_eq db;
  let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
  assert (s == UV.as_seq h ub);
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b h
