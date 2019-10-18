module Vale.X64.Flags
open FStar.Mul
open Vale.X64.Machine_s

type t = (m:Map.t flag flag_val_t{Set.equal (Map.domain m) (Set.complement Set.empty)})

[@va_qattr "opaque_to_smt"]
let sel (r:flag) (m:t) : flag_val_t =
  Map.sel m r

[@va_qattr "opaque_to_smt"]
let upd (r:flag) (v:flag_val_t) (m:t) : t =
  reveal_opaque (`%t) t;
  Map.upd m r v

let of_fun m =
  let m' = Map.const None in
  let m' = Map.upd m' 0 (m 0) in
  let m' = Map.upd m' 1 (m 1) in
  let m' = Map.upd m' 2 (m 2) in
  let m' = Map.upd m' 3 (m 3) in
  let m' = Map.upd m' 4 (m 4) in
  let m' = Map.upd m' 5 (m 5) in
  let m' = Map.upd m' 6 (m 6) in
  let m' = Map.upd m' 7 (m 7) in
  let m' = Map.upd m' 8 (m 8) in
  let m' = Map.upd m' 9 (m 9) in
  let m' = Map.upd m' 10 (m 10) in
  let m' = Map.upd m' 11 (m 11) in
  let m' = Map.upd m' 12 (m 12) in
  let m' = Map.upd m' 13 (m 13) in
  let m' = Map.upd m' 14 (m 14) in
  let m' = Map.upd m' 15 (m 15) in
  assert_norm (m 0 == sel 0 m');
  assert_norm (m 1 == sel 1 m');
  assert_norm (m 2 == sel 2 m');
  assert_norm (m 3 == sel 3 m');
  assert_norm (m 4 == sel 4 m');
  assert_norm (m 5 == sel 5 m');
  assert_norm (m 6 == sel 6 m');
  assert_norm (m 7 == sel 7 m');
  assert_norm (m 8 == sel 8 m');
  assert_norm (m 9 == sel 9 m');
  assert_norm (m 10 == sel 10 m');
  assert_norm (m 11 == sel 11 m');
  assert_norm (m 12 == sel 12 m');
  assert_norm (m 13 == sel 13 m');
  assert_norm (m 14 == sel 14 m');
  assert_norm (m 15 == sel 15 m');
  m'

let lemma_upd_eq r v m =
  reveal_opaque (`%sel) sel;
  reveal_opaque (`%upd) upd;
  Map.lemma_SelUpd1 m r v

let lemma_upd_ne r r' v m =
  reveal_opaque (`%sel) sel;
  reveal_opaque (`%upd) upd;
  Map.lemma_SelUpd2 m r r' v

let equal m1 m2 = m1 == m2

let lemma_equal_intro m1 m2 =
  assert_norm (forall (r:flag). sel r m1 == Map.sel m1 r);
  assert_norm (forall (r:flag). sel r m2 == Map.sel m2 r);
  reveal_opaque (`%t) t;
  Map.lemma_equal_intro m1 m2

let lemma_equal_elim m1 m2 = ()
