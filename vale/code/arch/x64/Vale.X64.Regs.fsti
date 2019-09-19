module Vale.X64.Regs
open FStar.Mul
// This interface should not refer to Machine_Semantics_s

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Lib.Map16

type regs_fun = FStar.FunctionalExtensionality.restricted_t reg t_reg
type regs_def = map16 nat64 & map16 quad32

[@"opaque_to_smt"]
type t = regs_def

[@va_qattr "opaque_to_smt"]
let sel (r:reg) (m:t) : t_reg r =
  match m with (m0, m1) ->
  match r with Reg rf i ->
  match rf with
  | 0 -> sel16 m0 i
  | 1 -> sel16 m1 i

[@va_qattr "opaque_to_smt"]
let upd (r:reg) (v:t_reg r) (m:t) : t =
  match m with (m0, m1) ->
  match r with Reg rf i ->
  match rf with
  | 0 -> (upd16 m0 i v, m1)
  | 1 -> (m0, upd16 m1 i v)

// Used in eta-expansion; we ensure that it stops normalization by not marking it va_qattr
[@"opaque_to_smt"]
let eta_sel (r:reg) (m:t) : v:(t_reg r){v == sel r m} =
  sel r m

// Eta-expand into a map where normalization gracefully terminates to eta_sel applications,
// so that we don't accidentally normalize past type abstractions
[@va_qattr "opaque_to_smt"]
let eta (m:t) : t =
  let m0_3 = ((eta_sel (Reg 0 0) m, eta_sel (Reg 0 1) m), (eta_sel (Reg 0 2) m, eta_sel (Reg 0 3) m)) in
  let m4_7 = ((eta_sel (Reg 0 4) m, eta_sel (Reg 0 5) m), (eta_sel (Reg 0 6) m, eta_sel (Reg 0 7) m)) in
  let m8_11 = ((eta_sel (Reg 0 8) m, eta_sel (Reg 0 9) m), (eta_sel (Reg 0 10) m, eta_sel (Reg 0 11) m)) in
  let m12_15 = ((eta_sel (Reg 0 12) m, eta_sel (Reg 0 13) m), (eta_sel (Reg 0 14) m, eta_sel (Reg 0 15) m)) in
  let m0 = ((m0_3, m4_7), (m8_11, m12_15)) in
  let m0_3 = ((eta_sel (Reg 1 0) m, eta_sel (Reg 1 1) m), (eta_sel (Reg 1 2) m, eta_sel (Reg 1 3) m)) in
  let m4_7 = ((eta_sel (Reg 1 4) m, eta_sel (Reg 1 5) m), (eta_sel (Reg 1 6) m, eta_sel (Reg 1 7) m)) in
  let m8_11 = ((eta_sel (Reg 1 8) m, eta_sel (Reg 1 9) m), (eta_sel (Reg 1 10) m, eta_sel (Reg 1 11) m)) in
  let m12_15 = ((eta_sel (Reg 1 12) m, eta_sel (Reg 1 13) m), (eta_sel (Reg 1 14) m, eta_sel (Reg 1 15) m)) in
  let m1 = ((m0_3, m4_7), (m8_11, m12_15)) in
  (m0, m1)

let to_fun (m:t) : regs_fun =
  FStar.FunctionalExtensionality.on_dom reg (fun (r:reg) -> sel r m)

val of_fun (m:(r:reg -> t_reg r)) : Pure t
  (requires True)
  (ensures fun m' -> (forall (r:reg).{:pattern (m r) \/ (sel r m')} m r == sel r m'))

val lemma_upd_eq (r:reg) (v:t_reg r) (m:t) : Lemma
  (requires True)
  (ensures sel r (upd r v m) == v)
  [SMTPat (sel r (upd r v m))]

val lemma_upd_ne (r r':reg) (v:t_reg r') (m:t) : Lemma
  (requires r =!= r')
  (ensures sel r (upd r' v m) == sel r m)
  [SMTPat (sel r (upd r' v m))]

val equal (regs1:t) (regs2:t) : prop0

val lemma_equal_intro (regs1:t) (regs2:t) : Lemma
  (requires forall (r:reg). sel r regs1 == sel r regs2)
  (ensures equal regs1 regs2)
  [SMTPat (equal regs1 regs2)]

val lemma_equal_elim (regs1:t) (regs2:t) : Lemma
  (requires equal regs1 regs2)
  (ensures regs1 == regs2)
  [SMTPat (equal regs1 regs2)]

val lemma_eta (m:t) : Lemma
  (requires True)
  (ensures eta m == m)
  [SMTPat (eta m)]
