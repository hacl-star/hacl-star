module X64.Vale.Regs
// This interface should not refer to Semantics_s

open Prop_s
open X64.Machine_s
open Map16

type regs_def = map16 nat64
[@"opaque_to_smt"]
type t = regs_def

[@va_qattr "opaque_to_smt"]
let sel (r:reg) (m:t) : nat64 =
  sel16 m r

[@va_qattr "opaque_to_smt"]
let upd (r:reg) (v:nat64) (m:t) : t =
  upd16 m r v

// Used in eta-expansion; we ensure that it stops normalization by not marking it va_qattr
[@"opaque_to_smt"]
let eta_sel (r:reg) (m:t) : v:nat64{v == sel r m} =
  sel r m

// Eta-expand into a map where normalization gracefully terminates to eta_sel applications,
// so that we don't accidentally normalize past type abstractions
[@va_qattr "opaque_to_smt"]
let eta (m:t) : t =
  let m0_3 = ((eta_sel rRax m, eta_sel rRbx m), (eta_sel rRcx m, eta_sel rRdx m)) in
  let m4_7 = ((eta_sel rRsi m, eta_sel rRdi m), (eta_sel rRbp m, eta_sel rRsp m)) in
  let m8_11 = ((eta_sel rR8 m, eta_sel rR9 m), (eta_sel rR10 m, eta_sel rR11 m)) in
  let m12_15 = ((eta_sel rR12 m, eta_sel rR13 m), (eta_sel rR14 m, eta_sel rR15 m)) in
  ((m0_3, m4_7), (m8_11, m12_15))

let to_fun (m:t) : (FStar.FunctionalExtensionality.restricted_t reg (fun _ -> nat64)) =
  FStar.FunctionalExtensionality.on reg (fun (r:reg) -> sel r m)

val of_fun (m:reg -> nat64) : Pure t
  (requires True)
  (ensures fun m' -> (forall (r:reg).{:pattern (m r) \/ (sel r m')} m r == sel r m'))

val lemma_upd_eq (r:reg) (v:nat64) (m:t) : Lemma
  (requires True)
  (ensures sel r (upd r v m) == v)
  [SMTPat (sel r (upd r v m))]

val lemma_upd_ne (r r':reg) (v:nat64) (m:t) : Lemma
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
