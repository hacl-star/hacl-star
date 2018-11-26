module X64.Vale.Regs
// This interface should not refer to Semantics_s

open Prop_s
open X64.Machine_s
open Map16

type regs_def = map16 nat64
[@"opaque_to_smt"]
type t = regs_def

type reg_int:eqtype = i:int{0 <= i /\ i < 16}

[@va_qattr]
let reg_to_int (r:reg) : reg_int =
  match r with
  | Rax -> 0
  | Rbx -> 1
  | Rcx -> 2
  | Rdx -> 3
  | Rsi -> 4
  | Rdi -> 5
  | Rbp -> 6
  | Rsp -> 7
  | R8 -> 8
  | R9 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15

[@va_qattr "opaque_to_smt"]
let sel (r:reg) (m:t) : nat64 =
  sel16 m (reg_to_int r)

[@va_qattr "opaque_to_smt"]
let upd (r:reg) (v:nat64) (m:t) : t =
  upd16 m (reg_to_int r) v

// Used in eta-expansion; we ensure that it stops normalization by not marking it va_qattr
[@"opaque_to_smt"]
let eta_sel (r:reg) (m:t) : v:nat64{v == sel r m} =
  sel r m

// Eta-expand into a map where normalization gracefully terminates to eta_sel applications,
// so that we don't accidentally normalize past type abstractions
[@va_qattr "opaque_to_smt"]
let eta (m:t) : t =
  let m0_3 = ((eta_sel Rax m, eta_sel Rbx m), (eta_sel Rcx m, eta_sel Rdx m)) in
  let m4_7 = ((eta_sel Rsi m, eta_sel Rdi m), (eta_sel Rbp m, eta_sel Rsp m)) in
  let m8_11 = ((eta_sel R8 m, eta_sel R9 m), (eta_sel R10 m, eta_sel R11 m)) in
  let m12_15 = ((eta_sel R12 m, eta_sel R13 m), (eta_sel R14 m, eta_sel R15 m)) in
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
