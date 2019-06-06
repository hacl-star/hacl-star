module Vale.X64.Flags
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Lib.Map16

type flag_val_t = option bool

type flags_def = map16 flag_val_t
[@"opaque_to_smt"]
type t = flags_def

[@va_qattr "opaque_to_smt"]
let sel (r:flag) (m:t) : flag_val_t =
  sel16 m r

[@va_qattr "opaque_to_smt"]
let upd (r:flag) (v:flag_val_t) (m:t) : t =
  upd16 m r v

// Used in eta-expansion; we ensure that it stops normalization by not marking it va_qattr
[@"opaque_to_smt"]
let eta_sel (r:flag) (m:t) : v:flag_val_t{v == sel r m} =
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

let to_fun (m:t) : (FStar.FunctionalExtensionality.restricted_t flag (fun _ -> flag_val_t)) =
  FStar.FunctionalExtensionality.on flag (fun (r:flag) -> sel r m)

val of_fun (m:flag -> flag_val_t) : Pure t
  (requires True)
  (ensures fun m' -> (forall (r:flag).{:pattern (m r) \/ (sel r m')} m r == sel r m'))

val lemma_upd_eq (r:flag) (v:flag_val_t) (m:t) : Lemma
  (requires True)
  (ensures sel r (upd r v m) == v)
  [SMTPat (sel r (upd r v m))]

val lemma_upd_ne (r r':flag) (v:flag_val_t) (m:t) : Lemma
  (requires r =!= r')
  (ensures sel r (upd r' v m) == sel r m)
  [SMTPat (sel r (upd r' v m))]

val equal (flags1:t) (flags2:t) : prop0

val lemma_equal_intro (flags1:t) (flags2:t) : Lemma
  (requires forall (r:flag). sel r flags1 == sel r flags2)
  (ensures equal flags1 flags2)
  [SMTPat (equal flags1 flags2)]

val lemma_equal_elim (flags1:t) (flags2:t) : Lemma
  (requires equal flags1 flags2)
  (ensures flags1 == flags2)
  [SMTPat (equal flags1 flags2)]

val lemma_eta (m:t) : Lemma
  (requires True)
  (ensures eta m == m)
  [SMTPat (eta m)]
