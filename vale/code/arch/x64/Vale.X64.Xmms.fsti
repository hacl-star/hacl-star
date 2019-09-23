module Vale.X64.Xmms
open FStar.Mul
// This interface should not refer to Machine_Semantics_s
(*
open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Lib.Map16

unfold let quad32 = Vale.Def.Types_s.quad32
type xmms_def = map16 quad32
[@"opaque_to_smt"]
type t = xmms_def

[@va_qattr "opaque_to_smt"]
let sel (r:xmm) (m:t) : quad32 =
  sel16 m r

[@va_qattr "opaque_to_smt"]
let upd (r:xmm) (v:quad32) (m:t) : t =
  upd16 m r v

// Used in eta-expansion; we ensure that it stops normalization by not marking it va_qattr
[@"opaque_to_smt"]
let eta_sel (r:xmm) (m:t) : v:quad32{v == sel r m} =
  sel r m

// Eta-expand into a map where normalization gracefully terminates to eta_sel applications,
// so that we don't accidentally normalize past type abstractions
[@va_qattr "opaque_to_smt"]
let eta (m:t) : t =
  let m0_3 = ((eta_sel 0 m, eta_sel 1 m), (eta_sel 2 m, eta_sel 3 m)) in
  let m4_7 = ((eta_sel 4 m, eta_sel 5 m), (eta_sel 6 m, eta_sel 7 m)) in
  let m8_11 = ((eta_sel 8 m, eta_sel 9 m), (eta_sel 10 m, eta_sel 11 m)) in
  let m12_15 = ((eta_sel 12 m, eta_sel 13 m), (eta_sel 14 m, eta_sel 15 m)) in
  ((m0_3, m4_7), (m8_11, m12_15))

let to_fun (m:t) : (FStar.FunctionalExtensionality.restricted_t xmm (fun _ -> quad32)) =
  FStar.FunctionalExtensionality.on xmm (fun (r:xmm) -> sel r m)

val of_fun (m:xmm -> quad32) : Pure t
  (requires True)
  (ensures fun m' -> (forall (r:xmm).{:pattern (m r) \/ (sel r m')} m r == sel r m'))

val lemma_upd_eq (r:xmm) (v:quad32) (m:t) : Lemma
  (requires True)
  (ensures sel r (upd r v m) == v)
  [SMTPat (sel r (upd r v m))]

val lemma_upd_ne (r r':xmm) (v:quad32) (m:t) : Lemma
  (requires r =!= r')
  (ensures sel r (upd r' v m) == sel r m)
  [SMTPat (sel r (upd r' v m))]

val equal (xmms1:t) (xmms2:t) : prop0

val lemma_equal_intro (xmms1:t) (xmms2:t) : Lemma
  (requires forall (r:xmm). sel r xmms1 == sel r xmms2)
  (ensures equal xmms1 xmms2)
  [SMTPat (equal xmms1 xmms2)]

val lemma_equal_elim (xmms1:t) (xmms2:t) : Lemma
  (requires equal xmms1 xmms2)
  (ensures xmms1 == xmms2)
  [SMTPat (equal xmms1 xmms2)]

val lemma_eta (m:t) : Lemma
  (requires True)
  (ensures eta m == m)
  [SMTPat (eta m)]
*)
