module Vale.X64.Flags
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Lib.Map16

type flag_val_t = option bool

type flags_def = (m:Map.t flag flag_val_t{Set.equal (Map.domain m) (Set.complement Set.empty)})
[@"opaque_to_smt"]
type t = flags_def

[@va_qattr "opaque_to_smt"]
let sel (r:flag) (m:t) : flag_val_t =
  Map.sel m r

[@va_qattr "opaque_to_smt"]
let upd (r:flag) (v:flag_val_t) (m:t) : t =
  reveal_opaque (`%t) t;
  Map.upd m r v

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
