module Vale.X64.Flags
open FStar.Mul
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Lib.Map16

unfold let flag_val_t = option bool // HACK: this shouldn't have to be unfolded (it has to do with the lambda in FStar.FunctionalExtensionality.(^->))

val t : Type0

val sel (f:flag) (m:t) : flag_val_t

val upd (f:flag) (v:flag_val_t) (m:t) : t

let sel_curry (m:t) (f:flag) : flag_val_t = sel f m

let to_fun (m:t) : (FStar.FunctionalExtensionality.restricted_t flag (fun _ -> flag_val_t)) =
  FStar.FunctionalExtensionality.on flag (sel_curry m)

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
