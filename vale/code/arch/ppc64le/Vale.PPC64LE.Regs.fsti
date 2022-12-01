module Vale.PPC64LE.Regs
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.PPC64LE.Machine_s

module F = FStar.FunctionalExtensionality
type t = F.restricted_t reg (fun _ -> nat64)

val equal (regs1:t) (regs2:t) : prop0

val lemma_equal_intro (regs1:t) (regs2:t) : Lemma
  (requires forall r. regs1 r == regs2 r)
  (ensures equal regs1 regs2)
  [SMTPat (equal regs1 regs2)]

val lemma_equal_elim (regs1:t) (regs2:t) : Lemma
  (requires equal regs1 regs2)
  (ensures regs1 == regs2)
  [SMTPat (equal regs1 regs2)]

