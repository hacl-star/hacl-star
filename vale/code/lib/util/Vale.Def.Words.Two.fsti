module Vale.Def.Words.Two

open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open FStar.Mul

val nat_to_two_to_nat (n1 n2:nat32) : Lemma
  (nat_to_two 32 (two_to_nat 32 (Mktwo n1 n2)) == Mktwo n1 n2)
  [SMTPat (nat_to_two 32 (two_to_nat 32 (Mktwo n1 n2)))]

val two_to_nat_to_two (n:nat64) : Lemma
  (two_to_nat 32 (nat_to_two 32 n) == n)
  [SMTPat (two_to_nat 32 (nat_to_two 32 n))]

val two_to_nat_32_injective (_:unit) : Lemma
  (forall (x x':two (natN (pow2_norm 32))).{:pattern two_to_nat 32 x; two_to_nat 32 x'}
    two_to_nat 32 x == two_to_nat 32 x' ==> x == x')
