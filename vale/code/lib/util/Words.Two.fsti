module Words.Two

open Types_s
open Words_s
open Words.Two_s
open FStar.Mul

val nat_to_two_to_nat (n1 n2:nat32) : Lemma
  (nat_to_two 32 (two_to_nat 32 (Mktwo n1 n2)) == Mktwo n1 n2)
  [SMTPat (nat_to_two 32 (two_to_nat 32 (Mktwo n1 n2)))]
