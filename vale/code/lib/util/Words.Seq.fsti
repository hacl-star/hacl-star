module Words.Seq

open FStar.Seq
open Words_s
open Words.Four_s
open Words.Seq_s
open FStar.Mul

val two_to_seq_to_two_LE (#a:Type) (x:seq2 a) :
  Lemma (two_to_seq_LE (seq_to_two_LE x) == x)
  [SMTPat (two_to_seq_LE (seq_to_two_LE x))]

val seq_to_two_to_seq_LE (#a:Type) (x:two a) :
  Lemma (seq_to_two_LE (two_to_seq_LE x) == x)
  [SMTPat (seq_to_two_LE (two_to_seq_LE x))]
  
val seq_to_seq_four_to_seq_LE  (#a:Type) (x:seq (four a)) :
  Lemma (seq_to_seq_four_LE (seq_four_to_seq_LE x) == x)
  [SMTPat (seq_to_seq_four_LE (seq_four_to_seq_LE x))]

val seq_to_seq_four_to_seq_BE  (#a:Type) (x:seq (four a)) :
  Lemma (seq_to_seq_four_BE (seq_four_to_seq_BE x) == x)
  [SMTPat (seq_to_seq_four_BE (seq_four_to_seq_BE x))]

val seq_four_to_seq_to_seq_four_LE (#a:Type) (x:seq a{length x % 4 == 0}) :
  Lemma (seq_four_to_seq_LE (seq_to_seq_four_LE x) == x)
  [SMTPat (seq_four_to_seq_LE (seq_to_seq_four_LE x))]

val four_to_nat_to_four_8 (x:natN (pow2_norm 32)) :
  Lemma (four_to_nat 8 (nat_to_four 8 x) == x)
  [SMTPat (four_to_nat 8 (nat_to_four 8 x))]

val nat_to_four_to_nat (x:four (natN (pow2_norm 8))) :
  Lemma (nat_to_four 8 (four_to_nat 8 x) == x)
  [SMTPat (nat_to_four 8 (four_to_nat 8 x))]


val four_to_seq_to_four_LE (#a:Type) (x:seq4 a) :
  Lemma (four_to_seq_LE (seq_to_four_LE x) == x)

val seq_to_four_to_seq_LE (#a:Type) (x:four a) :
  Lemma (seq_to_four_LE (four_to_seq_LE x) == x)

val four_to_seq_to_four_BE (#a:Type) (x:seq4 a) :
  Lemma (four_to_seq_BE (seq_to_four_BE x) == x)

val seq_to_four_to_seq_BE (#a:Type) (x:four a) :
  Lemma (seq_to_four_BE (four_to_seq_BE x) == x)

val four_to_seq_LE_is_seq_four_to_seq_LE(#a:Type) (x:four a) :
  Lemma (four_to_seq_LE x == seq_four_to_seq_LE (create 1 x))

val seq_nat8_to_seq_nat32_to_seq_nat8_LE (x:seq nat32) :
  Lemma (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE x) == x)
  [SMTPat (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE x))]

val seq_nat32_to_seq_nat8_to_seq_nat32_LE (x:seq nat8{length x % 4 == 0}) :
  Lemma (seq_nat32_to_seq_nat8_LE (seq_nat8_to_seq_nat32_LE x) == x)
  [SMTPat (seq_nat32_to_seq_nat8_LE (seq_nat8_to_seq_nat32_LE x))]

val seq_nat8_to_seq_uint8_to_seq_nat8 (x:seq UInt8.t) :
  Lemma (seq_nat8_to_seq_uint8 (seq_uint8_to_seq_nat8 x) == x)
  [SMTPat (seq_nat8_to_seq_uint8 (seq_uint8_to_seq_nat8 x))]

val seq_uint8_to_seq_nat8_to_seq_uint8 (x:seq nat8) :
  Lemma (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 x) == x)
  [SMTPat (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 x))]

val seq_nat8_to_seq_uint8_injective (b b':seq nat8) : Lemma
  (requires equal (seq_nat8_to_seq_uint8 b) (seq_nat8_to_seq_uint8 b'))
  (ensures b == b')

val seq_four_to_seq_LE_injective: (a:eqtype) ->
  Lemma (forall (x x':seq (four a)). seq_four_to_seq_LE x == seq_four_to_seq_LE x' ==> x == x')

val seq_four_to_seq_LE_injective_specific (#a:eqtype) (x x':seq (four a)) :
  Lemma (seq_four_to_seq_LE x == seq_four_to_seq_LE x' ==> x == x')

val four_to_seq_LE_injective (a:eqtype) :
  Lemma (forall (x x': four a) . four_to_seq_LE x == four_to_seq_LE x' ==> x == x')

(*
val seq_to_seq_four_LE_injective: unit ->
  Lemma (forall (#a:Type) (x:seq a{length x % 4 == 0}) (x':seq a{length x' % 4 == 0}) . seq_to_seq_four_LE x == seq_to_seq_four_LE x' ==> x == x')
*)
val four_to_nat_8_injective: unit ->
  Lemma (forall (x x':four (natN (pow2_norm 8))) . four_to_nat 8 x == four_to_nat 8 x' ==> x == x')

val nat_to_four_8_injective: unit ->
  Lemma (forall (x x':natN (pow2_norm 32)) . nat_to_four 8 x == nat_to_four 8 x' ==> x == x')
(*
val seq_to_four_LE_injective: unit ->
  Lemma (forall (#a:Type) (x x':seq4 a) . seq_to_four_LE x == seq_to_four_LE x' ==> x == x')
*)

val append_distributes_seq_to_seq_four_LE (#a:Type) (x:seq a{length x % 4 == 0}) (y:seq a{length y % 4 == 0}) :
  Lemma (seq_to_seq_four_LE (x @| y) == seq_to_seq_four_LE x @| seq_to_seq_four_LE y)

val append_distributes_seq_four_to_seq_LE (#a:Type) (x:seq (four a)) (y:seq (four a)) :
  Lemma (seq_four_to_seq_LE (x @| y) == seq_four_to_seq_LE x @| seq_four_to_seq_LE y)
