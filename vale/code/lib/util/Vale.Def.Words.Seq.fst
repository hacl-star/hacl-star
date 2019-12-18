module Vale.Def.Words.Seq

open FStar.Seq
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open FStar.Mul
open Vale.Lib.Meta
open Vale.Lib.Seqs_s
open Vale.Lib.Seqs

let two_to_seq_to_two_LE #a x =
  assert (equal (two_to_seq_LE (seq_to_two_LE x)) x)

let seq_to_two_to_seq_LE #a x = ()

let seq_to_seq_four_to_seq_LE  (#a:Type) (x:seq (four a)) :
  Lemma (seq_to_seq_four_LE (seq_four_to_seq_LE x) == x)
  [SMTPat (seq_to_seq_four_LE (seq_four_to_seq_LE x))]
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #a);
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #a);
  let bytes = seq_four_to_seq_LE x in
  let fours = seq_to_seq_four_LE bytes in
  assert (equal fours x);
  ()

let seq_to_seq_four_to_seq_BE  (#a:Type) (x:seq (four a)) :
  Lemma (seq_to_seq_four_BE (seq_four_to_seq_BE x) == x)
  [SMTPat (seq_to_seq_four_BE (seq_four_to_seq_BE x))]
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #a);
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #a);
  assert (equal (seq_to_seq_four_BE (seq_four_to_seq_BE x)) x);
  ()

let seq_four_to_seq_to_seq_four_LE (#a:Type) (x:seq a{length x % 4 == 0}) :
  Lemma (seq_four_to_seq_LE (seq_to_seq_four_LE x) == x)
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #a);
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #a);
  assert (equal (seq_four_to_seq_LE (seq_to_seq_four_LE x)) x);
  ()

unfold let pow2_24 = 16777216 //normalize_term (pow2 24)

#reset-options "--z3rlimit 200 --using_facts_from 'Prims Vale.Def.Words_s'"
let lemma_fundamental_div_mod_4 (x:nat32) :
  Lemma (x = x % pow2_8 + pow2_8 * ((x / pow2_8) % pow2_8) + pow2_16 * ((x / pow2_16) % pow2_8) + pow2_24 * ((x / pow2_24) % pow2_8))
  =
  ()
#reset-options "--z3rlimit 30"

let four_to_nat_to_four_8 (x:natN (pow2_norm 32)) :
  Lemma (four_to_nat 8 (nat_to_four 8 x) == x)
  [SMTPat (four_to_nat 8 (nat_to_four 8 x))]
  =
  let size = 8 in
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let n3 = pow2_norm (3 * size) in
  let n4 = pow2_norm (4 * size) in
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 0x10000);
  assert_norm (pow2 24 == 0x1000000);
  assert_norm (pow2 32 == 0x100000000);
  let fourX = nat_to_four 8 x in
  assert_norm (nat_to_four 8 x == Mkfour (x % n1) ((x / n1) % n1) ((x / n2) % n1) ((x / n3) % n1));
  let Mkfour x0 x1 x2 x3 = fourX in
  let x' = x0 + x1 * n1 + x2 * n2 + x3 * n3 in
  assert_norm (four_to_nat 8 fourX == int_to_natN n4 (x0 + x1 * n1 + x2 * n2 + x3 * n3));
  lemma_fundamental_div_mod_4 x;
  ()

#reset-options "--z3rlimit 400 --using_facts_from 'Vale.Def.Words_s Prims'"
let nat_to_four_to_nat (x:four (natN (pow2_norm 8))) :
  Lemma (nat_to_four 8 (four_to_nat 8 x) == x)
  [SMTPat (nat_to_four 8 (four_to_nat 8 x))]
  =
  let size = 8 in
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let n3 = pow2_norm (3 * size) in
  let n4 = pow2_norm (4 * size) in
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 0x10000);
  assert_norm (pow2 24 == 0x1000000);
  assert_norm (pow2 32 == 0x100000000);
  let x' = four_to_nat 8 x in
  assert_norm (nat_to_four 8 x' == Mkfour (x' % n1) ((x' / n1) % n1) ((x' / n2) % n1) ((x' / n3) % n1));
  let Mkfour x0 x1 x2 x3 = x in
  let x' = x0 + x1 * n1 + x2 * n2 + x3 * n3 in
  assert_norm (four_to_nat 8 x == int_to_natN n4 (x0 + x1 * n1 + x2 * n2 + x3 * n3));
  lemma_fundamental_div_mod_4 x';
  ()

#reset-options
let four_to_seq_to_four_LE (#a:Type) (x:seq4 a) :
  Lemma (four_to_seq_LE (seq_to_four_LE x) == x)
  =
  assert (equal (four_to_seq_LE (seq_to_four_LE x)) x);
  ()

let seq_to_four_to_seq_LE (#a:Type) (x:four a) :
  Lemma (seq_to_four_LE (four_to_seq_LE x) == x)
  =
  ()

let four_to_seq_to_four_BE (#a:Type) (x:seq4 a) :
  Lemma (four_to_seq_BE (seq_to_four_BE x) == x)
  =
  assert (equal (four_to_seq_BE (seq_to_four_BE x)) x);
  ()

let seq_to_four_to_seq_BE (#a:Type) (x:four a) :
  Lemma (seq_to_four_BE (four_to_seq_BE x) == x)
  =
  ()

let four_to_seq_LE_is_seq_four_to_seq_LE(#a:Type) (x:four a) :
  Lemma (four_to_seq_LE x == seq_four_to_seq_LE (create 1 x))
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #a);
  let s0 = four_to_seq_LE x  in
  let s1 = seq_four_to_seq_LE (create 1 x) in
  assert (equal s0 s1);
  ()

let seq_nat8_to_seq_nat32_to_seq_nat8_LE (x:seq nat32) :
  Lemma (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE x) == x)
  =
  assert (equal (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE x)) x);
  ()

let seq_nat32_to_seq_nat8_to_seq_nat32_LE (x:seq nat8{length x % 4 == 0}) :
  Lemma (seq_nat32_to_seq_nat8_LE (seq_nat8_to_seq_nat32_LE x) == x)
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
  assert (equal (seq_nat32_to_seq_nat8_LE (seq_nat8_to_seq_nat32_LE x)) x);
  ()

let seq_nat8_to_seq_uint8_to_seq_nat8 (x:seq UInt8.t) =
  assert (equal (seq_nat8_to_seq_uint8 (seq_uint8_to_seq_nat8 x)) x)

let seq_uint8_to_seq_nat8_to_seq_uint8 (x:seq nat8) =
  assert (equal (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 x)) x)

let seq_nat8_to_seq_uint8_injective b b' =
  seq_map_injective UInt8.uint_to_t b b'

let seq_four_to_seq_LE_injective (a:eqtype) :
  Lemma (forall (x x': seq (four a)). seq_four_to_seq_LE #a x == seq_four_to_seq_LE #a x' ==> x == x')
  =
  let seq_four_to_seq_LE_stronger (#b:Type) (x:seq (four b)) : (s:seq b{length s % 4 == 0}) =
    seq_four_to_seq_LE x
  in
  generic_injective_proof (seq_four_to_seq_LE_stronger) (seq_to_seq_four_LE #a) (seq_to_seq_four_to_seq_LE #a);
  ()

let seq_four_to_seq_LE_injective_specific (#a:eqtype) (x x':seq (four a)) :
  Lemma (seq_four_to_seq_LE x == seq_four_to_seq_LE x' ==> x == x')
  =
  seq_four_to_seq_LE_injective a

let four_to_seq_LE_injective (a:eqtype) :
  Lemma (forall (x x': four a) . four_to_seq_LE x == four_to_seq_LE x' ==> x == x')
  =
  generic_injective_proof #(four a) #(seq4 a) (four_to_seq_LE #a) (seq_to_four_LE #a) (seq_to_four_to_seq_LE #a)

let four_to_nat_8_injective () :
  Lemma (forall (x x':four (natN (pow2_norm 8))) . four_to_nat 8 x == four_to_nat 8 x' ==> x == x')
  =
  generic_injective_proof (four_to_nat 8) (nat_to_four 8) nat_to_four_to_nat

let nat_to_four_8_injective () :
  Lemma (forall (x x':natN (pow2_norm 32)) . nat_to_four 8 x == nat_to_four 8 x' ==> x == x')
  =
  generic_injective_proof (nat_to_four 8) (four_to_nat 8) four_to_nat_to_four_8

(*
let seq_to_four_LE_injective () :
  Lemma (forall (#a:Type) (x x':seq4 a) . seq_to_four_LE x == seq_to_four_LE x' ==> x == x')
  =
  generic_injective_proof seq_to_four_LE four_to_seq_LE four_to_seq_to_four_LE
*)

let append_distributes_seq_to_seq_four_LE (#a:Type) (x:seq a{length x % 4 == 0}) (y:seq a{length y % 4 == 0}) :
  Lemma (seq_to_seq_four_LE (x @| y) == seq_to_seq_four_LE x @| seq_to_seq_four_LE y)
  =
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #a);
  assert (equal (seq_to_seq_four_LE (x @| y)) (seq_to_seq_four_LE x @| seq_to_seq_four_LE y));
  ()

let append_distributes_seq_four_to_seq_LE #a x y =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #a);
  assert (equal (seq_four_to_seq_LE (x @| y)) (seq_four_to_seq_LE x @| seq_four_to_seq_LE y))
