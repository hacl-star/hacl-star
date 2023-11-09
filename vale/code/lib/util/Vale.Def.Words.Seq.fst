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

let seq_four_to_seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) :
  Lemma (seq_four_to_seq_BE (seq_to_seq_four_BE x) == x)
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #a);
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #a);
  assert (equal (seq_four_to_seq_BE (seq_to_seq_four_BE x)) x);
  ()

unfold let pow2_24 = 16777216 //normalize_term (pow2 24)

#push-options "--z3rlimit 200 --using_facts_from 'Prims Vale.Def.Words_s'"
let lemma_fundamental_div_mod_4 (x:nat32) :
  Lemma (x = x % pow2_8 + pow2_8 * ((x / pow2_8) % pow2_8) + pow2_16 * ((x / pow2_16) % pow2_8) + pow2_24 * ((x / pow2_24) % pow2_8))
  =
  ()
#pop-options

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

let rec base_to_nat (base:pos) (cs : list (natN base)) : nat =
  match cs with
  | [] -> 0
  | c :: cs' -> c + base_to_nat base cs' * base
  (* NB: right-multiplying by base is a lot better than left-multiplying
  since it more closely matches the lemmas in FStar.Math.Lemmas. *)

(* If two lists represent the same number, their heads must match,
otherwise their modulus wrt the base would differ. *)
let base_to_nat_inj_head (base:pos) (x y : list (natN base)) :
  Lemma (requires base_to_nat base x == base_to_nat base y /\ Cons? x /\ Cons? y)
        (ensures List.Tot.hd x == List.Tot.hd y)
  =
  match x, y with
  | x1 :: xs, y1 :: ys ->
    let x' = base_to_nat base x in
    let y' = base_to_nat base y in
    let open FStar.Math.Lemmas in
    calc (==) {
      x1 <: int;
      == { small_mod x1 base }
      x1 % base;
      == { lemma_mod_plus x1 (base_to_nat base xs) base }
      (x1 + base_to_nat base xs * base) % base;
      == {}
      x' % base;
      == {}
      y' % base;
      == {}
      (y1 + base_to_nat base ys * base) % base;
      == { lemma_mod_plus y1 (base_to_nat base ys) base }
      y1 % base;
      == { small_mod y1 base }
      y1;
    }

(* Generalizing the lemma above, if two lists represent the same number,
and they have the same length, they must be the same list. The length requirement
is due to the possibility of trailing zeroes. Another possibility is stating
that one of them is a prefix of the other, which is enough for this module,
even without stating that the "rest" is all zeroes. *)
let rec base_to_nat_inj (base:pos) (x y : list (natN base)) :
  Lemma (requires base_to_nat base x == base_to_nat base y /\ List.length x == List.length y)
        (ensures x == y)
  =
  match x, y with
  | [], [] -> ()
  | x1 :: xs, y1 :: ys ->
    base_to_nat_inj_head base x y;
    let x' = base_to_nat base x in
    let y' = base_to_nat base y in
    let open FStar.Math.Lemmas in
    calc (==) {
      base_to_nat base xs * base;
      == {}
      x' - x1;
      == {}
      y' - y1;
      == {}
      base_to_nat base ys * base;
    };
    lemma_cancel_mul (base_to_nat base xs) (base_to_nat base ys) base;
    assert (base_to_nat base xs == base_to_nat base ys);
    base_to_nat_inj base xs ys

let four_to_nat_inj (x y : four (natN 256)) :
  Lemma (requires four_to_nat 8 x == four_to_nat 8 y)
        (ensures x == y)
  =
  let Mkfour x0 x1 x2 x3 = x in
  let Mkfour y0 y1 y2 y3 = y in
  assert_norm (four_to_nat 8 x == base_to_nat 256 [x0; x1; x2; x3]);
  assert_norm (four_to_nat 8 y == base_to_nat 256 [y0; y1; y2; y3]);
  base_to_nat_inj 256 [x0; x1; x2; x3] [y0; y1; y2; y3];
  ()

let nat_to_four_to_nat (x:four (natN 256)) :
  Lemma (nat_to_four 8 (four_to_nat 8 x) == x)
  [SMTPat (nat_to_four 8 (four_to_nat 8 x))]
  =
  four_to_nat_to_four_8 (four_to_nat 8 x);
  four_to_nat_inj (nat_to_four 8 (four_to_nat 8 x)) x

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

let four_to_seq_BE_is_seq_four_to_seq_BE (x:four nat32) :
  Lemma (four_to_seq_BE x == seq_four_to_seq_BE (create 1 x))
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat32);
  let s0 = four_to_seq_BE x  in
  let s1 = seq_four_to_seq_BE (create 1 x) in
  assert (equal s0 s1);
  ()

let seq_nat8_to_seq_nat32_to_seq_nat8_LE (x:seq nat32) :
  Lemma (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE x) == x)
  =
  assert (equal (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE x)) x);
  ()

let seq_nat8_to_seq_nat32_to_seq_nat8_BE (x:seq nat32) :
  Lemma (seq_nat8_to_seq_nat32_BE (seq_nat32_to_seq_nat8_BE x) == x)
  =
  assert (equal (seq_nat8_to_seq_nat32_BE (seq_nat32_to_seq_nat8_BE x)) x);
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

let seq_four_to_seq_BE_injective (a:eqtype) :
  Lemma (forall (x x': seq (four a)). seq_four_to_seq_BE #a x == seq_four_to_seq_BE #a x' ==> x == x')
  =
  let seq_four_to_seq_BE_stronger (#b:Type) (x:seq (four b)) : (s:seq b{length s % 4 == 0}) =
    seq_four_to_seq_BE x
  in
  generic_injective_proof (seq_four_to_seq_BE_stronger) (seq_to_seq_four_BE #a) (seq_to_seq_four_to_seq_BE #a);
  ()

let seq_four_to_seq_LE_injective_specific (#a:eqtype) (x x':seq (four a)) :
  Lemma (seq_four_to_seq_LE x == seq_four_to_seq_LE x' ==> x == x')
  =
  seq_four_to_seq_LE_injective a

let seq_four_to_seq_BE_injective_specific (#a:eqtype) (x x':seq (four a)) :
  Lemma (seq_four_to_seq_BE x == seq_four_to_seq_BE x' ==> x == x')
  =
  seq_four_to_seq_BE_injective a

let four_to_seq_LE_injective (a:eqtype) :
  Lemma (forall (x x': four a) . four_to_seq_LE x == four_to_seq_LE x' ==> x == x')
  =
  generic_injective_proof #(four a) #(seq4 a) (four_to_seq_LE #a) (seq_to_four_LE #a) (seq_to_four_to_seq_LE #a)

let four_to_seq_BE_injective (a:eqtype) :
  Lemma (forall (x x': four a) . four_to_seq_BE x == four_to_seq_BE x' ==> x == x')
  =
  generic_injective_proof #(four a) #(seq4 a) (four_to_seq_BE #a) (seq_to_four_BE #a) (seq_to_four_to_seq_BE #a)

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

let append_distributes_seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) (y:seq a{length y % 4 == 0}) :
  Lemma (seq_to_seq_four_BE (x @| y) == seq_to_seq_four_BE x @| seq_to_seq_four_BE y)
  =
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #a);
  assert (equal (seq_to_seq_four_BE (x @| y)) (seq_to_seq_four_BE x @| seq_to_seq_four_BE y));
  ()

let append_distributes_seq_four_to_seq_LE #a x y =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #a);
  assert (equal (seq_four_to_seq_LE (x @| y)) (seq_four_to_seq_LE x @| seq_four_to_seq_LE y))

let append_distributes_seq_four_to_seq_BE #a x y =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #a);
  assert (equal (seq_four_to_seq_BE (x @| y)) (seq_four_to_seq_BE x @| seq_four_to_seq_BE y))
