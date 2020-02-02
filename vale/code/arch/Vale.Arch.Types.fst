module Vale.Arch.Types

open FStar.Mul
open Vale.Def.Opaque_s
open Vale.Def.Types_s
open Vale.Arch.TypesNative
open Vale.Lib.Seqs
open Vale.Def.Words_s
open Vale.Def.Words.Two
open FStar.Calc

let lemma_nat_to_two32 () =
  assert_norm (forall (x:nat64).{:pattern (nat_to_two 32 x)}
    nat_to_two 32 x == Mktwo (x % 0x100000000) (x / 0x100000000))

let lemma_BitwiseXorCommutative x y =
  lemma_ixor_nth_all 32;
  lemma_equal_nth 32 (x *^ y) (y *^ x)

let lemma_BitwiseXorWithZero n =
  lemma_ixor_nth_all 32;
  lemma_zero_nth 32;
  lemma_equal_nth 32 (n *^ 0) n

let lemma_BitwiseXorCancel n =
  lemma_ixor_nth_all 32;
  lemma_zero_nth 32;
  lemma_equal_nth 32 (n *^ n) 0

let lemma_BitwiseXorCancel64 (n:nat64) =
  lemma_ixor_nth_all 64;
  lemma_zero_nth 64;
  lemma_equal_nth 64 (ixor n n) 0

let lemma_BitwiseXorAssociative x y z =
  lemma_ixor_nth_all 32;
  lemma_equal_nth 32 (x *^ (y *^ z)) ((x *^ y) *^ z)

let xor_lemmas () =
  FStar.Classical.forall_intro_2 lemma_BitwiseXorCommutative;
  FStar.Classical.forall_intro lemma_BitwiseXorWithZero;
  FStar.Classical.forall_intro lemma_BitwiseXorCancel;
  FStar.Classical.forall_intro lemma_BitwiseXorCancel64;
  FStar.Classical.forall_intro_3 lemma_BitwiseXorAssociative;
  ()

#push-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 3 --initial_ifuel 3"  // REVIEW: Why do we need this?
let lemma_quad32_xor () =
  quad32_xor_reveal ();
  reverse_bytes_nat32_reveal ();
  xor_lemmas()
  (*
  let helper (q:quad32) : Lemma (quad32_xor q q == Mkfour 0 0 0 0) =
    let q' = quad32_xor q q in
    quad32_xor_reveal ();
    reverse_bytes_nat32_reveal ();
    // REVIEW: Why are these necessary?
    assert (q'.lo0 == nat32_xor q.lo0 q.lo0);
    assert (q'.lo1 == nat32_xor q.lo1 q.lo1);
    assert (q'.hi2 == nat32_xor q.hi2 q.hi2);
    assert (q'.hi3 == nat32_xor q.hi3 q.hi3);
    xor_lemmas()
  in
  FStar.Classical.forall_intro helper
  *)
#pop-options

let lemma_reverse_reverse_bytes_nat32 (n:nat32) :
  Lemma (reverse_bytes_nat32 (reverse_bytes_nat32 n) == n)
  =
  reverse_bytes_nat32_reveal ();
  let r = reverse_seq (nat32_to_be_bytes n) in
  be_bytes_to_nat32_to_be_bytes r;
  ()

#push-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 3 --initial_ifuel 3"  // REVIEW: Why do we need this?
let lemma_reverse_bytes_quad32 (q:quad32) =
  quad32_xor_reveal ();
  reverse_bytes_nat32_reveal ();
  reveal_reverse_bytes_quad32 q;
  reveal_reverse_bytes_quad32 (reverse_bytes_quad32 q);
  ()
#pop-options

let lemma_reverse_bytes_nat32 (_:unit) : Lemma
  (reverse_bytes_nat32 0 == 0)
  =
  reverse_bytes_nat32_reveal ();
  assert_norm (nat_to_four 8 0 == Mkfour 0 0 0 0);
  ()

let lemma_reverse_bytes_quad32_zero (_:unit) : Lemma
  (let z = Mkfour 0 0 0 0 in
   reverse_bytes_quad32 z == z)
  =
  let z = Mkfour 0 0 0 0 in
  calc (==) {
    reverse_bytes_quad32 z;
    == { reveal_reverse_bytes_quad32 z }
    four_reverse (four_map reverse_bytes_nat32 z);
    == { lemma_reverse_bytes_nat32() }
    z;
  };
  ()

let lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (ensures reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  =
  reveal_reverse_bytes_nat32_seq s;
  reveal_reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s);
  assert (equal (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s)) s)

(*
let lemma_equality_check_helper_two_to_nat_32 (n:two nat32) :
  Lemma ( ((n.lo == 0 /\ n.hi == 0) ==> two_to_nat 32 n == 0) /\
          ( ~(n.lo == 0) \/ (~(n.hi == 0))) ==> ~(two_to_nat 32 n == 0) /\
          ((n.lo == 0xFFFFFFFF /\ n.hi == 0xFFFFFFFF) <==> two_to_nat 32 n == 0xFFFFFFFFFFFFFFFF))
  =
  if n.lo == 0 /\ n.hi == 0 then (
    assert (int_to_natN pow2_64 (n.lo + pow2_32 * n.hi) == 0);
    ()
  ) else (
    ()
  );
  ()

let lemma_equality_check_helper_lo (q:quad32) :
  Lemma ((q.lo0 == 0 /\ q.lo1 == 0 ==> lo64 q == 0) /\
         ((not (q.lo0 = 0) \/ not (q.lo1 = 0)) ==> not (lo64 q = 0)) /\
         (q.lo0 == 0xFFFFFFFF /\ q.lo1 == 0xFFFFFFFF <==> lo64 q == 0xFFFFFFFFFFFFFFFF))
  =
  assert (lo64 q == two_to_nat 32 (Mktwo q.lo0 q.lo1));
  lemma_equality_check_helper_two_to_nat_32 (Mktwo q.lo0 q.lo1);
  ()

let lemma_equality_check_helper_hi (q:quad32) :
  Lemma ((q.hi2 == 0 /\ q.hi3 == 0 ==> hi64 q == 0) /\
         ((~(q.hi2 = 0) \/ ~(q.hi3 = 0)) ==> ~(hi64 q = 0)) /\
         (q.hi2 == 0xFFFFFFFF /\ q.hi3 == 0xFFFFFFFF <==> hi64 q == 0xFFFFFFFFFFFFFFFF))
  =
  assert (hi64 q == two_to_nat 32 (Mktwo q.hi2 q.hi3));
  lemma_equality_check_helper_two_to_nat_32 (Mktwo q.hi2 q.hi3);
  ()
*)

let lemma_insert_nat64_properties (q:quad32) (n:nat64) :
  Lemma ( (let q' = insert_nat64 q n 0 in
            q'.hi2 == q.hi2 /\
            q'.hi3 == q.hi3) /\
           (let q' = insert_nat64 q n 1 in
            q'.lo0 == q.lo0 /\
            q'.lo1 == q.lo1))
  =
  insert_nat64_reveal ();
  ()

let lemma_insert_nat64_nat32s (q:quad32) (n0 n1:nat32) :
  Lemma ( insert_nat64 q (two_to_nat32 (Mktwo n0 n1)) 0 ==
          Mkfour n0 n1 q.hi2 q.hi3 /\
          insert_nat64 q (two_to_nat32 (Mktwo n0 n1)) 1 ==
          Mkfour q.lo0 q.lo1 n0 n1 )
  =
  let open Vale.Def.Words.Two in
  insert_nat64_reveal ();
  ()

let lemma_lo64_properties (_:unit) :
  Lemma (forall (q0 q1:quad32) . (q0.lo0 == q1.lo0 /\ q0.lo1 == q1.lo1) <==> (lo64 q0 == lo64 q1))
  =
  lo64_reveal ();
  let helper (q0 q1:quad32) : Lemma ((q0.lo0 == q1.lo0 /\ q0.lo1 == q1.lo1) <==> (lo64 q0 == lo64 q1)) =
    let Mktwo n1 n2 = two_select (four_to_two_two q0) 0 in
    nat_to_two_to_nat n1 n2;
    let Mktwo n1 n2 = two_select (four_to_two_two q1) 0 in
    nat_to_two_to_nat n1 n2;
    ()
  in
  FStar.Classical.forall_intro_2 helper;
  ()

let lemma_hi64_properties (_:unit) :
  Lemma (forall (q0 q1:quad32) . (q0.hi2 == q1.hi2 /\ q0.hi3 == q1.hi3) <==> (hi64 q0 == hi64 q1))
  =
  hi64_reveal ();
  let helper (q0 q1:quad32) : Lemma ((q0.hi2 == q1.hi2 /\ q0.hi3 == q1.hi3) <==> (hi64 q0 == hi64 q1)) =
    let Mktwo n1 n2 = two_select (four_to_two_two q0) 1 in
    nat_to_two_to_nat n1 n2;
    let Mktwo n1 n2 = two_select (four_to_two_two q1) 1 in
    nat_to_two_to_nat n1 n2;
    ()
  in
  FStar.Classical.forall_intro_2 helper;
  ()

let lemma_reverse_bytes_nat64_32 (n0 n1:nat32) : Lemma
  (reverse_bytes_nat64 (two_to_nat32 (Mktwo n0 n1)) == two_to_nat32 (Mktwo (reverse_bytes_nat32 n1) (reverse_bytes_nat32 n0)))
  =
  reverse_bytes_nat64_reveal ()

let lemma_reverse_bytes_quad32_64 (src orig final:quad32) : Lemma
  (requires final == insert_nat64 (insert_nat64 orig (reverse_bytes_nat64 (hi64 src)) 0) (reverse_bytes_nat64 (lo64 src)) 1)
  (ensures  final == reverse_bytes_quad32 src)
  =

  reverse_bytes_nat64_reveal ();
  let Mkfour x0 x1 x2 x3 = src in

  let two32 = (two_to_nat32 (Mktwo (reverse_bytes_nat32 x3) (reverse_bytes_nat32 x2))) in
  let two10 = (two_to_nat32 (Mktwo (reverse_bytes_nat32 x1) (reverse_bytes_nat32 x0))) in

  calc (==) {
       reverse_bytes_quad32 src;
       == { reveal_reverse_bytes_quad32 src }
       four_reverse (four_map reverse_bytes_nat32 src);
       == {}
       four_reverse (Mkfour (reverse_bytes_nat32 x0) (reverse_bytes_nat32 x1) (reverse_bytes_nat32 x2) (reverse_bytes_nat32 x3));
       == {}
       Mkfour (reverse_bytes_nat32 x3) (reverse_bytes_nat32 x2) (reverse_bytes_nat32 x1) (reverse_bytes_nat32 x0);
       == { lemma_insert_nat64_nat32s (Mkfour (reverse_bytes_nat32 x3) (reverse_bytes_nat32 x2) orig.hi2 orig.hi3)
                                      (reverse_bytes_nat32 x1) (reverse_bytes_nat32 x0) }
       insert_nat64 (Mkfour (reverse_bytes_nat32 x3) (reverse_bytes_nat32 x2) orig.hi2 orig.hi3) two10 1;
       == { lemma_insert_nat64_nat32s orig (reverse_bytes_nat32 x3) (reverse_bytes_nat32 x2) }
       insert_nat64 (insert_nat64 orig two32 0) two10 1;
  };

  calc (==) {
       reverse_bytes_nat64 (hi64 src);
       == { hi64_reveal ()}
       reverse_bytes_nat64 (two_to_nat 32 (two_select (four_to_two_two src) 1));
       == {}
       reverse_bytes_nat64 (two_to_nat 32 (Mktwo x2 x3));
       == { lemma_reverse_bytes_nat64_32 x2 x3 }
       two32;
  };
  calc (==) {
       reverse_bytes_nat64 (lo64 src);
       == { lo64_reveal () }
       reverse_bytes_nat64 (two_to_nat 32 (two_select (four_to_two_two src) 0));
       == {}
       reverse_bytes_nat64 (two_to_nat 32 (Mktwo x0 x1));
       == { lemma_reverse_bytes_nat64_32 x0 x1 }
       two10;
  };
  ()

let lemma_equality_check_helper (q:quad32) :
  Lemma ((q.lo0 == 0 /\ q.lo1 == 0 ==> lo64 q == 0) /\
         ((not (q.lo0 = 0) \/ not (q.lo1 = 0)) ==> not (lo64 q = 0)) /\
         (q.hi2 == 0 /\ q.hi3 == 0 ==> hi64 q == 0) /\
         ((~(q.hi2 = 0) \/ ~(q.hi3 = 0)) ==> ~(hi64 q = 0)) /\
         (q.lo0 == 0xFFFFFFFF /\ q.lo1 == 0xFFFFFFFF <==> lo64 q == 0xFFFFFFFFFFFFFFFF) /\
         (q.hi2 == 0xFFFFFFFF /\ q.hi3 == 0xFFFFFFFF <==> hi64 q == 0xFFFFFFFFFFFFFFFF)
         )
  =
//  lemma_equality_check_helper_lo q;
//  lemma_equality_check_helper_hi q;
  lo64_reveal ();
  hi64_reveal ();
  assert (forall (x:two nat32).{:pattern (two_to_nat 32 x)} two_to_nat 32 x == two_to_nat_unfold 32 x);
  ()


let push_pop_xmm (x y:quad32) : Lemma
  (let x' = insert_nat64 (insert_nat64 y (hi64 x) 1) (lo64 x) 0 in
   x == x')
   =
//   assert (nat_to_two 32 (hi64 x) == two_select (four_to_two_two x) 1);
  insert_nat64_reveal ();
  lo64_reveal ();
  hi64_reveal ();
  ()

#push-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 3 --initial_ifuel 3"  // REVIEW: Why do we need this?
let lemma_insrq_extrq_relations (x y:quad32) :
  Lemma (let z = insert_nat64 x (lo64 y) 0 in
         z == Mkfour y.lo0 y.lo1 x.hi2 x.hi3 /\
        (let z = insert_nat64 x (hi64 y) 1 in
         z == Mkfour x.lo0 x.lo1 y.hi2 y.hi3))
  =
  let open Vale.Def.Words.Two in
  let z = insert_nat64 x (lo64 y) 0 in
  insert_nat64_reveal ();
  lo64_reveal ();
  hi64_reveal ();
  assert (z == insert_nat64_def x (lo64_def y) 0);
  //assert (q'.hi2 == q.hi2);
  //assert (q'.hi3 == q.hi3);
  //assert (q' == two_two_to_four (two_insert (four_to_two_two q) (nat_to_two 32 (lo64 q)) 0));
  //assert (q' == two_two_to_four (two_insert (four_to_two_two q) (nat_to_two 32 (two_to_nat 32 (two_select (four_to_two_two q) 0))) 0));
  let Mktwo n1 n2 = two_select (four_to_two_two y) 0 in
  nat_to_two_to_nat n1 n2;
  let Mktwo n1 n2 = two_select (four_to_two_two y) 1 in
  nat_to_two_to_nat n1 n2;
  //assert (q' == two_two_to_four (two_insert (four_to_two_two q) (two_select (four_to_two_two q) 0) 0));
  //assert (q'.lo1 == q.lo1);
  //assert (q == q');
  ()

open Vale.Def.Words.Two

let le_bytes_to_nat64_to_bytes s =
  le_nat64_to_bytes_reveal ();
  le_bytes_to_nat64_reveal ()

let le_nat64_to_bytes_to_nat64 n =
  le_nat64_to_bytes_reveal ();
  le_bytes_to_nat64_reveal ()


let le_bytes_to_seq_quad32_empty () :
  Lemma (forall s . {:pattern (length (le_bytes_to_seq_quad32 s)) } length s == 0 ==> length (le_bytes_to_seq_quad32 s) == 0)
  =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  ()

#reset-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties'"
let le_bytes_to_seq_quad32_to_bytes_one_quad b =
  calc (==) {
    le_bytes_to_seq_quad32 (le_quad32_to_bytes b);
    == {reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32}
    seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE (le_quad32_to_bytes b));
    == {reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes}
    seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE (seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE b))));
    == {}
    seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE (seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE b)))));
    == {seq_to_seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE b))}
    seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_map (nat_to_four 8) (four_to_seq_LE b)));
    == {seq_map_inverses (nat_to_four 8) (four_to_nat 8) (four_to_seq_LE b)}
    seq_to_seq_four_LE (four_to_seq_LE b);
    == {four_to_seq_LE_is_seq_four_to_seq_LE b}
    seq_to_seq_four_LE (seq_four_to_seq_LE (create 1 b));
    == {}
    create 1 b;
  }

let le_bytes_to_seq_quad32_to_bytes (s:seq quad32) :
  Lemma (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes s) == s)
(* This expands into showing:
   le_bytes_to_seq_quad32 (le_quad32_to_bytes s)
 == { definition of le_bytes_to_seq_quad32 }
   seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE (le_seq_quad32_to_bytes s))
 == { definition of le_seq_quad32_to_bytes }
   seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE s)))
 == { definition of seq_nat8_to_seq_nat32_LE }
   seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE (seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE s))))
 == { definition of seq_nat32_to_seq_nat8_LE }
    seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE (seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)))))
 *)
  =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  le_seq_quad32_to_bytes_reveal ();
  seq_to_seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s));
  seq_map_inverses (nat_to_four 8) (four_to_nat 8) (seq_four_to_seq_LE s);
  seq_to_seq_four_to_seq_LE (s) ;
  ()

let le_seq_quad32_to_bytes_to_seq_quad32 s =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  le_seq_quad32_to_bytes_reveal ();
  calc (==) {
    le_seq_quad32_to_bytes (le_bytes_to_seq_quad32 s);
    (==) { }
    seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE (seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE s)));
    (==) { }
    s;
  }

(*
le_quad32_to_bytes (le_bytes_to_quad32 s)
== { definition of le_quad32_to_bytes }
seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE (le_bytes_to_quad32 s)))
== { definition of le_bytes_to_quad32 }
seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE (seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s)))))
*)

let le_quad32_to_bytes_to_quad32 s =
  calc (==) {
    le_quad32_to_bytes (le_bytes_to_quad32 s);
    == {le_bytes_to_quad32_reveal ()}
    le_quad32_to_bytes (seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s)));
    == {reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes}
    seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE (seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s)))));
    == {four_to_seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s))}
    seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_map (four_to_nat 8) (seq_to_seq_four_LE s)));
    == {seq_map_inverses (four_to_nat 8) (nat_to_four 8) (seq_to_seq_four_LE s)}
    seq_four_to_seq_LE (seq_to_seq_four_LE s);
    == {}
    s;
  }

let le_seq_quad32_to_bytes_of_singleton (q:quad32) :
  Lemma (le_quad32_to_bytes q == le_seq_quad32_to_bytes (create 1 q))
  =
  le_seq_quad32_to_bytes_reveal ();
  reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  four_to_seq_LE_is_seq_four_to_seq_LE q;
  ()

let le_quad32_to_bytes_injective ():
  Lemma (forall b b' . le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b')
  =
  reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  let helper (b b':quad32) : Lemma (le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b') =
    if le_quad32_to_bytes b = le_quad32_to_bytes b' then (
      let b1  = seq_map (nat_to_four 8) (four_to_seq_LE b) in
      let b1' = seq_map (nat_to_four 8) (four_to_seq_LE b') in
      assert (le_quad32_to_bytes b == seq_four_to_seq_LE b1);
      assert (le_quad32_to_bytes b' == seq_four_to_seq_LE b1');
      seq_four_to_seq_LE_injective_specific b1 b1';
      assert (b1 == b1');
      nat_to_four_8_injective();
      seq_map_injective (nat_to_four 8) (four_to_seq_LE b) (four_to_seq_LE b');
      assert ((four_to_seq_LE b) == (four_to_seq_LE b'));
      four_to_seq_LE_injective nat32;
      ()
    ) else
    ()
  in
  FStar.Classical.forall_intro_2 helper

let le_quad32_to_bytes_injective_specific (b b':quad32) :
  Lemma (le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b')
  =
  le_quad32_to_bytes_injective()

let le_seq_quad32_to_bytes_injective (b b':seq quad32) =
  le_seq_quad32_to_bytes_reveal ();
  seq_four_to_seq_LE_injective nat8;
  nat_to_four_8_injective();
  seq_map_injective (nat_to_four 8) (seq_four_to_seq_LE b) (seq_four_to_seq_LE b');
  seq_four_to_seq_LE_injective_specific b b';
  assert (equal b b')

let seq_to_four_LE_is_seq_to_seq_four_LE (#a:Type) (s:seq4 a) : Lemma
  (create 1 (seq_to_four_LE s) == seq_to_seq_four_LE s)
  =
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #a);
  assert (equal (create 1 (seq_to_four_LE s)) (seq_to_seq_four_LE s));
  ()

let le_bytes_to_seq_quad_of_singleton (q:quad32) (b:seq nat8 { length b == 16 }) : Lemma
  (requires q == le_bytes_to_quad32 b)
  (ensures create 1 q == le_bytes_to_seq_quad32 b)
  =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  le_bytes_to_quad32_reveal ();
  seq_to_four_LE_is_seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE b));
  // q == le_bytes_to_quad32 b
  //   == seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE b))
  //

  //     == seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE b))
  // le_bytes_to_seq_quad32 b == seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE b)
  ()

let le_bytes_to_quad32_to_bytes (q:quad32) :
  Lemma(le_bytes_to_quad32 (le_quad32_to_bytes q) == q)
  =
  le_seq_quad32_to_bytes_of_singleton q;  // ==> le_quad32_to_bytes q == le_seq_quad32_to_bytes (create 1 q)
  let b = le_quad32_to_bytes q in
  let q' = le_bytes_to_quad32 b in
  le_bytes_to_seq_quad_of_singleton q' b; // ==> create 1 q' == le_bytes_to_seq_quad32 b
                                          //                 == le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes (create 1 q))
  le_bytes_to_seq_quad32_to_bytes (create 1 q); //           == create 1 q
  //assert (create 1 q == create 1 q');
  //assert (equal (create 1 q) (create 1 q'));
  assert (q == index (create 1 q) 0);      // OBSERVE
  assert (q == q');
  ()

let be_bytes_to_quad32_to_bytes (q:quad32) :
  Lemma (be_bytes_to_quad32 (be_quad32_to_bytes q) == q)
  =
  be_bytes_to_quad32_reveal ();
  let q':quad32 = be_bytes_to_quad32 (be_quad32_to_bytes q) in
  seq_to_seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE q));
  seq_map_inverses (nat_to_four 8) (four_to_nat 8) (four_to_seq_BE q);
  seq_to_four_to_seq_BE q;
  ()

let lemma_reverse_reverse_bytes_nat32_quad32 (s:quad32) :
  Lemma (reverse_bytes_nat32_quad32 (reverse_bytes_nat32_quad32 s) == s)
  [SMTPat (reverse_bytes_nat32_quad32 (reverse_bytes_nat32_quad32 s))]
  =
  let s' = reverse_bytes_nat32_quad32 s in
  let s''= reverse_bytes_nat32_quad32 s' in
  assert (s''.lo0 == reverse_bytes_nat32 (reverse_bytes_nat32 s.lo0));  // OBSERVE
  assert (s''.lo1 == reverse_bytes_nat32 (reverse_bytes_nat32 s.lo1));  // OBSERVE
  assert (s''.hi2 == reverse_bytes_nat32 (reverse_bytes_nat32 s.hi2));  // OBSERVE
  assert (s''.hi3 == reverse_bytes_nat32 (reverse_bytes_nat32 s.hi3));  // OBSERVE
  ()

let lemma_reverse_reverse_bytes_nat32_quad32_seq (s:seq quad32) :
  Lemma (reverse_bytes_nat32_quad32_seq (reverse_bytes_nat32_quad32_seq s) == s)
  [SMTPat (reverse_bytes_nat32_quad32_seq (reverse_bytes_nat32_quad32_seq s))]
  =
  seq_map_inverses reverse_bytes_nat32_quad32 reverse_bytes_nat32_quad32 s

let lemma_reverse_reverse_bytes_quad32_seq (s:seq quad32) :
  Lemma (reverse_bytes_quad32_seq (reverse_bytes_quad32_seq s) == s)
  [SMTPat (reverse_bytes_quad32_seq (reverse_bytes_quad32_seq s))]
  =
  seq_map_inverses reverse_bytes_quad32 reverse_bytes_quad32 s

let lemma_le_seq_quad32_to_bytes_length (s:seq quad32) :
  Lemma(length (le_seq_quad32_to_bytes s) == (length s) * 16)
  =
  ()

let slice_commutes_seq_four_to_seq_LE (#a:Type) (s:seq (four a)) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_four_to_seq_LE s) (n * 4) (n' * 4) ==
        seq_four_to_seq_LE (slice s n n'))
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #a);
  assert (equal (slice (seq_four_to_seq_LE s) (n * 4) (n' * 4))
                (seq_four_to_seq_LE (slice s n n')));
  ()

let slice_commutes_le_seq_quad32_to_bytes (s:seq quad32) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (le_seq_quad32_to_bytes s) (n * 16) (n' * 16) ==
        le_seq_quad32_to_bytes (slice s n n'))
  =
  le_seq_quad32_to_bytes_reveal ();
  slice_commutes_seq_four_to_seq_LE s n n';
  assert (slice (seq_four_to_seq_LE s) (n * 4) (n' * 4) == seq_four_to_seq_LE (slice s n n'));
(*
  le_seq_quad32_to_bytes (slice s n n') == seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE (slice s n n')));
                                        == seq_four_to_seq_LE (seq_map (nat_to_four 8) (slice (seq_four_to_seq_LE s) (n * 4) (n' * 4))
  slice (le_seq_quad32_to_bytes s) (n * 16) (n' * 16)
  ==  slice (seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s))) (n * 16) (n' * 16)
  ==  seq_four_to_seq_LE (slice (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)) (n * 4) (n' * 4))
*)
  slice_seq_map_commute (nat_to_four 8) (seq_four_to_seq_LE s) (n*4) (n'*4);

  let s_inner = (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)) in
  slice_commutes_seq_four_to_seq_LE s_inner (n * 4) (n' * 4);
  ()

let slice_commutes_le_seq_quad32_to_bytes0 (s:seq quad32) (n:nat{n <= length s}) :
  Lemma(slice (le_seq_quad32_to_bytes s) 0 (n * 16) ==
        le_seq_quad32_to_bytes (slice s 0 n))
  =
  slice_commutes_le_seq_quad32_to_bytes s 0 n

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties'"
let append_distributes_le_bytes_to_seq_quad32 (s1:seq nat8 { length s1 % 16 == 0 }) (s2:seq nat8 { length s2 % 16 == 0 }) :
  Lemma(le_bytes_to_seq_quad32 (s1 @| s2) == (le_bytes_to_seq_quad32 s1) @| (le_bytes_to_seq_quad32 s2))
  =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  let s1' = seq_nat8_to_seq_nat32_LE s1 in
  let s2' = seq_nat8_to_seq_nat32_LE s2 in
  // (le_bytes_to_seq_quad32 s1) @| (le_bytes_to_seq_quad32 s2))
  // =  { Definition of le_bytes_to_seq_quad32 }
  // seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE s1) @| seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE s2)
  append_distributes_seq_to_seq_four_LE s1' s2';
  // =
  // seq_to_seq_four_LE ((seq_nat8_to_seq_nat32_LE s1) @| (seq_nat8_to_seq_nat32_LE s2))
  append_distributes_seq_map (four_to_nat 8) (seq_to_seq_four_LE s1) (seq_to_seq_four_LE s2);
  // seq_to_seq_four_LE (seq_map (four_to_nat 8) ((seq_to_seq_four_LE s1) @| (seq_to_seq_four_LE s2)))
  append_distributes_seq_to_seq_four_LE s1 s2;
  // seq_to_seq_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE (s1 @| s2)))
  // le_bytes_to_seq_quad32 (s1 @| s2)
  ()

let append_distributes_le_seq_quad32_to_bytes s1 s2 =
  le_seq_quad32_to_bytes_reveal ();
  calc (==) {
    le_seq_quad32_to_bytes (s1 @| s2);
    (==) { }
    seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE (s1 @| s2));
    (==) { append_distributes_seq_four_to_seq_LE s1 s2 }
    seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE s1 @| seq_four_to_seq_LE s2);
    (==) { append_distributes_seq_map (nat_to_four 8) (seq_four_to_seq_LE s1) (seq_four_to_seq_LE s2) }
    seq_four_to_seq_LE (
      seq_map (nat_to_four 8) (seq_four_to_seq_LE s1) @|
      seq_map (nat_to_four 8) (seq_four_to_seq_LE s2));
    (==) { append_distributes_seq_four_to_seq_LE
         (seq_map (nat_to_four 8) (seq_four_to_seq_LE s1))
         (seq_map (nat_to_four 8) (seq_four_to_seq_LE s2)) }
      seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s1)) @|
      seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s2));
    (==) { }
    le_seq_quad32_to_bytes s1 @| le_seq_quad32_to_bytes s2;
  }
