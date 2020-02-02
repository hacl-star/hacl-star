module Vale.Arch.Types

open FStar.Mul
open Vale.Def.Opaque_s
open Vale.Def.Types_s
open Vale.Lib.Seqs_s
open Vale.Lib.Seqs
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Seq
open FStar.Seq
open Vale.Def.Words.Two_s

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

unfold let add_wrap32 (x:nat32) (y:nat32) : nat32 = add_wrap x y
unfold let add_wrap64 (x:nat64) (y:nat64) : nat64 = add_wrap x y
unfold let sub_wrap32 (x:nat32) (y:nat32) : nat32 = sub_wrap x y
unfold let sub_wrap64 (x:nat64) (y:nat64) : nat64 = sub_wrap x y

unfold let iand32 (a:nat32) (b:nat32) : nat32 = iand a b
unfold let ixor32 (a:nat32) (b:nat32) : nat32 = ixor a b
unfold let ior32 (a:nat32) (b:nat32) : nat32 = ior a b
unfold let inot32 (a:nat32) : nat32 = inot a
unfold let ishl32 (a:nat32) (s:int) : nat32 = ishl a s
unfold let ishr32 (a:nat32) (s:int) : nat32 = ishr a s

unfold let iand64 (a:nat64) (b:nat64) : nat64 = iand a b
unfold let ixor64 (a:nat64) (b:nat64) : nat64 = ixor a b
unfold let ior64 (a:nat64) (b:nat64) : nat64 = ior a b
unfold let inot64 (a:nat64) : nat64 = inot a
unfold let ishl64 (a:nat64) (s:int) : nat64 = ishl a s
unfold let ishr64 (a:nat64) (s:int) : nat64 = ishr a s

unfold let iand128 (a:nat128) (b:nat128) : nat128 = iand a b
unfold let ixor128 (a:nat128) (b:nat128) : nat128 = ixor a b
unfold let ior128 (a:nat128) (b:nat128) : nat128 = ior a b
unfold let inot128 (a:nat128) : nat128 = inot a
unfold let ishl128 (a:nat128) (s:int) : nat128 = ishl a s
unfold let ishr128 (a:nat128) (s:int) : nat128 = ishr a s

unfold let two_to_nat32 (x:two nat32) : nat64 = two_to_nat 32 x

val lemma_nat_to_two32 (_:unit) : Lemma
  (forall (x:nat64).{:pattern (nat_to_two 32 x)}
    nat_to_two 32 x == Mktwo (x % 0x100000000) (x / 0x100000000))

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2

let add_wrap_quad32 (q0 q1:quad32) : quad32 =
  let open Vale.Def.Words_s in
  Mkfour (add_wrap q0.lo0 q1.lo0)
         (add_wrap q0.lo1 q1.lo1)
         (add_wrap q0.hi2 q1.hi2)
         (add_wrap q0.hi3 q1.hi3)

val lemma_BitwiseXorCommutative (x y:nat32) : Lemma (x *^ y == y *^ x)
val lemma_BitwiseXorWithZero (n:nat32) : Lemma (n *^ 0 == n)
val lemma_BitwiseXorCancel (n:nat32) : Lemma (n *^ n == 0)
val lemma_BitwiseXorCancel64 (n:nat64) : Lemma (ixor n n == 0)
val lemma_BitwiseXorAssociative (x y z:nat32) : Lemma (x *^ (y *^ z) == (x *^ y) *^ z)

val xor_lemmas (_:unit) : Lemma
  (ensures
    (forall (x y:nat32).{:pattern (x *^ y)} x *^ y == y *^ x) /\
    (forall (n:nat32).{:pattern (n *^ 0)} n *^ 0 == n) /\
    (forall (n:nat32).{:pattern (n *^ n)} n *^ n == 0) /\
    (forall (n:nat64).{:pattern (ixor n n)} ixor n n == 0) /\
    (forall (x y z:nat32).{:pattern (x *^ (y *^ z))} x *^ (y *^ z) == (x *^ y) *^ z)
  )

val lemma_quad32_xor (_:unit) : Lemma (forall q . {:pattern quad32_xor q q} quad32_xor q q == Mkfour 0 0 0 0)

let quad32_double_lo (q:quad32) : double32 = (four_to_two_two q).lo
let quad32_double_hi (q:quad32) : double32 = (four_to_two_two q).hi

val lemma_reverse_reverse_bytes_nat32 (n:nat32) :
  Lemma (reverse_bytes_nat32 (reverse_bytes_nat32 n) == n)
  [SMTPat (reverse_bytes_nat32 (reverse_bytes_nat32 n))]

val lemma_reverse_bytes_quad32 (q:quad32) :
  Lemma (reverse_bytes_quad32 (reverse_bytes_quad32 q) == q)
  [SMTPat (reverse_bytes_quad32 (reverse_bytes_quad32 q))]

val lemma_reverse_bytes_quad32_zero (_:unit) : Lemma
  (let z = Mkfour 0 0 0 0 in
   reverse_bytes_quad32 z == z)

val lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  [SMTPat (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s))]

unfold let quad32_to_seq (q:quad32) : seq nat32 = four_to_seq_LE q

val lemma_insert_nat64_properties (q:quad32) (n:nat64) :
  Lemma ( (let q' = insert_nat64 q n 0 in
            q'.hi2 == q.hi2 /\
            q'.hi3 == q.hi3) /\
           (let q' = insert_nat64 q n 1 in
            q'.lo0 == q.lo0 /\
            q'.lo1 == q.lo1))
  [SMTPat (insert_nat64 q n)]

val lemma_insert_nat64_nat32s (q:quad32) (n0 n1:nat32) :
  Lemma ( insert_nat64 q (two_to_nat32 (Mktwo n0 n1)) 0 ==
          Mkfour n0 n1 q.hi2 q.hi3 /\
          insert_nat64 q (two_to_nat32 (Mktwo n0 n1)) 1 ==
          Mkfour q.lo0 q.lo1 n0 n1 )

let lo64_def (q:quad32) : nat64 = two_to_nat 32 (two_select (four_to_two_two q) 0)
[@"opaque_to_smt"] let lo64 = opaque_make lo64_def
irreducible let lo64_reveal = opaque_revealer (`%lo64) lo64 lo64_def

let hi64_def (q:quad32) : nat64 = two_to_nat 32 (two_select (four_to_two_two q) 1)
[@"opaque_to_smt"] let hi64 = opaque_make hi64_def
irreducible let hi64_reveal = opaque_revealer (`%hi64) hi64 hi64_def

val lemma_lo64_properties (_:unit) : Lemma
  (forall (q0 q1:quad32).{:pattern lo64 q0; lo64 q1}
    (q0.lo0 == q1.lo0 /\ q0.lo1 == q1.lo1) <==> (lo64 q0 == lo64 q1))

val lemma_hi64_properties (_:unit) : Lemma
  (forall (q0 q1:quad32).{:pattern hi64 q0; hi64 q1}
    (q0.hi2 == q1.hi2 /\ q0.hi3 == q1.hi3) <==> (hi64 q0 == hi64 q1))

val lemma_reverse_bytes_quad32_64 (src orig final:quad32) : Lemma
  (requires final == insert_nat64 (insert_nat64 orig (reverse_bytes_nat64 (hi64 src)) 0) (reverse_bytes_nat64 (lo64 src)) 1)
  (ensures  final == reverse_bytes_quad32 src)

val lemma_equality_check_helper (q:quad32) :
  Lemma ((q.lo0 == 0 /\ q.lo1 == 0 ==> lo64 q == 0) /\
         ((not (q.lo0 = 0) \/ not (q.lo1 = 0)) ==> not (lo64 q = 0)) /\
         (q.hi2 == 0 /\ q.hi3 == 0 ==> hi64 q == 0) /\
         ((~(q.hi2 = 0) \/ ~(q.hi3 = 0)) ==> ~(hi64 q = 0)) /\
         (q.lo0 == 0xFFFFFFFF /\ q.lo1 == 0xFFFFFFFF <==> lo64 q == 0xFFFFFFFFFFFFFFFF) /\
         (q.hi2 == 0xFFFFFFFF /\ q.hi3 == 0xFFFFFFFF <==> hi64 q == 0xFFFFFFFFFFFFFFFF)
         )

let lemma_equality_check_helper_2 (q1 q2 cmp:quad32) (tmp1 result1 tmp2 tmp3 result2:nat64) : Lemma
  (requires cmp == Mkfour (if q1.lo0 = q2.lo0 then 0xFFFFFFFF else 0)
                          (if q1.lo1 = q2.lo1 then 0xFFFFFFFF else 0)
                          (if q1.hi2 = q2.hi2 then 0xFFFFFFFF else 0)
                          (if q1.hi3 = q2.hi3 then 0xFFFFFFFF else 0) /\
            tmp1 = lo64 cmp /\
            result1 = (if tmp1 = 0xFFFFFFFFFFFFFFFF then 0 else 1) /\
            tmp2 = hi64 cmp /\
            tmp3 = (if tmp2 = 0xFFFFFFFFFFFFFFFF then 0 else 1) /\
            result2 = tmp3 + result1)
  (ensures (if q1 = q2 then result2 = 0 else result2 > 0))
  =
  lemma_equality_check_helper cmp;
  ()

val push_pop_xmm (x y:quad32) : Lemma
  (let x' = insert_nat64 (insert_nat64 y (hi64 x) 1) (lo64 x) 0 in
   x == x')

val lemma_insrq_extrq_relations (x y:quad32) :
  Lemma (let z = insert_nat64 x (lo64 y) 0 in
         z == Mkfour y.lo0 y.lo1 x.hi2 x.hi3 /\
        (let z = insert_nat64 x (hi64 y) 1 in
         z == Mkfour x.lo0 x.lo1 y.hi2 y.hi3))

val le_bytes_to_nat64_to_bytes (s:nat64) :
  Lemma (le_bytes_to_nat64 (le_nat64_to_bytes s) == s)

val le_nat64_to_bytes_to_nat64 (s:seq nat8 { length s == 8 }) :
  Lemma (le_nat64_to_bytes (le_bytes_to_nat64 s) == s)

val le_bytes_to_seq_quad32_empty: unit ->
  Lemma (forall s . {:pattern (length (le_bytes_to_seq_quad32 s)) } length s == 0 ==> length (le_bytes_to_seq_quad32 s) == 0)

val le_bytes_to_seq_quad32_to_bytes_one_quad (b:quad32) :
  Lemma (le_bytes_to_seq_quad32 (le_quad32_to_bytes b) == create 1 b)

val le_bytes_to_seq_quad32_to_bytes (s:seq quad32) :
  Lemma (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes s) == s)

val le_seq_quad32_to_bytes_to_seq_quad32 (s:seq nat8{length s % 16 = 0}) :
  Lemma (le_seq_quad32_to_bytes (le_bytes_to_seq_quad32 s) == s)

val le_quad32_to_bytes_to_quad32 (s:seq nat8 { length s == 16 }) :
  Lemma(le_quad32_to_bytes (le_bytes_to_quad32 s) == s)

val le_seq_quad32_to_bytes_of_singleton (q:quad32) :
  Lemma (le_quad32_to_bytes q == le_seq_quad32_to_bytes (create 1 q))

val le_quad32_to_bytes_injective: unit ->
  Lemma (forall b b' . le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b')

val le_quad32_to_bytes_injective_specific (b b':quad32) :
  Lemma (le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b')

val le_seq_quad32_to_bytes_injective (b b':Seq.seq quad32) : Lemma
  (requires Seq.equal (le_seq_quad32_to_bytes b) (le_seq_quad32_to_bytes b'))
  (ensures b == b')

val seq_to_four_LE_is_seq_to_seq_four_LE (#a:Type) (s:seq4 a) : Lemma
  (create 1 (seq_to_four_LE s) == seq_to_seq_four_LE s)

val le_bytes_to_seq_quad_of_singleton (q:quad32) (b:seq nat8 { length b == 16 }) : Lemma
  (requires q == le_bytes_to_quad32 b)
  (ensures create 1 q == le_bytes_to_seq_quad32 b)

val le_bytes_to_quad32_to_bytes (q:quad32) :
  Lemma(le_bytes_to_quad32 (le_quad32_to_bytes q) == q)

let be_quad32_to_bytes (q:quad32) : seq16 nat8 =
  seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE q))

val be_bytes_to_quad32_to_bytes (q:quad32) :
  Lemma (be_bytes_to_quad32 (be_quad32_to_bytes q) == q)
  [SMTPat (be_bytes_to_quad32 (be_quad32_to_bytes q))]

// Reverse each nat32 in the quad, but leave the nat32s in their original order
let reverse_bytes_nat32_quad32 (q:quad32) : quad32 =
  Vale.Def.Words.Four_s.four_map reverse_bytes_nat32 q

val lemma_reverse_reverse_bytes_nat32_quad32 (s:quad32) :
  Lemma (reverse_bytes_nat32_quad32 (reverse_bytes_nat32_quad32 s) == s)
  [SMTPat (reverse_bytes_nat32_quad32 (reverse_bytes_nat32_quad32 s))]

let reverse_bytes_nat32_quad32_seq (q:seq quad32) : seq quad32 =
  seq_map reverse_bytes_nat32_quad32 q

val lemma_reverse_reverse_bytes_nat32_quad32_seq (s:seq quad32) :
  Lemma (reverse_bytes_nat32_quad32_seq (reverse_bytes_nat32_quad32_seq s) == s)
  [SMTPat (reverse_bytes_nat32_quad32_seq (reverse_bytes_nat32_quad32_seq s))]

let reverse_bytes_quad32_seq (s:seq quad32) : seq quad32 =
  seq_map reverse_bytes_quad32 s

val lemma_reverse_reverse_bytes_quad32_seq (s:seq quad32) :
  Lemma (reverse_bytes_quad32_seq (reverse_bytes_quad32_seq s) == s)
  [SMTPat (reverse_bytes_quad32_seq (reverse_bytes_quad32_seq s))]

val lemma_le_seq_quad32_to_bytes_length (s:seq quad32) :
  Lemma(length (le_seq_quad32_to_bytes s) == (length s) * 16)


val slice_commutes_seq_four_to_seq_LE (#a:Type) (s:seq (four a)) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_four_to_seq_LE s) (n * 4) (n' * 4) ==
        seq_four_to_seq_LE (slice s n n'))

val slice_commutes_le_seq_quad32_to_bytes (s:seq quad32) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (le_seq_quad32_to_bytes s) (n * 16) (n' * 16) ==
        le_seq_quad32_to_bytes (slice s n n'))

val slice_commutes_le_seq_quad32_to_bytes0 (s:seq quad32) (n:nat{n <= length s}) :
  Lemma(slice (le_seq_quad32_to_bytes s) 0 (n * 16) ==
        le_seq_quad32_to_bytes (slice s 0 n))

(*
val slice_commutes_le_bytes_to_seq_quad32 (s:seq nat8 { length s % 16 == 0 }) (n:nat{n * 16 <= length s}) :
  Lemma(length (le_bytes_to_seq_quad32 s) == length s / 16 /\
        slice (le_bytes_to_seq_quad32 s) 0 n ==
        le_bytes_to_seq_quad32 (slice s 0 (n*16)))
*)

val append_distributes_le_bytes_to_seq_quad32 (s1:seq nat8 { length s1 % 16 == 0 }) (s2:seq nat8 { length s2 % 16 == 0 }) :
  Lemma(le_bytes_to_seq_quad32 (s1 @| s2) == (le_bytes_to_seq_quad32 s1) @| (le_bytes_to_seq_quad32 s2))

val append_distributes_le_seq_quad32_to_bytes (s1:seq quad32) (s2:seq quad32) :
  Lemma(le_seq_quad32_to_bytes (s1 @| s2) == (le_seq_quad32_to_bytes s1) @| (le_seq_quad32_to_bytes s2))
