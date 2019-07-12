module Arch.Types

open Types_s
open Collections.Seqs_s
open Collections.Seqs
open Words_s
open Words.Four_s
open Words.Seq_s
open Words.Seq
open FStar.Seq
open Words.Two_s

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2

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

val lemma_reverse_reverse_bytes_nat32_seq (s:seq nat32) :
  Lemma (ensures reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s) == s)
  [SMTPat (reverse_bytes_nat32_seq (reverse_bytes_nat32_seq s))]

unfold let quad32_to_seq (q:quad32) = four_to_seq_LE q

let lo64 (q:quad32) : nat64 = two_to_nat 32 (two_select (four_to_two_two q) 0)
let hi64 (q:quad32) : nat64 = two_to_nat 32 (two_select (four_to_two_two q) 1)

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

val le_bytes_to_seq_quad32_to_bytes_one_quad (b:quad32) :
  Lemma (le_bytes_to_seq_quad32 (le_quad32_to_bytes b) == create 1 b)

val le_bytes_to_seq_quad32_to_bytes (s:seq quad32) :
  Lemma (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes s) == s)

val le_quad32_to_bytes_to_quad32 (s:seq nat8 { length s == 16 }) :
  Lemma(le_quad32_to_bytes (le_bytes_to_quad32 s) == s)

val le_seq_quad32_to_bytes_of_singleton (q:quad32) :
  Lemma (le_quad32_to_bytes q == le_seq_quad32_to_bytes (create 1 q))

val le_quad32_to_bytes_injective: unit ->
  Lemma (forall b b' . le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b')

val le_quad32_to_bytes_injective_specific (b b':quad32) :
  Lemma (le_quad32_to_bytes b == le_quad32_to_bytes b' ==> b == b')

val seq_to_four_LE_is_seq_to_seq_four_LE (#a:Type) (s:seq4 a) : Lemma
  (create 1 (seq_to_four_LE s) == seq_to_seq_four_LE s)

val le_bytes_to_seq_quad_of_singleton (q:quad32) (b:seq nat8 { length b == 16 }) : Lemma
  (requires q == le_bytes_to_quad32 b)
  (ensures create 1 q == le_bytes_to_seq_quad32 b)

val le_bytes_to_quad32_to_bytes (q:quad32) :
  Lemma(le_bytes_to_quad32 (le_quad32_to_bytes q) == q)

let be_quad32_to_bytes (q:quad32) : seqn 16 nat8 =
  seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE q))

val be_bytes_to_quad32_to_bytes (q:quad32) :
  Lemma (be_bytes_to_quad32 (be_quad32_to_bytes q) == q)
  [SMTPat (be_bytes_to_quad32 (be_quad32_to_bytes q))]

open FStar.Mul
val slice_commutes_seq_four_to_seq_LE (#a:Type) (s:seq (four a)) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_four_to_seq_LE s) (n * 4) (n' * 4) ==
        seq_four_to_seq_LE (slice s n n'))

val slice_commutes_le_seq_quad32_to_bytes (s:seq quad32) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (le_seq_quad32_to_bytes s) (n * 16) (n' * 16) ==
        le_seq_quad32_to_bytes (slice s n n'))

val slice_commutes_le_seq_quad32_to_bytes0 (s:seq quad32) (n:nat{n <= length s}) :
  Lemma(slice (le_seq_quad32_to_bytes s) 0 (n * 16) ==
        le_seq_quad32_to_bytes (slice s 0 n))

val append_distributes_le_bytes_to_seq_quad32 (s1:seq nat8 { length s1 % 16 == 0 }) (s2:seq nat8 { length s2 % 16 == 0 }) :
  Lemma(le_bytes_to_seq_quad32 (s1 @| s2) == (le_bytes_to_seq_quad32 s1) @| (le_bytes_to_seq_quad32 s2))
