module Vale.Bignum.Defs

open FStar.Mul
open FStar.Seq
open Vale.Def.Words_s
unfold let (.[]) = Seq.index

val lemma_mul_nat_bound (a a' b b':nat) : Lemma
  (requires a <= a' /\ b <= b')
  (ensures 0 <= a * b /\ a * b <= a' * b')

val lemma_mul_n_bound (#n:nat) (a b:natN n) : Lemma (0 <= a * b /\ a * b <= (n - 1) * (n - 1))
val lemma_mul_div_n_lt (#n:nat) (a b:natN n) : Lemma ((a * b) / n < (if n <= 1 then n else n - 1))
val lemma_mul_div_n (#n:pos) (a b:natN n) : Lemma (0 <= (a * b) / n /\ (a * b) / n < n)

let add_lo_def (#n:nat) (a b:natN n) (c:nat1) : natN n =
  let x = a + b + c in
  if x < n then x else x - n

val add_lo (#n:nat) (a b:natN n) (c:nat1) : natN n
val reveal_add_lo (#n:nat) (a b:natN n) (c:nat1) : Lemma (add_lo a b c == add_lo_def a b c)
val reveal_add_lo_all (_:unit) : Lemma
  (forall (n:nat) (a b:natN n) (c:nat1).{:pattern add_lo a b c} add_lo a b c == add_lo_def a b c)

let add_hi_def (#n:nat) (a b:natN n) (c:nat1) : nat1 =
  if a + b + c < n then 0 else 1

val add_hi (#n:nat) (a b:natN n) (c:nat1) : nat1
val reveal_add_hi (#n:nat) (a b:natN n) (c:nat1) : Lemma (add_hi a b c == add_hi_def a b c)
val reveal_add_hi_all (_:unit) : Lemma
  (forall (n:nat) (a b:natN n) (c:nat1).{:pattern add_hi a b c} add_hi a b c == add_hi_def a b c)

let mul_lo_def (#n:pos) (a b:natN n) : natN n =
  (a * b) % n

val mul_lo (#n:pos) (a b:natN n) : natN n
val reveal_mul_lo (#n:nat) (a b:natN n) : Lemma (mul_lo a b == mul_lo_def a b)
val reveal_mul_lo_all (_:unit) : Lemma
  (forall (n:nat) (a b:natN n).{:pattern mul_lo a b} mul_lo a b == mul_lo_def a b)

let mul_hi_def (#n:pos) (a b:natN n) : natN n =
  lemma_mul_div_n a b;
  (a * b) / n

val mul_hi (#n:pos) (a b:natN n) : natN n
val reveal_mul_hi (#n:nat) (a b:natN n) : Lemma (mul_hi a b == mul_hi_def a b)
val reveal_mul_hi_all (_:unit) : Lemma
  (forall (n:nat) (a b:natN n).{:pattern mul_hi a b} mul_hi a b == mul_hi_def a b)

let rec sum_seq_left (s:seq int) (i j:nat) : Pure int
  (requires i <= j /\ j <= length s)
  (ensures fun _ -> True)
  (decreases j)
  =
  if i = j then 0
  else s.[j - 1] + sum_seq_left s i (j - 1)

let rec sum_seq_right (s:seq int) (i j:nat) : Pure int
  (requires i <= j /\ j <= length s)
  (ensures fun _ -> True)
  (decreases (j - i))
  =
  if i = j then 0
  else s.[i] + sum_seq_right s (i + 1) j

let rec pow_int (a:int) (b:nat) : int =
  if b = 0 then 1
  else a * pow_int a (b - 1)

let pow_seq (#n:nat) (s:seq (natN n)) : seq int =
  init (length s) (fun (i:nat{i < length s}) -> s.[i] * pow_int n i)

let sum_pow_seq_left (#n:nat) (s:seq (natN n)) (i:nat{i <= length s}) : int =
  sum_seq_left (pow_seq s) 0 i

let sum_pow_seq (#n:nat) (s:seq (natN n)) : int =
  sum_pow_seq_left s (length s)

