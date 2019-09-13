module Vale.Bignum.Lemmas

open FStar.Mul
open FStar.Seq
open Vale.Def.Words_s
open Vale.Bignum.Defs
unfold let (.[]) = Seq.index

let rec seq_add_c (#n:nat) (as bs:seq (natN n)) (c0:nat1) (i:nat) : Pure nat1
  (requires length as == length bs /\ i <= length as)
  (ensures fun _ -> True)
  =
  if i = 0 then c0 else add_hi as.[i - 1] bs.[i - 1] (seq_add_c as bs c0 (i - 1))

let seq_add_i (#n:nat) (as bs:seq (natN n)) (c0:nat1) (i:nat) : Pure (natN n)
  (requires length as == length bs /\ i < length as)
  (ensures fun _ -> True)
  =
  add_lo as.[i] bs.[i] (seq_add_c as bs c0 i)

// as + bs
let seq_add (#n:nat) (as bs:seq (natN n)) (c0:nat1) : Pure (seq (natN n) & nat1)
  (requires length as == length bs)
  (ensures fun (xs, _) -> length xs == length as)
  =
  let f (i:nat{i < length as}) = seq_add_i as bs c0 i in
  (init (length as) f, seq_add_c as bs c0 (length as))

let last_carry (a b:nat) (c:nat1) : int =
  if c = 0 then 0 else pow_int a b

let seq_scale_lo (#n:pos) (a:natN n) (bs:seq (natN n)) : Pure (seq (natN n))
  (requires True)
  (ensures fun xs -> length xs = length bs + 1)
  =
  let f (i:nat{i <= length bs}) : natN n = if i = length bs then 0 else mul_lo a bs.[i] in
  init (length bs + 1) f

let seq_scale_hi (#n:pos) (a:natN n) (bs:seq (natN n)) (d:natN n) : Pure (seq (natN n))
  (requires True)
  (ensures fun xs -> length xs = length bs + 1)
  =
  let f (i:nat{i <= length bs}) : natN n = if i = 0 then d else mul_hi a bs.[i - 1] in
  init (length bs + 1) f

// a * bs + d
let seq_scale (#n:pos) (a:natN n) (bs:seq (natN n)) (d:natN n) : Pure (seq (natN n))
  (requires True)
  (ensures fun xs -> length xs = length bs + 1)
  =
  fst (seq_add (seq_scale_lo a bs) (seq_scale_hi a bs d) 0)

val lemma_sum_seq_left_right (s:seq int) (i j:nat) : Lemma
  (requires i <= j /\ j <= length s)
  (ensures sum_seq_left s i j == sum_seq_right s i j)

val lemma_pow_nat (a:nat) (b:nat) : Lemma (0 <= pow_int a b)

val lemma_sum_pow_seq_bound (#n:nat) (s:seq (natN n)) : Lemma
  (ensures 0 <= sum_pow_seq s /\ sum_pow_seq s < pow_int n (length s))

let rec seq_add_is (#n:nat) (as bs:seq (natN n)) (c0:nat1) (i:nat) : Pure Type0
  (requires length as == length bs /\ i <= length as)
  (ensures fun _ -> True)
  =
  if i = 0 then True else
  seq_add_is as bs c0 (i - 1) /\ (fst (seq_add as bs c0)).[i - 1] == seq_add_i as bs c0 (i - 1)

unfold let seq_add_is_norm (#n:nat) (as bs:seq (natN n)) (c0:nat1) (i:nat) : Pure Type0
  (requires length as == length bs /\ i <= length as)
  (ensures fun _ -> True)
  =
  norm [iota; zeta; primops; delta_only [`%seq_add_is]] (seq_add_is as bs c0 i)

val lemma_seq_add_is_norm (#n:nat) (as bs:seq (natN n)) (c0:nat1) (i:nat) : Lemma
  (requires length as == length bs /\ i <= length as)
  (ensures seq_add_is as bs c0 i == seq_add_is_norm as bs c0 i)

val lemma_last_carry_mul (a b:nat) (c:nat1) : Lemma (last_carry a b c == c * pow_int a b)

val lemma_add_lo_mul_right (#n:nat) (a b:natN n) (c:nat1) (m:int) : Lemma
  (add_lo a b c * m == (let x = a * m + b * m + c * m in if a + b + c < n then x else x - n * m))

val lemma_seq_add (#n:nat) (as bs:seq (natN n)) (c0:nat1) : Lemma
  (requires length bs == length as)
  (ensures (
    let (xs, ci) = seq_add as bs c0 in
    sum_pow_seq xs + last_carry n (length as) ci == sum_pow_seq as + sum_pow_seq bs + c0
  ))

val lemma_seq_scale_carry (#n:nat) (a:natN n) (bs:seq (natN n)) (d:natN n) : Lemma
  (ensures (
    snd (seq_add (seq_scale_lo a bs) (seq_scale_hi a bs d) 0) == 0
  ))

val lemma_seq_scale (#n:nat) (a:natN n) (bs:seq (natN n)) (d:natN n) : Lemma
  (ensures (
    sum_pow_seq (seq_scale a bs d) == sum_pow_seq (seq_scale_lo a bs) + sum_pow_seq (seq_scale_hi a bs d) /\
    sum_pow_seq (seq_scale a bs d) == a * sum_pow_seq bs + d
  ))

let ys_init (#n:nat) (a:natN n) (bs:seq (natN n)) (i:nat{i <= length bs}) : natN n =
  if i = length bs then 0 else mul_lo a bs.[i]

let zs_init (#n:nat) (a:natN n) (bs:seq (natN n)) (d:natN n) (i:nat{i <= length bs}) : natN n =
  if i = 0 then d else mul_hi a bs.[i - 1]

let init_ys (#n:nat) (a:natN n) (bs:seq (natN n)) : seq (natN n) =
  init (length bs + 1) (ys_init a bs)

let init_zs (#n:nat) (a:natN n) (bs:seq (natN n)) (d:natN n) : seq (natN n) =
  init (length bs + 1) (zs_init a bs d)

val lemma_scale_add (#n:nat) (l:nat) (a d:natN n) (bs rs ys zs qs xs:seq (natN n)) : Lemma
  (requires length bs == l /\ length rs == l + 1 /\ rs.[l] == 0)
  (ensures (
    let c0 = 0 in
    let ys = init (l + 1) (ys_init a bs) in
    let zs = init (l + 1) (zs_init a bs d) in
    let (qs, qc) = seq_add rs zs c0 in
    let (xs, xc) = seq_add qs ys c0 in
    sum_pow_seq xs == sum_pow_seq rs + a * sum_pow_seq bs + d /\ qc == 0 /\ xc == 0
  ))
