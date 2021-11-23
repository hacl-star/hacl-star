module Spec.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Lib.Exponentiation
module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

val exp_rl_lemma_loop: #t:Type -> k:concrete_ops t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i <= bBits} ->
  Lemma (let one = k.one () in
    let (accs, cs) = Loops.repeati i (S.exp_rl_f k.to.cm bBits b) (k.to.refl one, k.to.refl a) in
    let (acc, c) = Loops.repeati i (exp_rl_f k bBits b) (one, a) in
    k.to.refl acc == accs /\ k.to.refl c == cs)

let rec exp_rl_lemma_loop #t k a bBits b i =
  let one = k.one () in
  let inp0 = (k.to.refl one, k.to.refl a) in
  let inp1 = (one, a) in
  let f0 = S.exp_rl_f k.to.cm bBits b in
  let f1 = exp_rl_f k bBits b in

  if i = 0 then begin
    Loops.eq_repeati0 bBits f0 inp0;
    Loops.eq_repeati0 bBits f1 inp1 end
  else begin
    exp_rl_lemma_loop #t k a bBits b (i - 1);
    Loops.unfold_repeati bBits f0 inp0 (i - 1);
    Loops.unfold_repeati bBits f1 inp1 (i - 1) end


let exp_rl_lemma #t k a bBits b =
  exp_rl_lemma_loop #t k a bBits b bBits


val exp_mont_ladder_swap_lemma_loop: #t:Type -> k:concrete_ops t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i <= bBits} ->
  Lemma (let one = k.one () in
    let (r0s, r1s, sws) =
      Loops.repeati i (S.exp_mont_ladder_swap_f k.to.cm bBits b) (k.to.refl one, k.to.refl a, 0) in
    let (r0, r1, sw) =
      Loops.repeati i (exp_mont_ladder_swap_f k bBits b) (one, a, 0) in
    k.to.refl r0 == r0s /\ k.to.refl r1 == r1s /\ sw == sws)

let rec exp_mont_ladder_swap_lemma_loop #t k a bBits b i =
  let one = k.one () in
  let inp0 = (k.to.refl one, k.to.refl a, 0) in
  let inp1 = (one, a, 0) in
  let f0 = S.exp_mont_ladder_swap_f k.to.cm bBits b in
  let f1 = exp_mont_ladder_swap_f k bBits b in

  if i = 0 then begin
    Loops.eq_repeati0 bBits f0 inp0;
    Loops.eq_repeati0 bBits f1 inp1 end
  else begin
    exp_mont_ladder_swap_lemma_loop #t k a bBits b (i - 1);
    Loops.unfold_repeati bBits f0 inp0 (i - 1);
    Loops.unfold_repeati bBits f1 inp1 (i - 1) end


let exp_mont_ladder_swap_lemma #t k a bBits b =
  exp_mont_ladder_swap_lemma_loop #t k a bBits b bBits


val exp_pow2_lemma_loop: #t:Type -> k:concrete_ops t -> a:t -> b:nat -> i:nat{i <= b} ->
  Lemma (
    let accs = Loops.repeat i (S.sqr k.to.cm) (k.to.refl a) in
    let acc = Loops.repeat i k.sqr a in
    k.to.refl acc == accs)

let rec exp_pow2_lemma_loop #t k a b i =
  if i = 0 then begin
    Loops.eq_repeat0 (S.sqr k.to.cm) (k.to.refl a);
    Loops.eq_repeat0 k.sqr a end
  else begin
    exp_pow2_lemma_loop #t k a b (i - 1);
    Loops.unfold_repeat b (S.sqr k.to.cm) (k.to.refl a) (i - 1);
    Loops.unfold_repeat b k.sqr a (i - 1) end


let exp_pow2_lemma #t k a b =
  exp_pow2_lemma_loop k a b b


val precomp_table_lemma_loop: #t:Type0 -> k:concrete_ops t -> a:t ->
  table_len:size_nat{1 < table_len} -> table:lseq t table_len -> i:nat{i <= table_len - 2} -> Lemma
  (requires
    k.to.refl table.[0] == S.pow k.to.cm (k.to.refl a) 0 /\
    k.to.refl table.[1] == S.pow k.to.cm (k.to.refl a) 1)
  (ensures
   (let table = Loops.repeati i (precomp_table_f k a table_len) table in
    (forall (j:nat{j < i + 2}). k.to.refl table.[j] == S.pow k.to.cm (k.to.refl a) j)))

let rec precomp_table_lemma_loop #t k a table_len table i =
  if i = 0 then
    Loops.eq_repeati0 i (precomp_table_f k a table_len) table
  else begin
    let table1 = Loops.repeati (i - 1) (precomp_table_f k a table_len) table in
    Loops.unfold_repeati i (precomp_table_f k a table_len) table (i - 1);
    precomp_table_lemma_loop k a table_len table (i - 1);
    assert ((forall (j:nat{j < i + 1}). k.to.refl table1.[j] == S.pow k.to.cm (k.to.refl a) j));
    let table = table1.[i + 1] <- k.mul table1.[i] a in
    assert ((forall (j:nat{j < i + 1}). k.to.refl table.[j] == S.pow k.to.cm (k.to.refl a) j));

    S.lemma_pow_add k.to.cm (k.to.refl a) i 1;
    S.lemma_pow1 k.to.cm (k.to.refl a);
    assert ((forall (j:nat{j < i + 2}). k.to.refl table.[j] == S.pow k.to.cm (k.to.refl a) j));
    () end


val precomp_table_lemma: #t:Type0 -> k:concrete_ops t -> a:t -> table_len:size_nat{1 < table_len} ->
  Lemma (let table = precomp_table k a table_len in
    (forall (i:nat{i < table_len}). k.to.refl table.[i] == S.pow k.to.cm (k.to.refl a) i))

let precomp_table_lemma #t k a table_len =
  let table = create table_len (k.one ()) in
  let table = table.[0] <- one () in
  let table = table.[1] <- a in
  S.lemma_pow0 k.to.cm (k.to.refl a);
  S.lemma_pow1 k.to.cm (k.to.refl a);
  precomp_table_lemma_loop k a table_len table (table_len - 2)


val exp_fw_lemma_loop: #t:Type -> k:concrete_ops t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos
  -> table_len:size_nat{1 < table_len /\ table_len = pow2 l} -> table:lseq t table_len
  -> acc0:t -> i:nat{i <= bBits / l} -> Lemma
  (requires
    (forall (i:nat{i < table_len}). k.to.refl table.[i] == S.pow k.to.cm (k.to.refl a) i))
  (ensures
    (let acc = Loops.repeati i (exp_fw_f k a bBits b l table_len table) acc0 in
     let accs = Loops.repeati i (S.exp_fw_f k.to.cm (k.to.refl a) bBits b l) (k.to.refl acc0) in
     k.to.refl acc == accs))

let rec exp_fw_lemma_loop #t k a bBits b l table_len table acc0 i =
  let f0 = exp_fw_f k a bBits b l table_len table in
  let f1 = S.exp_fw_f k.to.cm (k.to.refl a) bBits b l in

  if i = 0 then begin
    Loops.eq_repeati0 i f0 acc0;
    Loops.eq_repeati0 i f1 (k.to.refl acc0) end
  else begin
    let acc1 = Loops.repeati (i - 1) f0 acc0 in
    exp_fw_lemma_loop #t k a bBits b l table_len table acc0 (i - 1);
    Loops.unfold_repeati i f0 acc0 (i - 1);
    Loops.unfold_repeati i f1 (k.to.refl acc0) (i - 1);
    exp_pow2_lemma k acc1 l end


let exp_fw_lemma #t k a bBits b l =
  Math.Lemmas.pow2_lt_compat 32 l;
  Math.Lemmas.pow2_lt_compat l 0;
  let table_len : size_nat = pow2 l in
  precomp_table_lemma k a table_len;
  let table = precomp_table k a table_len in

  let acc0 = if bBits % l = 0 then one () else exp_fw_acc0 k a bBits b l table_len table in
  exp_fw_lemma_loop #t k a bBits b l table_len table acc0 (bBits / l)


val exp_double_fw_lemma_loop: #t:Type -> k:concrete_ops t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos
  -> table_len:size_nat{1 < table_len /\ table_len = pow2 l}
  -> table1:lseq t table_len -> table2:lseq t table_len
  -> acc0:t -> i:nat{i <= bBits / l} -> Lemma
  (requires
    (forall (i:nat{i < table_len}). k.to.refl table1.[i] == S.pow k.to.cm (k.to.refl a1) i) /\
    (forall (i:nat{i < table_len}). k.to.refl table2.[i] == S.pow k.to.cm (k.to.refl a2) i))
  (ensures
    (let acc = Loops.repeati i (exp_double_fw_f k a1 bBits b1 a2 b2 l table_len table1 table2) acc0 in
     let accs = Loops.repeati i (S.exp_double_fw_f k.to.cm (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l) (k.to.refl acc0) in
     k.to.refl acc == accs))

let rec exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l table_len table1 table2 acc0 i =
  let f0 = exp_double_fw_f k a1 bBits b1 a2 b2 l table_len table1 table2 in
  let f1 = S.exp_double_fw_f k.to.cm (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l in

  if i = 0 then begin
    Loops.eq_repeati0 i f0 acc0;
    Loops.eq_repeati0 i f1 (k.to.refl acc0) end
  else begin
    let acc1 = Loops.repeati (i - 1) f0 acc0 in
    exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l table_len table1 table2 acc0 (i - 1);
    Loops.unfold_repeati i f0 acc0 (i - 1);
    Loops.unfold_repeati i f1 (k.to.refl acc0) (i - 1);
    exp_pow2_lemma k acc1 l end


let exp_double_fw_lemma #t k a1 bBits b1 a2 b2 l =
  Math.Lemmas.pow2_lt_compat 32 l;
  Math.Lemmas.pow2_lt_compat l 0;
  let table_len : size_nat = pow2 l in
  precomp_table_lemma k a1 table_len;
  precomp_table_lemma k a2 table_len;
  let table1 = precomp_table k a1 table_len in
  let table2 = precomp_table k a2 table_len in

  let acc0 =
    if bBits % l = 0 then one ()
    else exp_double_fw_acc0 k a1 bBits b1 a2 b2 l table_len table1 table2 in

  exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l table_len table1 table2 acc0 (bBits / l)
