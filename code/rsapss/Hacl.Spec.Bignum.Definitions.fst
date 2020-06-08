module Hacl.Spec.Bignum.Definitions

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val blocks: x: size_pos -> m: size_pos -> Tot (r:size_pos{x <= m * r})
let blocks x m = (x - 1) / m + 1


let lbignum len = lseq uint64 len

// TODO: replace with the `nat_from_intseq_le` function?
val eval_: len:size_nat -> s:lbignum len -> i:nat{i <= len} -> nat
let rec eval_ len s i =
  if i = 0 then 0
  else eval_ len s (i - 1) + v s.[i - 1] * pow2 (64 * (i - 1))

let bn_v (#len:size_nat) (s:lbignum len) = eval_ len s len

///
///  Lemmas
///

#set-options "--fuel 2"
val bn_eval0: #len:size_nat -> b:lbignum len -> Lemma (eval_ len b 0 == 0)
let bn_eval0 #len b = ()

val bn_eval1: b:lbignum 1 -> Lemma (bn_v b == v b.[0])
let bn_eval1 b = ()

val bn_eval_unfold_i: #len:size_pos -> b:lbignum len -> i:pos{i <= len} -> Lemma
  (eval_ len b i == eval_ len b (i - 1) + v b.[i - 1] * pow2 (64 * (i - 1)))
let bn_eval_unfold_i #len b i = ()


val bn_eval_zeroes: len:size_nat -> i:nat{i <= len} -> Lemma (eval_ len (create len (u64 0)) i == 0)
let rec bn_eval_zeroes len i =
  if i = 0 then ()
  else bn_eval_zeroes len (i - 1)

val bn_eval_create1: c:uint64 -> Lemma (bn_v (create 1 c) == v c)
let bn_eval_create1 c =
  bn_eval1 (create 1 c)


val bn_eval_extensionality_j:
    #len1:size_nat
  -> #len2:size_nat
  -> b1:lbignum len1
  -> b2:lbignum len2
  -> j:nat{j <= len1 /\ j <= len2} ->
  Lemma
    (requires sub b1 0 j == sub b2 0 j)
    (ensures  eval_ len1 b1 j == eval_ len2 b2 j)
    (decreases j)

let rec bn_eval_extensionality_j #len1 #len2 b1 b2 j =
  if j = 0 then ()
  else begin
    let b1j = slice b1 0 j in
    let b2j = slice b2 0 j in
    let c1 = slice b1j 0 (j - 1) in
    let c2 = slice b2j 0 (j - 1) in
    eq_intro c1 c2;
    bn_eval_extensionality_j #len1 #len2 b1 b2 (j - 1);
    Seq.lemma_index_slice b1 0 j (j - 1);
    Seq.lemma_index_slice b2 0 j (j - 1);
    assert (v b1.[j - 1] == v b2.[j - 1]);
    () end


val bn_eval_snoc: #len:size_nat{len + 1 <= max_size_t} -> b:lbignum len -> e:uint64 -> Lemma
  (bn_v #(len + 1) (Seq.snoc b e) == bn_v #len b + v e * pow2 (64 * len))

let bn_eval_snoc #len b e =
  let b1 = Seq.snoc b e in
  bn_eval_unfold_i #(len + 1) b1 (len + 1);
  bn_eval_extensionality_j #(len+1) #len b1 (slice #_ #(len+1) b1 0 len) len;
  eq_intro (sub #uint64 #(len + 1) b1 0 len) b


// val bn_eval_sub: #len:size_nat -> b:lbignum len -> j:nat{j <= len} -> Lemma
//   (eval_ len b j == eval_ j (sub b 0 j) j)
// let bn_eval_sub #len b j =
//   bn_eval_extensionality_j #len #j b (sub b 0 j) j


val bn_eval_split_i_aux: a:nat -> b:nat -> c:nat -> i:nat -> Lemma
  (requires pow2 64 * c == a - b)
  (ensures pow2 (64 * (i + 1)) * c == pow2 (64 * i) * a - pow2 (64 * i) * b)

let bn_eval_split_i_aux a b c i =
  calc (==) {
    pow2 (64 * (i + 1)) * c;
    (==) { Math.Lemmas.pow2_plus (64 * i) 64 }
    pow2 (64 * i) * pow2 64 * c;
    (==) { Math.Lemmas.paren_mul_right (pow2 (64 * i)) (pow2 64) c }
    pow2 (64 * i) * (pow2 64 * c);
    (==) { }
    pow2 (64 * i) * (a - b);
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * i)) a b }
    pow2 (64 * i) * a - pow2 (64 * i) * b;
  }


val bn_eval_split_i: #len:size_nat -> b:lbignum len -> i:nat{i <= len} -> Lemma
  (ensures bn_v b == bn_v (slice b 0 i) + pow2 (64 * i) * bn_v (slice b i len))
  (decreases (len - i))

let rec bn_eval_split_i #len b i =
  if i = 0 then ()
  else begin
    if len = i then ()
    else begin
      let b1 = slice b i len in
      bn_eval_split_i b1 1;
      assert (bn_v b1 == v b1.[0] + pow2 64 * bn_v (slice b1 1 (len - i)));
      Seq.lemma_index_slice b i len 0;
      assert (bn_v b1 == v b.[i] + pow2 64 * bn_v (slice b (i + 1) len));
      calc (==) {
        bn_v b;
        (==) { bn_eval_split_i b (i + 1) }
        bn_v (slice b 0 (i + 1)) + pow2 (64 * (i + 1)) * bn_v (slice b (i + 1) len);
        (==) { bn_eval_split_i_aux (bn_v b1) (v b.[i]) (bn_v (slice b (i + 1) len)) i }
        bn_v (slice b 0 (i + 1)) + pow2 (64 * i) * bn_v b1 - pow2 (64 * i) * v b.[i];
        (==) { bn_eval_unfold_i b (i + 1) }
        eval_ (i + 1) (slice b 0 (i + 1)) i + pow2 (64 * i) * bn_v b1;
        (==) { bn_eval_extensionality_j (slice b 0 (i + 1)) (slice b 0 i) i }
        eval_ i (slice b 0 i) i + pow2 (64 * i) * bn_v b1;
      }; () end end


val bn_eval_inj: len:size_nat -> b1:lbignum len -> b2: lbignum len -> Lemma
  (requires bn_v b1 == bn_v b2)
  (ensures  equal b1 b2)
  (decreases len)

let rec bn_eval_inj len b1 b2 =
  if len = 0 then ()
  else begin
    bn_eval_split_i b1 1;
    bn_eval_split_i b2 1;
    bn_eval_inj (len - 1) (slice b1 1 len) (slice b2 1 len);
    Seq.lemma_split b1 1;
    Seq.lemma_split b2 1
  end


val bn_eval_bound: #len:size_nat -> b:lbignum len -> i:nat{i <= len} -> Lemma
  (eval_ len b i < pow2 (64 * i))

let rec bn_eval_bound #len b i =
  if i = 0 then ()
  else begin
    bn_eval_unfold_i b i;
    assert (eval_ len b i == eval_ len b (i - 1) + pow2 (64 * (i - 1)) * v b.[i - 1]);
    calc (<) {
      eval_ len b (i - 1) + pow2 (64 * (i - 1)) * v b.[i - 1];
      (<) { bn_eval_bound #len b (i - 1) }
      pow2 (64 * (i - 1)) + pow2 (64 * (i - 1)) * v b.[i - 1];
      (==) { Math.Lemmas.distributivity_add_right (pow2 (64 * (i - 1))) 1 (v b.[i - 1]) }
      pow2 (64 * (i - 1)) * (1 + v b.[i - 1]);
      (<=) { Math.Lemmas.lemma_mult_le_left (pow2 (64 * (i - 1))) (1 + v b.[i - 1]) (pow2 64) }
      pow2 (64 * (i - 1)) * pow2 64;
      (==) { Math.Lemmas.pow2_plus (64 * (i - 1)) 64 }
      pow2 (64 * i);
    };
    assert (eval_ len b i < pow2 (64 * i))
    end


#set-options "--fuel 0"

val bn_eval_update_sub: len1:size_nat -> b1:lbignum len1 -> len2:size_nat{len1 <= len2} ->
  Lemma (let b2 = create len2 (u64 0) in bn_v b1 == bn_v (update_sub b2 0 len1 b1))

let bn_eval_update_sub len1 b1 len2 =
  let b2 = create len2 (u64 0) in
  let b2 = update_sub b2 0 len1 b1 in
  bn_eval_split_i b2 len1;
  assert (bn_v b2 == bn_v b1 + pow2 (64 * len1) * bn_v (slice b2 len1 len2));
  let b_zeroes = create (len2 - len1) (u64 0) in
  eq_intro b_zeroes (slice b2 len1 len2);
  bn_eval_zeroes (len2 - len1) (len2 - len1)


val bn_eval_index: #len:size_nat -> b:lbignum len -> i:nat{i < len} -> Lemma
  (v b.[i] == bn_v b / pow2 (64 * i) % pow2 64)

let bn_eval_index #len b i =
  calc (==) {
    bn_v b / pow2 (64 * i) % pow2 64;
    (==) { bn_eval_split_i #len b i }
    (bn_v (slice b 0 i) + pow2 (64 * i) * bn_v (slice b i len)) / pow2 (64 * i) % pow2 64;
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice b 0 i)) (pow2 (64 * i)) (bn_v (slice b i len)) }
    (bn_v (slice b 0 i) / pow2 (64 * i) + bn_v (slice b i len)) % pow2 64;
    (==) { bn_eval_bound (slice b 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice b 0 i)) (pow2 (64 * i)) }
    bn_v (slice b i len) % pow2 64;
    (==) { bn_eval_split_i (slice b i len) 1 }
    (bn_v (slice b i (i + 1)) + pow2 64 * bn_v (slice b (i + 1) len)) % pow2 64;
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v (slice b i (i + 1))) (pow2 64) (bn_v (slice b (i + 1) len)) }
    bn_v (slice b i (i + 1)) % pow2 64;
    (==) { bn_eval1 (slice b i (i + 1)); Seq.lemma_index_slice b i (i + 1) 0 }
    v b.[i] % pow2 64;
    (==) { Math.Lemmas.modulo_lemma (v b.[i]) (pow2 64) }
    v b.[i];
  };
  assert (bn_v b / pow2 (64 * i) % pow2 64 == v b.[i])


val bn_mask_lemma: #len:size_nat -> b:lbignum len -> mask:uint64 -> Lemma
  (requires v mask == v (ones U64 SEC) \/ v mask == 0)
  (ensures  bn_v (map (logand mask) b) == (if v mask = 0 then 0 else bn_v b))

let bn_mask_lemma #len b mask =
  let res = map (logand mask) b in
  //assert (forall (i:nat{i < len}). res.[i] == (mask &. b.[i]));
  let lemma_aux (i:nat{i < len}) : Lemma (v res.[i] == (if v mask = 0 then 0 else v b.[i])) =
    logand_lemma mask b.[i] in

  Classical.forall_intro lemma_aux;

  if v mask = 0 then begin
    eq_intro res (create len (u64 0));
    bn_eval_zeroes len len;
    assert (bn_v res == 0) end
  else eq_intro res b


inline_for_extraction noextract
val mask_select: mask:uint64 -> a:uint64 -> b:uint64 -> uint64
let mask_select mask a b =
  (mask &. a) |. ((lognot mask) &. b)

val mask_select_lemma: mask:uint64 -> a:uint64 -> b:uint64 -> Lemma
  (requires v mask == v (ones U64 SEC) \/ v mask == 0)
  (ensures  (mask_select mask a b) == (if v mask = 0 then b else a))

let mask_select_lemma mask a b =
  if v mask = 0 then begin
    logand_lemma mask a;
    assert (v (mask &. a) = 0);
    lognot_lemma mask;
    assert (v (lognot mask) = v (ones U64 SEC));
    logand_lemma (lognot mask) b;
    assert (v ((lognot mask) &. b) == v b);
    logor_lemma (mask &. a) ((lognot mask) &. b);
    assert (v (mask_select mask a b) == v b) end
  else begin
    logand_lemma mask a;
    assert (v (mask &. a) = v a);
    lognot_lemma mask;
    assert (v (lognot mask) = 0);
    logand_lemma (lognot mask) b;
    assert (v ((lognot mask) &. b) == 0);
    logor_zeros (mask &. a);
    assert (v (mask_select mask a b) == v a) end


val bn_mask_select_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len -> mask:uint64 -> Lemma
  (requires v mask == v (ones U64 SEC) \/ v mask == 0)
  (ensures  bn_v (map2 (mask_select mask) a b) == (if v mask = 0 then bn_v b else bn_v a))

let bn_mask_select_lemma #len a b mask =
  let res = map2 (mask_select mask) a b in

  let lemma_aux (i:nat{i < len}) : Lemma (v res.[i] == (if v mask = 0 then v b.[i] else v a.[i])) =
    mask_select_lemma mask a.[i] b.[i] in

  Classical.forall_intro lemma_aux;
  if v mask = 0 then eq_intro res b else eq_intro res a


val bn_eval_lt: len:size_nat -> a:lbignum len -> b:lbignum len -> k:pos{k <= len} -> Lemma
  (requires v a.[k - 1] < v b.[k - 1])
  (ensures  eval_ len a k < eval_ len b k)

let bn_eval_lt len a b k =
  calc (==) {
    eval_ len b k - eval_ len a k;
    (==) { bn_eval_unfold_i b k }
    eval_ len b (k - 1) + v b.[k - 1] * pow2 (64 * (k - 1)) - eval_ len a k;
    (==) { bn_eval_unfold_i a k }
    eval_ len b (k - 1) + v b.[k - 1] * pow2 (64 * (k - 1)) - eval_ len a (k - 1) - v a.[k - 1] * pow2 (64 * (k - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v b.[k - 1]) (v a.[k - 1]) (pow2 (64 * (k - 1))) }
    eval_ len b (k - 1) - eval_ len a (k - 1) + (v b.[k - 1] - v a.[k - 1]) * pow2 (64 * (k - 1));
  };
  bn_eval_bound a (k - 1);
  bn_eval_bound b (k - 1);
  assert (eval_ len b (k - 1) - eval_ len a (k - 1) > - pow2 (64 * (k - 1)));
  assert ((v b.[k - 1] - v a.[k - 1]) * pow2 (64 * (k - 1)) >= pow2 (64 * (k - 1)))
