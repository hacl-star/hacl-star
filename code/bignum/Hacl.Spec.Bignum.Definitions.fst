module Hacl.Spec.Bignum.Definitions

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val blocks: x:size_pos -> m:size_pos -> Tot (r:size_pos{x <= m * r})
let blocks x m = (x - 1) / m + 1

inline_for_extraction noextract
let limb_t = t:inttype{t = U32 \/ t = U64}
inline_for_extraction noextract
let limb (t:limb_t) = uint_t t SEC
let lbignum (t:limb_t) len = lseq (limb t) len

val eval_: #t:limb_t -> len:size_nat -> s:lbignum t len -> i:nat{i <= len} -> nat
let rec eval_ #t len s i =
  if i = 0 then 0
  else eval_ #t len s (i - 1) + v s.[i - 1] * pow2 (bits t * (i - 1))

let bn_v (#t:limb_t) (#len:size_nat) (s:lbignum t len) = eval_ #t len s len

///
///  Lemmas
///

#push-options "--fuel 2"
val bn_eval0: #t:limb_t -> #len:size_nat -> b:lbignum t len -> Lemma (eval_ len b 0 == 0)
let bn_eval0 #t #len b = ()

val bn_eval1: #t:limb_t -> b:lbignum t 1 -> Lemma (bn_v b == v b.[0])
let bn_eval1 b = ()

val bn_eval_unfold_i: #t:limb_t -> #len:size_pos -> b:lbignum t len -> i:pos{i <= len} ->
  Lemma (eval_ len b i == eval_ len b (i - 1) + v b.[i - 1] * pow2 (bits t * (i - 1)))
let bn_eval_unfold_i #t #len b i = ()
#pop-options

val bn_eval_zeroes: #t:limb_t -> len:size_nat -> i:nat{i <= len} ->
  Lemma (eval_ len (create len (uint #t 0)) i == 0)
let rec bn_eval_zeroes #t len i =
  let b = create len (uint #t 0) in
  if i = 0 then
    bn_eval0 b
  else begin
    bn_eval_unfold_i b i;
    bn_eval_zeroes #t len (i - 1) end

val bn_eval_create1: #t:limb_t -> c:limb t -> Lemma (bn_v (create 1 c) == v c)
let bn_eval_create1 #t c =
  bn_eval1 (create 1 c)


val bn_eval_extensionality_j:
    #t:limb_t
  -> #len1:size_nat
  -> #len2:size_nat
  -> b1:lbignum t len1
  -> b2:lbignum t len2
  -> j:nat{j <= len1 /\ j <= len2} ->
  Lemma
    (requires sub b1 0 j == sub b2 0 j)
    (ensures  eval_ len1 b1 j == eval_ len2 b2 j)
    (decreases j)

let rec bn_eval_extensionality_j #t #len1 #len2 b1 b2 j =
  if j = 0 then begin
    bn_eval0 b1;
    bn_eval0 b2 end
  else begin
    bn_eval_unfold_i b1 j;
    bn_eval_unfold_i b2 j;
    let b1j = slice b1 0 j in
    let b2j = slice b2 0 j in
    let c1 = slice b1j 0 (j - 1) in
    let c2 = slice b2j 0 (j - 1) in
    eq_intro c1 c2;
    bn_eval_extensionality_j #t #len1 #len2 b1 b2 (j - 1);
    Seq.lemma_index_slice b1 0 j (j - 1);
    Seq.lemma_index_slice b2 0 j (j - 1);
    assert (v b1.[j - 1] == v b2.[j - 1]);
    () end


val bn_eval_snoc: #t:limb_t -> #len:size_nat{len + 1 <= max_size_t} -> b:lbignum t len -> e:limb t ->
  Lemma (bn_v #t #(len + 1) (Seq.snoc b e) == bn_v b + v e * pow2 (bits t * len))

let bn_eval_snoc #t #len b e =
  let b1 = Seq.snoc b e in
  bn_eval_unfold_i #t #(len + 1) b1 (len + 1);
  bn_eval_extensionality_j #t #(len+1) #len b1 (slice #_ #(len+1) b1 0 len) len;
  eq_intro (sub #_ #(len + 1) b1 0 len) b


val bn_eval_split_i_aux: p:nat -> a:nat -> b:nat -> c:nat -> i:nat -> Lemma
  (requires pow2 p * c == a - b)
  (ensures pow2 (p * (i + 1)) * c == pow2 (p * i) * a - pow2 (p * i) * b)

let bn_eval_split_i_aux p a b c i =
  calc (==) {
    pow2 (p * (i + 1)) * c;
    (==) { Math.Lemmas.pow2_plus (p * i) p }
    pow2 (p * i) * pow2 p * c;
    (==) { Math.Lemmas.paren_mul_right (pow2 (p * i)) (pow2 p) c }
    pow2 (p * i) * (pow2 p * c);
    (==) { }
    pow2 (p * i) * (a - b);
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (p * i)) a b }
    pow2 (p * i) * a - pow2 (p * i) * b;
  }


val bn_eval_split_i: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:nat{i <= len} -> Lemma
  (ensures bn_v b == bn_v (slice b 0 i) + pow2 (bits t * i) * bn_v (slice b i len))
  (decreases (len - i))

let rec bn_eval_split_i #t #len b i =
  let pbits = bits t in
  if i = 0 then
    bn_eval0 (slice b 0 i)
  else begin
    if len = i then
      bn_eval0 (slice b i len)
    else begin
      let b1 = slice b i len in
      bn_eval_split_i b1 1;
      bn_eval1 (slice b1 0 1);
      assert (bn_v b1 == v b1.[0] + pow2 pbits * bn_v (slice b1 1 (len - i)));
      Seq.lemma_index_slice b i len 0;
      assert (bn_v b1 == v b.[i] + pow2 pbits * bn_v (slice b (i + 1) len));
      calc (==) {
        bn_v b;
        (==) { bn_eval_split_i b (i + 1) }
        bn_v (slice b 0 (i + 1)) + pow2 (pbits * (i + 1)) * bn_v (slice b (i + 1) len);
        (==) { bn_eval_split_i_aux pbits (bn_v b1) (v b.[i]) (bn_v (slice b (i + 1) len)) i }
        bn_v (slice b 0 (i + 1)) + pow2 (pbits * i) * bn_v b1 - pow2 (pbits * i) * v b.[i];
        (==) { bn_eval_unfold_i (slice b 0 (i + 1)) (i + 1)}
        eval_ (i + 1) (slice b 0 (i + 1)) i + pow2 (pbits * i) * bn_v b1;
        (==) { bn_eval_extensionality_j (slice b 0 (i + 1)) (slice b 0 i) i }
        eval_ i (slice b 0 i) i + pow2 (pbits * i) * bn_v b1;
      }; () end end


val bn_eval_inj: #t:limb_t -> len:size_nat -> b1:lbignum t len -> b2:lbignum t len -> Lemma
  (requires bn_v b1 == bn_v b2)
  (ensures  equal b1 b2)
  (decreases len)

let rec bn_eval_inj #t len b1 b2 =
  if len = 0 then ()
  else begin
    bn_eval_split_i b1 1;
    bn_eval_split_i b2 1;
    bn_eval1 (slice b1 0 1);
    bn_eval1 (slice b2 0 1);
    bn_eval_inj (len - 1) (slice b1 1 len) (slice b2 1 len);
    Seq.lemma_split b1 1;
    Seq.lemma_split b2 1
  end


val bn_eval_bound: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:nat{i <= len} ->
  Lemma (eval_ len b i < pow2 (bits t * i))

let rec bn_eval_bound #t #len b i =
  let pbits = bits t in
  if i = 0 then
    bn_eval0 b
  else begin
    bn_eval_unfold_i b i;
    assert (eval_ len b i == eval_ len b (i - 1) + pow2 (pbits * (i - 1)) * v b.[i - 1]);
    calc (<) {
      eval_ len b (i - 1) + pow2 (pbits * (i - 1)) * v b.[i - 1];
      (<) { bn_eval_bound #t #len b (i - 1) }
      pow2 (pbits * (i - 1)) + pow2 (pbits * (i - 1)) * v b.[i - 1];
      (==) { Math.Lemmas.distributivity_add_right (pow2 (pbits * (i - 1))) 1 (v b.[i - 1]) }
      pow2 (pbits * (i - 1)) * (1 + v b.[i - 1]);
      (<=) { Math.Lemmas.lemma_mult_le_left (pow2 (pbits * (i - 1))) (1 + v b.[i - 1]) (pow2 pbits) }
      pow2 (pbits * (i - 1)) * pow2 pbits;
      (==) { Math.Lemmas.pow2_plus (pbits * (i - 1)) pbits }
      pow2 (pbits * i);
    };
    assert (eval_ len b i < pow2 (pbits * i))
    end


val bn_eval_index: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:nat{i < len} ->
  Lemma (v b.[i] == bn_v b / pow2 (bits t * i) % pow2 (bits t))

let bn_eval_index #t #len b i =
  let pbits = bits t in

  calc (==) {
    bn_v b / pow2 (pbits * i) % pow2 pbits;
    (==) { bn_eval_split_i #t #len b i }
    (bn_v (slice b 0 i) + pow2 (pbits * i) * bn_v (slice b i len)) / pow2 (pbits * i) % pow2 pbits;
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice b 0 i)) (pow2 (pbits * i)) (bn_v (slice b i len)) }
    (bn_v (slice b 0 i) / pow2 (pbits * i) + bn_v (slice b i len)) % pow2 pbits;
    (==) { bn_eval_bound (slice b 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice b 0 i)) (pow2 (pbits * i)) }
    bn_v (slice b i len) % pow2 pbits;
    (==) { bn_eval_split_i (slice b i len) 1 }
    (bn_v (slice b i (i + 1)) + pow2 pbits * bn_v (slice b (i + 1) len)) % pow2 pbits;
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v (slice b i (i + 1))) (pow2 pbits) (bn_v (slice b (i + 1) len)) }
    bn_v (slice b i (i + 1)) % pow2 pbits;
    (==) { bn_eval1 (slice b i (i + 1)); Seq.lemma_index_slice b i (i + 1) 0 }
    v b.[i] % pow2 pbits;
    (==) { Math.Lemmas.modulo_lemma (v b.[i]) (pow2 pbits) }
    v b.[i];
  };
  assert (bn_v b / pow2 (pbits * i) % pow2 pbits == v b.[i])



val bn_eval_lt: #t:limb_t -> len:size_nat -> a:lbignum t len -> b:lbignum t len -> k:pos{k <= len} -> Lemma
  (requires v a.[k - 1] < v b.[k - 1])
  (ensures  eval_ len a k < eval_ len b k)

let bn_eval_lt #t len a b k =
  let pbits = bits t in
  
  calc (==) {
    eval_ len b k - eval_ len a k;
    (==) { bn_eval_unfold_i b k }
    eval_ len b (k - 1) + v b.[k - 1] * pow2 (pbits * (k - 1)) - eval_ len a k;
    (==) { bn_eval_unfold_i a k }
    eval_ len b (k - 1) + v b.[k - 1] * pow2 (pbits * (k - 1)) - eval_ len a (k - 1) - v a.[k - 1] * pow2 (pbits * (k - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v b.[k - 1]) (v a.[k - 1]) (pow2 (pbits * (k - 1))) }
    eval_ len b (k - 1) - eval_ len a (k - 1) + (v b.[k - 1] - v a.[k - 1]) * pow2 (pbits * (k - 1));
  };
  bn_eval_bound a (k - 1);
  bn_eval_bound b (k - 1);
  assert (eval_ len b (k - 1) - eval_ len a (k - 1) > - pow2 (pbits * (k - 1)));
  assert ((v b.[k - 1] - v a.[k - 1]) * pow2 (pbits * (k - 1)) >= pow2 (pbits * (k - 1)))


val bn_eval_update_sub: #t:limb_t -> len1:size_nat -> b1:lbignum t len1 -> len2:size_nat{len1 <= len2} ->
  Lemma (let b2 = create len2 (uint #t 0) in bn_v b1 == bn_v (update_sub b2 0 len1 b1))

let bn_eval_update_sub #t len1 b1 len2 =
  let b2 = create len2 (uint #t 0) in
  let b2 = update_sub b2 0 len1 b1 in
  bn_eval_split_i b2 len1;
  assert (bn_v b2 == bn_v b1 + pow2 (bits t * len1) * bn_v (slice b2 len1 len2));
  let b_zeroes = create (len2 - len1) (uint #t 0) in
  eq_intro b_zeroes (slice b2 len1 len2);
  bn_eval_zeroes #t (len2 - len1) (len2 - len1)


val bn_update_sub_eval:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:nat{i + bLen <= aLen} ->
  Lemma (bn_v (update_sub a i bLen b) == bn_v a - bn_v (sub a i bLen) * pow2 (bits t * i) + bn_v b * pow2 (bits t * i))

let bn_update_sub_eval #t #aLen #bLen a b i =
  let pbits = bits t in
  let a' = update_sub a i bLen b in
  let c = bn_v (sub a i bLen) * pow2 (bits t * i) in

  calc (==) {
    bn_v a' + c;
    (==) { bn_eval_split_i a' i }
    bn_v (slice a' 0 i) + pow2 (pbits * i) * bn_v (slice a' i aLen) + c;
    (==) { eq_intro (slice a 0 i) (slice a' 0 i) }
    bn_v (slice a 0 i) + pow2 (pbits * i) * bn_v (slice a' i aLen) + c;
    (==) { bn_eval_split_i (slice a' i aLen) bLen }
    bn_v (slice a 0 i) + pow2 (pbits * i) * (bn_v (sub a' i bLen) + pow2 (pbits * bLen) * bn_v (slice a' (i + bLen) aLen)) + c;
    (==) { eq_intro (slice a' (i + bLen) aLen) (slice a (i + bLen) aLen) }
    bn_v (slice a 0 i) + pow2 (pbits * i) * (bn_v (sub a' i bLen) + pow2 (pbits * bLen) * bn_v (slice a (i + bLen) aLen)) + c;
    (==) {eq_intro (sub a' i bLen) b }
    bn_v (slice a 0 i) + pow2 (pbits * i) * (bn_v b + pow2 (pbits * bLen) * bn_v (slice a (i + bLen) aLen)) + c;
    (==) { Math.Lemmas.distributivity_add_right (pow2 (pbits * i)) (bn_v b) (pow2 (pbits * bLen) * bn_v (slice a (i + bLen) aLen)) }
    bn_v (slice a 0 i) + pow2 (pbits * i) * bn_v b + pow2 (pbits * i) * (pow2 (pbits * bLen) * bn_v (slice a (i + bLen) aLen)) + c;
    (==) { Math.Lemmas.paren_mul_right (pow2 (pbits * i)) (pow2 (pbits * bLen)) (bn_v (slice a (i + bLen) aLen));
           Math.Lemmas.pow2_plus (pbits * i) (pbits * bLen) }
    bn_v (slice a 0 i) + pow2 (pbits * i) * bn_v b + pow2 (pbits * (i + bLen)) * bn_v (slice a (i + bLen) aLen) + c;
    (==) { bn_eval_split_i (slice a 0 (i + bLen)) i }
    bn_v (slice a 0 (i + bLen)) + pow2 (pbits * i) * bn_v b + pow2 (pbits * (i + bLen)) * bn_v (slice a (i + bLen) aLen);
    (==) { bn_eval_split_i a (i + bLen) }
    bn_v a + pow2 (pbits * i) * bn_v b;
    }


val bn_mask_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> mask:limb t -> Lemma
  (requires v mask == v (ones t SEC) \/ v mask == 0)
  (ensures  bn_v (map (logand mask) b) == (if v mask = 0 then 0 else bn_v b))

let bn_mask_lemma #t #len b mask =
  let res = map (logand mask) b in
  //assert (forall (i:nat{i < len}). res.[i] == (mask &. b.[i]));
  let lemma_aux (i:nat{i < len}) : Lemma (v res.[i] == (if v mask = 0 then 0 else v b.[i])) =
    logand_lemma mask b.[i] in

  Classical.forall_intro lemma_aux;

  if v mask = 0 then begin
    eq_intro res (create len (uint #t 0));
    bn_eval_zeroes #t len len;
    assert (bn_v res == 0) end
  else eq_intro res b
