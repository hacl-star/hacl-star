module Hacl.Spec.Bignum

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let bn_add #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_add a b

let bn_add_lemma #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_add_lemma a b

let bn_sub #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_sub a b

let bn_sub_lemma #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_sub_lemma a b

let bn_mul #aLen #bLen a b =
  Hacl.Spec.Bignum.Multiplication.bn_mul a b

let bn_mul_lemma #aLen #bLen a b =
  Hacl.Spec.Bignum.Multiplication.bn_mul_lemma a b

let bn_mul1_lshift_add #aLen #resLen a b j acc =
  Hacl.Spec.Bignum.Multiplication.bn_mul1_lshift_add a b j acc

let bn_mul1_lshift_add_lemma #aLen #resLen a b j acc =
  Hacl.Spec.Bignum.Multiplication.bn_mul1_lshift_add_lemma a b j acc

let bn_rshift #len b i =
  slice b i len

let bn_rshift_lemma #len c i =
  calc (==) {
    bn_v c / pow2 (64 * i);
    (==) { bn_eval_split_i c i }
    (bn_v (slice c 0 i) + pow2 (64 * i) * bn_v (slice c i len)) / pow2 (64 * i);
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice c 0 i)) (pow2 (64 * i)) (bn_v (slice c i len)) }
    bn_v (slice c 0 i) / pow2 (64 * i) + bn_v (slice c i len);
    (==) { bn_eval_bound (slice c 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice c 0 i)) (pow2 (64 * i)) }
    bn_v (slice c i len);
  };
  assert (bn_v (slice c i len) == bn_v c / pow2 (64 * i))

let bn_sub_mask #len n a =
  let mask = BSeq.seq_eq_mask n a len in
  let mod_mask = map (logand mask) n in
  let c, res = Hacl.Spec.Bignum.Addition.bn_sub a mod_mask in
  res

let bn_sub_mask_lemma #len n a =
  let mask = Lib.ByteSequence.seq_eq_mask n a len in
  assert (n == a ==> v mask == v (ones U64 SEC));
  assert (n =!= a ==> v mask == v (zeros U64 SEC));
  let mod_mask = map (logand mask) n in
  assert (forall (i:nat{i < len}). mod_mask.[i] == (mask &. n.[i]));
  assume (bn_v mod_mask == (if bn_v a = bn_v n then bn_v n else 0));

  let c, res = Hacl.Spec.Bignum.Addition.bn_sub a mod_mask in
  Hacl.Spec.Bignum.Addition.bn_sub_lemma a mod_mask;
  assert (bn_v res - v c * pow2 (64 * len) == bn_v a - bn_v mod_mask);
  bn_eval_bound res len;
  assert (bn_v res == bn_v a - bn_v mod_mask)


[@CInline]
let bn_is_bit_set #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  let tmp = (tmp >>. size j) &. u64 1 in
  eq_u64 tmp (u64 1)


let bn_is_bit_set_lemma #len b ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp1 = b.[i] >>. size j in
  let tmp2 = tmp1 &. u64 1 in
  mod_mask_lemma tmp1 1ul;
  assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1));

  calc (==) {
    v tmp2;
    (==) { bn_eval_index b i }
    (bn_v b / pow2 (64 * i) % pow2 64) / pow2 j % 2;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b / pow2 (64 * i)) j 64 }
    (bn_v b / pow2 (64 * i) / pow2 j) % pow2 (64 - j) % 2;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v b / pow2 (64 * i) / pow2 j) 1 (64 - j) }
    (bn_v b / pow2 (64 * i) / pow2 j) % 2;
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v b) (pow2 (64 * i)) (pow2 j) }
    (bn_v b / (pow2 (64 * i) * pow2 j)) % 2;
    (==) { Math.Lemmas.pow2_plus (64 * i) j }
    bn_v b / pow2 (64 * i + j) % 2;
    (==) { Math.Lemmas.euclidean_div_axiom ind 64 }
    bn_v b / pow2 ind % 2;
  };
  assert (v tmp2 == bn_v b / pow2 ind % 2)

[@CInline]
let bn_bit_set #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let inp = input.[i] <- input.[i] |. (u64 1 <<. size j) in
  inp


val bn_bit_set_lemma_aux: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a + b * pow2 c < pow2 (c + d) /\ a < pow2 c)
  (ensures  b < pow2 d)
let bn_bit_set_lemma_aux a b c d =
  Math.Lemmas.lemma_div_lt_nat (a + b * pow2 c) (c + d) c;
  assert ((a + b * pow2 c) / pow2 c < pow2 d);
  Math.Lemmas.lemma_div_plus a b (pow2 c);
  assert (a / pow2 c + b < pow2 d);
  Math.Lemmas.small_division_lemma_1 a (pow2 c)


let bn_bit_set_lemma #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  Math.Lemmas.euclidean_division_definition ind 64;
  assert (bn_v input < pow2 (i * 64 + j));
  Math.Lemmas.pow2_lt_compat (i * 64 + 64) (i * 64 + j);
  bn_eval_split_i #len input (i + 1);
  assert (bn_v input == bn_v (slice input 0 (i + 1)));
  bn_eval_split_i #(i + 1) (slice input 0 (i + 1)) i;
  //Seq.Properties.slice_slice input 0 (i + 1) 0 i;
  //Seq.Properties.slice_slice input 0 (i + 1) i (i + 1);
  assert (bn_v input == bn_v (slice input 0 i) + pow2 (i * 64) * bn_v (slice input i (i + 1)));
  bn_eval_unfold_i #1 (slice input i (i + 1)) 1;
  bn_eval0 #1 (slice input i (i + 1));
  assert (bn_v input == bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i]);
  bn_eval_bound #i (slice input 0 i) i;
  bn_bit_set_lemma_aux (bn_v (slice input 0 i)) (v input.[i]) (i * 64) j;
  assert (v input.[i] < pow2 j);

  let b = u64 1 <<. size j in
  let inp = input.[i] <- input.[i] |. b in
  FStar.Math.Lemmas.pow2_lt_compat 64 j;
  FStar.Math.Lemmas.modulo_lemma (pow2 j) (pow2 64);
  assert (v b == pow2 j);
  logor_disjoint (input.[i]) b j;
  assert (v inp.[i] == v input.[i] + v b);

  calc (==) {
    bn_v inp;
    (==) { bn_eval_split_i #len inp (i + 1) }
    bn_v (slice inp 0 (i + 1));
    (==) { bn_eval_split_i #(i + 1) (slice inp 0 (i + 1)) i }
    bn_v (slice inp 0 i) + pow2 (i * 64) * bn_v (slice inp i (i + 1));
    (==) { bn_eval_unfold_i #1 (slice inp i (i + 1)) 1; bn_eval0 #1 (slice inp i (i + 1)) }
    bn_v (slice inp 0 i) + pow2 (i * 64) * v inp.[i];
    (==) { bn_eval_extensionality_j input inp i }
    bn_v (slice input 0 i) + pow2 (i * 64) * v inp.[i];
    (==) { }
    bn_v (slice input 0 i) + pow2 (i * 64) * (v input.[i] + v b);
    (==) { Math.Lemmas.distributivity_add_right (pow2 (i * 64)) (v input.[i]) (v b) }
    bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i] + pow2 (i * 64) * v b;
    (==) { Math.Lemmas.pow2_plus (i * 64) j; Math.Lemmas.euclidean_division_definition ind 64 }
    bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i] + pow2 ind;
    (==) { }
    bn_v input + pow2 ind;
  }


let bn_from_bytes_be len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be len b

let bn_from_bytes_be_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma len b

let bn_to_bytes_be len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be len b

let bn_to_bytes_be_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma len b
