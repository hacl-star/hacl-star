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


let bn_from_bytes_be len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be len b

let bn_from_bytes_be_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma len b

let bn_to_bytes_be len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be len b

let bn_to_bytes_be_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma len b
