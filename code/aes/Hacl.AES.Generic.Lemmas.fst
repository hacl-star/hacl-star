module Hacl.AES.Generic.Lemmas

open Lib.ByteSequence
open Lib.Sequence
open Lib.IntVector

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

val lemma_uints_to_bytes_be_sub :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  #len:size_nat{len * numbytes t < pow2 32} ->
  s : lseq (uint_t t l) len ->
  i : size_nat {i < len} ->
  Lemma(sub (uints_to_bytes_be #t #l s) (i * numbytes t) (numbytes t) == uint_to_bytes_be (index s i))

let lemma_uints_to_bytes_be_sub #t #l #len s i =
  let lemma_uints_to_bytes_be_i_j (j : size_nat {j < numbytes t}):
      Lemma(index (uints_to_bytes_be #t #l s) (i * numbytes t + j) == index (uint_to_bytes_be (index s i)) j) =
        index_uints_to_bytes_be #t #l #len s (i*numbytes t + j);
        assert (index (uints_to_bytes_be #t #l s) (i*numbytes t + j) ==
                index (uint_to_bytes_be (index s i)) j) in

  Classical.forall_intro lemma_uints_to_bytes_be_i_j;
  eq_intro (sub (uints_to_bytes_be #t #l s) (i * numbytes t) (numbytes t)) (uint_to_bytes_be (index s i))

val key_to_bytes_ni_lemma:
  m:m_spec{m == MAES}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a-1) * v (klen m))
  -> i:nat{i < (num_rounds a-1)} ->
  Lemma (sub (keys_to_bytes m a b) (i*16) 16 == key_to_bytes m (sub b (i * v (klen m)) (v (klen m))))

let key_to_bytes_ni_lemma m a b i =
  let s = map #(vec_t U128 1) #(uint_t U128 SEC) #(Spec.AES.num_rounds a-1) (fun x -> (vec_v #U128 #1 x).[0]) b in
  lemma_uints_to_bytes_be_sub s i;
  assert (sub (uints_to_bytes_be s) (i*16) 16 == uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]);
  lemma_uint_to_bytes_be_preserves_value (vec_v #U128 #1 b.[i]).[0];
  assert (nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]) == v (vec_v #U128 #1 b.[i]).[0]);
  nat_from_intseq_be_lemma0 (vec_v #U128 #1 b.[i]);
  assert (nat_from_intseq_be (vec_v #U128 #1 b.[i]) == v (vec_v #U128 #1 b.[i]).[0]);
  assert (nat_from_intseq_be (vec_v #U128 #1 b.[i]) ==
    nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]));
  assert (nat_to_bytes_be 16 (nat_from_intseq_be (vec_v #U128 #1 b.[i])) ==
    nat_to_bytes_be #SEC 16 (nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0])));
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be (vec_v #U128 #1 b.[i]));
  assert (uints_to_bytes_be #U128 #SEC #1 (nat_to_intseq_be #U128 #SEC 1 (nat_from_intseq_be (vec_v #U128 #1 b.[i]))) ==
    nat_to_intseq_be #U8 #SEC 16 (nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0])));
  lemma_nat_from_to_intseq_be_preserves_value 1 (vec_v #U128 #1 b.[i]);
  lemma_nat_from_to_intseq_be_preserves_value 16 (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]);
  assert (uints_to_bytes_be (vec_v #U128 #1 b.[i]) == uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0])

let key_to_bytes_lemma m a b i =
  match m with
  | MAES -> key_to_bytes_ni_lemma m a b i
  | M32 -> (assume (sub (keys_to_bytes m a b) (i*16) 16 == key_to_bytes m (sub b (i*(v (klen m))) (v (klen m)))))

val keyx_to_bytes_ni_lemma:
  m:m_spec{m == MAES}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a+1) * v (klen m))
  -> i:nat{i < (num_rounds a+1)} ->
  Lemma (sub (keyx_to_bytes m a b) (i*16) 16 == key_to_bytes m (sub b (i * v (klen m)) (v (klen m))))

let keyx_to_bytes_ni_lemma m a b i =
  let s = map #(vec_t U128 1) #(uint_t U128 SEC) #(Spec.AES.num_rounds a+1) (fun x -> (vec_v #U128 #1 x).[0]) b in
  lemma_uints_to_bytes_be_sub s i;
  assert (sub (uints_to_bytes_be s) (i*16) 16 == uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]);
  lemma_uint_to_bytes_be_preserves_value (vec_v #U128 #1 b.[i]).[0];
  assert (nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]) == v (vec_v #U128 #1 b.[i]).[0]);
  nat_from_intseq_be_lemma0 (vec_v #U128 #1 b.[i]);
  assert (nat_from_intseq_be (vec_v #U128 #1 b.[i]) == v (vec_v #U128 #1 b.[i]).[0]);
  assert (nat_from_intseq_be (vec_v #U128 #1 b.[i]) ==
    nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]));
  assert (nat_to_bytes_be 16 (nat_from_intseq_be (vec_v #U128 #1 b.[i])) ==
    nat_to_bytes_be #SEC 16 (nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0])));
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be (vec_v #U128 #1 b.[i]));
  assert (uints_to_bytes_be #U128 #SEC #1 (nat_to_intseq_be #U128 #SEC 1 (nat_from_intseq_be (vec_v #U128 #1 b.[i]))) ==
    nat_to_intseq_be #U8 #SEC 16 (nat_from_bytes_be (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0])));
  lemma_nat_from_to_intseq_be_preserves_value 1 (vec_v #U128 #1 b.[i]);
  lemma_nat_from_to_intseq_be_preserves_value 16 (uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0]);
  assert (uints_to_bytes_be (vec_v #U128 #1 b.[i]) == uint_to_bytes_be (vec_v #U128 #1 b.[i]).[0])

let keyx_to_bytes_lemma m a b i =
  match m with
  | MAES -> keyx_to_bytes_ni_lemma m a b i
  | M32 -> (assume (sub (keyx_to_bytes m a b) (i*16) 16 == key_to_bytes m (sub b (i*(v (klen m))) (v (klen m)))))

let keys_to_bytes_lemma m a b =
  let b_s = sub b (v (klen m)) (v (klen m) * (num_rounds a-1)) in
  let l0 = sub (keyx_to_bytes m a b) 16 ((num_rounds a-1) * 16) in
  let l1 = keys_to_bytes m a b_s in
  let lemma_key_to_bytes (i : size_nat {i < num_rounds a-1}):
    Lemma(sub l0 (i*16) 16 == sub l1 (i*16) 16) =
      assert (sub l0 (i*16) 16 == sub (keyx_to_bytes m a b) ((i+1)*16) 16);
      keyx_to_bytes_lemma m a b (i + 1);
      key_to_bytes_lemma m a b_s i in

  Classical.forall_intro lemma_key_to_bytes;
  assert (forall (i:nat{0 <= i /\ i < num_rounds a-1}).
    (forall (j:nat{0 <= j /\ j < 16}).
      (sub l0 (i*16) 16).[j] == (sub l1 (i*16) 16).[j]));
  assert (forall (i:nat{0 <= i /\ i < num_rounds a-1}).
    (forall (j:nat{0 <= j /\ j < 16}).
      l0.[(i*16) + j] == l1.[(i*16) + j]));
  assert (forall (i:nat{0 <= i /\ i < (num_rounds a-1) * 16}). i == (i / 16) * 16 + i % 16);
  assert (forall (i:nat{0 <= i /\ i < (num_rounds a-1) * 16}). l0.[i] == l1.[i]);
  eq_intro l0 l1

val keyx_zero_ni_lemma:
  m:m_spec{m == MAES}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a+1) * (v (klen m))) ->
  Lemma 
  (requires (b == Seq.create ((num_rounds a+1) * v (klen m)) (elem_zero m)))
  (ensures (keyx_to_bytes m a b == create ((num_rounds a+1) * 16) (u8 0)))

let keyx_zero_ni_lemma m a b =
  let s = map #(vec_t U128 1) #(uint_t U128 SEC) #(Spec.AES.num_rounds a+1)
    (fun x -> (vec_v #U128 #1 x).[0]) b in
  let lemma_uint_to_bytes_be_zero (i : size_nat {i < num_rounds a+1}):
      Lemma(sub (uints_to_bytes_be s) (i*16) 16 == create 16 (u8 0)) =
        lemma_uints_to_bytes_be_sub s i;
        assert (sub (uints_to_bytes_be s) (i*16) 16 == uint_to_bytes_be (mk_int #U128 #SEC 0));
        index_uint_to_bytes_be (mk_int #U128 #SEC 0);
        assert (forall (i:nat{i < 16}). (uint_to_bytes_be (mk_int #U128 #SEC 0)).[i] == u8 0);
        eq_intro (uint_to_bytes_be (mk_int #U128 #SEC 0)) (create 16 (u8 0)) in

  Classical.forall_intro lemma_uint_to_bytes_be_zero;
  let l0 = keyx_to_bytes m a b in
  let l1 = create ((num_rounds a+1) * 16) (u8 0) in
  assert (forall (i:nat{0 <= i /\ i < num_rounds a+1}).
    (forall (j:nat{0 <= j /\ j < 16}).
      (sub l0 (i*16) 16).[j] == (sub l1 (i*16) 16).[j]));
  assert (forall (i:nat{0 <= i /\ i < num_rounds a+1}).
    (forall (j:nat{0 <= j /\ j < 16}).
      l0.[(i*16) + j] == l1.[(i*16) + j]));
  assert (forall (i:nat{0 <= i /\ i < (num_rounds a+1) * 16}). i == (i / 16) * 16 + i % 16);
  assert (forall (i:nat{0 <= i /\ i < (num_rounds a+1) * 16}). l0.[i] == l1.[i]);
  eq_intro l0 l1

let keyx_zero_lemma m a b =
  match m with
  | MAES -> keyx_zero_ni_lemma m a b
  | M32 -> (assume (keyx_to_bytes m a b == create ((num_rounds a+1) * 16) (u8 0)))

let u8_16_to_le_lemma x =
  eq_intro (Hacl.AES.Common.u8_16_to_le (Hacl.AES.Common.u8_16_to_le x)) x
