module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

module B2 = Spec.Blake2

friend Spec.Agile.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let rec repeati_ext (#a:Type) (n:nat) (f1 f2:(i:nat{i < n} -> a -> a)) (acc0:a) (i:nat{i <= n})
  : Lemma
    (requires forall (i:nat{i < n}) (acc:a). f1 i acc == f2 i acc)
    (ensures Lib.LoopCombinators.repeati i f1 acc0 == Lib.LoopCombinators.repeati i f2 acc0)
    (decreases i)
  = let open Lib.LoopCombinators in
    if i = 0 then (
      eq_repeati0 n f1 acc0;
      eq_repeati0 n f2 acc0
    ) else (
      unfold_repeati n f1 acc0 (i-1);
      unfold_repeati n f2 acc0 (i-1);
      repeati_ext n f1 f2 acc0 (i-1)
    )

let rec lemma_update_multi_core_blake_snd
  (a:hash_alg{is_blake a})
  (blocks:bytes{Seq.length blocks <= maxint U64})
  (nb:nat)
  (h:words_state a)
  : Lemma
    (requires snd h == u64 0 /\ Seq.length blocks == nb * block_length a)
    (ensures snd (Spec.Agile.Hash.update_multi a h blocks) == u64 (S.length blocks))
    (decreases nb)
  = if nb = 0 then (
       assert (S.equal blocks S.empty);
       update_multi_zero a h
    ) else (
      let nb' = nb - 1 in
      let blocks' = S.slice blocks 0 (nb' * block_length a) in
      let last = S.slice blocks (nb' * block_length a) (S.length blocks) in
      let h_inter = update_multi a h blocks' in
      let h_f = update_multi a h blocks in

      calc (==) {
        v #U64 #SEC (snd h_f);
        (==) {
          update_multi_associative a h blocks' last;
          assert (S.equal (blocks' `S.append` last) blocks);
          lemma_update_multi_core_blake_snd a blocks' nb' h;
          update_multi_update a h_inter last  }
        v (u64 (S.length blocks') +. u64 (block_length a));
        (==) { }
        (S.length blocks' + block_length a) % pow2 64;
        (==) { FStar.Math.Lemmas.small_mod (S.length blocks' + block_length a) (pow2 64) }
        S.length blocks' + block_length a;
        (==) { }
        S.length blocks;
      };
      v_injective #U64 #SEC (snd h_f)
    )

let rec lemma_update_multi_core_blake
  (a:hash_alg{is_blake a})
  (blocks:bytes{Seq.length blocks <= max_input_length a})
  (nb:nat)
  (h:words_state a)
  : Lemma
    (requires snd h == u64 0 /\ Seq.length blocks == nb * block_length a)
    (ensures fst (Spec.Agile.Hash.update_multi a h blocks) ==
             Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 blocks) (fst h))
    (decreases nb)
  = let n = S.length blocks / block_length a in
    let f = B2.blake2_update1 (to_blake_alg a) 0 blocks in
    let open Lib.LoopCombinators in
    if nb = 0 then (
       admit()
       // eq_repeati0 n f (fst h);
       // assert (repeati nb f (fst h) == fst h);

       // let h_f = fst (Spec.Agile.Hash.update_multi a h blocks) in
       // assert (blocks `S.equal` S.empty);
       // update_multi_zero a h;
       // assert (h_f == fst h)
    ) else (
      admit()
      // let h_fr = repeati nb (B2.blake2_update1 (to_blake_alg a) 0 blocks) (fst h) in

      // let n' = nb - 1 in
      // let blocks' = S.slice blocks 0 (n' * block_length a) in
      // let last = S.slice blocks (n' * block_length a) (S.length blocks) in
      // update_multi_associative a h blocks' last;
      // let h_f = Spec.Agile.Hash.update_multi a h blocks in
      // let h_inter = update_multi a h blocks' in
      // assert (S.equal (S.append blocks' last) blocks);
      // assert (h_f == update_multi a h_inter last);
      // let f' = B2.blake2_update1 (to_blake_alg a) 0 blocks' in
      // lemma_update_multi_core_blake a blocks' n' h;
      // assert (fst h_inter == repeati n' (B2.blake2_update1 (to_blake_alg a) 0 blocks') (fst h));


      // unfold_repeati n f (fst h) (nb - 1);
      // assert (h_fr == f (nb-1) (repeati (nb-1) f (fst h)));
      // assume (h_fr == f (nb-1) (repeati n' f' (fst h)));

      // admit()
    )



#push-options "--z3rlimit 100"

let lemma_blake2_split
  (a:hash_alg{is_blake a})
  (d:bytes{Seq.length d <= max_input_length a})
  (h:words_state a)
  : Lemma
    (let (nb, rem) = B2.split (to_blake_alg a) (Seq.length d) in
     let blocks = Seq.slice d 0 (nb * block_length a) in
     Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 d) (fst h) ==
     Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 blocks) (fst h))
  = let (nb, rem) = B2.split (to_blake_alg a) (Seq.length d) in
    let blocks = Seq.slice d 0 (nb * block_length a) in
    let n = S.length blocks / block_length a in
    let f1 = B2.blake2_update1 (to_blake_alg a) 0 d in
    let f2 = B2.blake2_update1 (to_blake_alg a) 0 blocks in
    repeati_ext n f1 f2 (fst h) nb

#pop-options

let lemma_small_last_split (a:hash_alg{is_blake a}) (input:bytes)
  : Lemma
    (requires S.length input <= block_length a)
    (ensures (let bs, l, rem = last_split_blake a input in
              bs `S.equal` S.empty /\
              S.equal l (B2.get_last_padded_block (to_blake_alg a) input rem) /\
              rem == S.length input))
  = let bs, l, rem = last_split_blake a input in
    if S.length input = block_length a then ()
    else FStar.Math.Lemmas.small_div (S.length input) (block_length a)

let update_last_blake_aux (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= maxint U64}) :
  Tot (words_state a)
  = let blocks, last_block, rem = last_split_blake a input in
    let h' = update_multi a hash blocks in
    let h_f = Spec.Blake2.blake2_update_block (to_blake_alg a) true (prevlen + S.length input) last_block (fst h') in
    (h_f, u64 0)

let lemma_update_last_aux (a:hash_alg{is_blake a})
  (s:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= maxint U64}) :
  Lemma
    (requires v #U64 #SEC (snd s) == prevlen /\
      // Not necessary, but simplifies proof, and all we need here
      S.length input <= block_length a)
    (ensures
      update_last_blake a s prevlen input == update_last_blake_aux a s prevlen input)
  = let b, l, r = last_split_blake a input in

    FStar.Math.Lemmas.small_mod (prevlen + S.length input) (pow2 64)

let lemma_last_padded_block (a:hash_alg{is_blake a}) (blocks l:bytes)
  (rem:nat{rem <= S.length l /\ rem <= block_length a})
  : Lemma
    (requires S.length blocks % block_length a == 0 /\ rem == S.length l)
    (ensures B2.get_last_padded_block (to_blake_alg a) l rem `S.equal`
             B2.get_last_padded_block (to_blake_alg a) (blocks `S.append` l) rem)
  = let m = blocks `S.append` l in
    let last_m = Seq.slice m (S.length m - rem) (S.length m) in
    assert (last_m `S.equal` l)

let lemma_update_last_blake2
  (a:hash_alg{is_blake a})
  (rem:nat)
  (d:bytes)
  (s:words_state a)
  : Lemma
    (requires rem <= block_length a /\ rem <= S.length d /\ S.length d <= maxint U64 /\
      (let bs, l = split_blocks a d in
       rem == S.length l /\ v #U64 #SEC (snd s) == S.length bs)
    )
    (ensures
      (let bs, l = split_blocks a d in
      B2.blake2_update_last (to_blake_alg a) 0 rem d (fst s) ==
      fst (update_last_blake a s (S.length bs) l))
    )
  = let bs, l = split_blocks a d in

    lemma_small_last_split a l;

    lemma_update_last_aux a s (S.length bs) l;

    let h_ag = B2.blake2_update_last (to_blake_alg a) 0 rem d (fst s) in

    let last_b = B2.get_last_padded_block (to_blake_alg a) d rem in
    assert (B2.blake2_update_last (to_blake_alg a) 0 rem d (fst s) ==
      B2.blake2_update_block (to_blake_alg a) true (S.length d) last_b (fst s));

    let blocks, last_block, r = last_split_blake a l in
    lemma_last_padded_block a bs l rem;

    let s' = update_multi a s blocks in

    update_multi_zero a s

let lemma_hash_incremental_body_blake2
  (a:hash_alg{is_blake a})
  (d:bytes{Seq.length d <= maxint U64})
  (s:words_state a)
  : Lemma
    (requires (snd s) == u64 0)
    (ensures (
      fst (hash_incremental_body a d s) ==
      B2.blake2_update_blocks (to_blake_alg a) 0 d (fst s)))
  = let open Lib.LoopCombinators in
    let bs, l = split_blocks a d in
    let (nb, rem) = B2.split (to_blake_alg a) (Seq.length d) in
    assert (rem == Seq.length l);
    assert (nb * block_length a + rem == Seq.length d);
    let blocks = Seq.slice d 0 (nb * block_length a) in
    let rest = Seq.slice d (nb * block_length a) (Seq.length d) in
    let s_ag1 = update_multi a s bs in
    let s_b1 = repeati nb (B2.blake2_update1 (to_blake_alg a) 0 d) (fst s) in
    lemma_update_multi_core_blake a bs nb s;
    lemma_update_multi_core_blake_snd a bs nb s;
    lemma_blake2_split a d s;

    lemma_update_last_blake2 a rem d s_ag1

let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (d:bytes{Seq.length d <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) d 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)) ==
     hash_incremental a d)
  = admit()
    // TODO: max_input_length should be pow2 64 for both blake
    //lemma_hash_incremental_body_blake2 a d (init a)

let md_is_hash_incremental
  (a:hash_alg{not (is_blake a)})
  (input: bytes { S.length input <= max_input_length a })
  (s:words_state a)
  : Lemma (
      let blocks, rest = split_blocks a input in
      update_multi a s (input `S.append` (pad a (S.length input))) ==
      update_last a (update_multi a s blocks) (S.length blocks) rest)
   = let blocks, rest = split_blocks a input in
     assert (S.length input == S.length blocks + S.length rest);
     let padding = pad a (S.length input) in
     calc (==) {
       update_last a (update_multi a s blocks) (S.length blocks) rest;
       (==) { }
       update_multi a (update_multi a s blocks) S.(rest @| padding);
       (==) { update_multi_associative a s blocks S.(rest @| padding) }
       update_multi a s S.(blocks @| (rest @| padding));
       (==) { S.append_assoc blocks rest padding }
       update_multi a s S.((blocks @| rest) @| padding);
       (==) { }
       update_multi a s S.(input @| padding);
     }

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
=
  if is_blake a then (blake2_is_hash_incremental a input)
  else md_is_hash_incremental a input (init a)
