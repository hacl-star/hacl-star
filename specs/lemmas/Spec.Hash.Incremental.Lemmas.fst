module Spec.Hash.Incremental.Lemmas

open Spec.Agile.Hash
open Spec.Hash.PadFinish

open FStar.Mul
open Lib.IntTypes

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let lemma_split_blocks_assoc (a:hash_alg) (s1 s2:bytes)
  : Lemma
      (requires
        S.length s1 + S.length s2 <= max_input_length a /\
        S.length s1 % block_length a == 0 /\ S.length s2 > 0)
      (ensures (
        let b1, l1 = split_blocks a (s1 `S.append` s2) in
        let b2, l2 = split_blocks a s2 in
        b1 == s1 `S.append` b2 /\ l1 == l2))
  = let s = s1 `S.append` s2 in
    let n_s1 = S.length s1 / block_length a in

    let n1 = S.length s / block_length a in
    let n2 = S.length s2 / block_length a in

    Math.Lemmas.division_addition_lemma (S.length s2) (block_length a) n_s1;
    assert (n1 == n2 + n_s1);

    let n1' = if S.length s % block_length a = 0 then n1-1 else n1 in
    let n2' = if S.length s2 % block_length a = 0 then n2-1 else n2 in

    let bs1, ls1 = S.split s (n1' * block_length a) in
    let bs2, ls2 = S.split s2 (n2' * block_length a) in
    assert (n1' * block_length a == n2' * block_length a + S.length s1);
    assert (S.equal ls1 ls2);
    assert (S.equal bs1 (s1 `S.append` bs2))

let lemma_split_blake_modulo (a:hash_alg{is_blake a}) (s1 s2:bytes)
  : Lemma
      (requires S.length s1 + S.length s2 <= max_input_length a /\
        S.length s1 % block_length a == 0 /\ S.length s2 > 0)
      (ensures (
        let b1, l1, rem1 = last_split_blake a (s1 `S.append` s2) in
        let b2, l2, rem2 = last_split_blake a s2 in
        l1 == l2 /\ rem1 == rem2)
      )
   = lemma_split_blocks_assoc a s1 s2

let compose_split_blocks (a:hash_alg{is_blake a}) (inp1:bytes) (inp2:bytes)
  : Lemma
    (requires S.length inp1 % block_length a == 0 /\
      S.length inp2 > 0 /\
      S.length inp1 + S.length inp2 <= max_input_length a)
    (ensures (
      let input = inp1 `Seq.append` inp2 in
      let bs, l = split_blocks a input in
      let _, last, _ = last_split_blake a l in
      let blocks2, last2, rem2 = last_split_blake a inp2 in
      last == last2 /\
      bs == inp1 `S.append` blocks2 /\
      rem2 == S.length l))
  = let input = inp1 `Seq.append` inp2 in
    let bs, l = split_blocks a input in
    let _, last, _ = last_split_blake a l in
    let blocks2, last2, rem2 = last_split_blake a inp2 in
    lemma_split_blocks_assoc a inp1 inp2;
    let b2, _ = split_blocks a inp2 in
    lemma_split_blake_modulo a b2 l

let concatenated_hash_incremental_blake_aux (a:hash_alg{is_blake a})
  (inp1:bytes) (inp2:bytes)
  (h:words_state a)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\
      Seq.length inp1 % block_length a == 0 /\ Seq.length inp2 > 0)
    (ensures (
      let input = inp1 `S.append` inp2 in
      let bs, l = split_blocks a input in
      fst (update_last_blake a (update_multi a h bs) (S.length bs) l) ==
      fst (update_last_blake a (update_multi a h inp1) (S.length inp1) inp2)))
  = let input = inp1 `S.append` inp2 in
    let bs, l = split_blocks a input in
    let blocks2, last2, rem2 = last_split_blake a inp2 in
    let h' = update_multi a (update_multi a h inp1) blocks2 in
    let h_f = update_last_blake a h' (S.length bs) l in

    let h_f2 = Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem2))
      last2 (fst h') in

    let _, last, _ = last_split_blake a l in
    compose_split_blocks a inp1 inp2;

    Spec.Hash.Lemmas.update_multi_associative a h inp1 blocks2;
    assert (h' == update_multi a h bs)


let concatenated_hash_incremental_blake (a:hash_alg{is_blake a}) (inp1:bytes) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\
      Seq.length inp1 % block_length a == 0 /\ Seq.length inp2 > 0)
    (ensures finish a (update_last_blake a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
  = let open FStar.Mul in
    let h = init a in
    concatenated_hash_incremental_blake_aux a inp1 inp2 h

#push-options "--z3rlimit 100"

let concatenated_hash_incremental_md (a:hash_alg{is_md a}) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
  = admit();
    allow_inversion hash_alg;
    let len = S.length inp2 in
    calc (S.equal) {
    finish a (update_last a (update_multi a (init a) inp1)
        (S.length inp1) inp2);
    (S.equal) { }
      finish a (update_multi a (update_multi a (init a) inp1)
        (S.append inp2 (pad a (S.length inp1 + len))));
    (S.equal) { }
      finish a (update_multi a (init a)
        (S.append inp1
          (S.append inp2 (pad a (S.length inp1 + len)))));
    (S.equal) { S.append_assoc
      inp1
      inp2
      (pad a (S.length inp1 + len))
    }
      finish a (update_multi a (init a)
        (S.append (S.append inp1 inp2)
          (pad a (S.length inp1 + len))));
    (==) { }
      Spec.Agile.Hash.hash a (S.append inp1 inp2);
    };
    hash_is_hash_incremental a (S.append inp1 inp2)

#pop-options

let concatenated_hash_incremental (a:hash_alg) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\ Seq.length inp2 > 0)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
   = if is_blake a then concatenated_hash_incremental_blake a inp1 inp2
     else concatenated_hash_incremental_md a inp1 inp2
