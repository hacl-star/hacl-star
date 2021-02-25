module Lib.UpdateMulti

/// This module defines a generic update_multi combinator, used in various
/// places, including hashes and the streaming functor. See
/// Lib.UpdateMulti.Lemmas for an equivalence between update_multi and the
/// Lib-style repeat combinators.

module S = FStar.Seq

open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let uint8 = Lib.IntTypes.uint8

/// Specification
/// =============

/// Helpers that deal with the modulo proof obligation to make things go
/// smoothly. Originally in Spec.Agile.Hash, now generic, with a much more
/// robust proof.

/// The first helpers help to reason about splitting data at ad-hoc number of blocks.

/// First, reason about the lengths
#push-options "--z3cliopt smt.arith.nl=false"
let split_nb_lem (block_length: pos)
  (data_length: nat)
  (n: nat):
  Lemma
    (requires
      n <= data_length / block_length)
    (ensures (
      0 <= n * block_length /\
      n * block_length <= data_length /\
      n * block_length % block_length = 0 /\
      (data_length - n * block_length) % block_length = data_length % block_length)) =
  let bl = n * block_length in
  Math.Lemmas.nat_times_nat_is_nat n block_length;
  Math.Lemmas.nat_over_pos_is_nat bl block_length;
  assert(bl >= 0);
  assert(bl / block_length >= 0);
  Math.Lemmas.multiple_modulo_lemma n block_length;
  assert(bl % block_length = 0);
  calc (<=) {
     bl;
  (<=) { Math.Lemmas.lemma_mult_le_right block_length n (data_length / block_length) }
    (data_length / block_length) * block_length;
  (<=) {}
    (data_length / block_length) * block_length + data_length % block_length;
  (==) { Math.Lemmas.euclidean_division_definition data_length block_length }
    data_length;
  };
  let r = data_length - bl in
  calc (==) {
    r % block_length;
  (==) { Math.Lemmas.modulo_distributivity data_length (- bl) block_length }
    (data_length % block_length + (- bl) % block_length) % block_length;
  (==) { Math.Lemmas.paren_mul_right (-1) n block_length }
    (data_length % block_length + ((- n) * block_length) % block_length) % block_length;
  (==) { Math.Lemmas.multiple_modulo_lemma (-n) block_length }
    (data_length % block_length) % block_length;
  (==) { Math.Lemmas.lemma_mod_add_distr 0 data_length block_length }
    data_length % block_length;
  }
#pop-options

/// The helper which actually splits sequences - TODO: rename
#push-options "--z3cliopt smt.arith.nl=false"
let split_block
  (block_length: pos)
  (data: S.seq uint8)
  (n: nat):
  Pure (S.seq uint8 & S.seq uint8)
    (requires
      n <= S.length data / block_length)
    (ensures fun (l, r) ->
      0 <= n * block_length /\
      n * block_length <= S.length data /\
      S.length l % block_length = 0 /\
      (S.length r % block_length = S.length data % block_length) /\
      l == fst (Seq.split data (FStar.Mul.(n * block_length))) /\
      r == snd (Seq.split data (FStar.Mul.(n * block_length))) /\
      S.append l r == data)
=
  split_nb_lem block_length (Seq.length data) n;
  let l, r = S.split data FStar.Mul.(n * block_length) in
  S.lemma_eq_intro (l `S.append` r) data;
  assert(S.length l = n * block_length);
  assert(S.length r = S.length data - n * block_length);
  assert (l == fst (Seq.split data (FStar.Mul.(n * block_length))));
  assert (r == snd (Seq.split data (FStar.Mul.(n * block_length))));
  assert (S.append l r == data);
  l, r
#pop-options

/// We now define more specific split functions, to split data between a
/// sequence of blocks and a remainder (strictly) smaller than a block.

/// First version: the remainder is strictly smaller than a block
#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_nb_rem
  (block_length: pos)
  (data_length: nat) :
  Pure (nat & nat)
    (requires True)
    (ensures fun (n, rem) ->
        0 <= n * block_length /\
        n * block_length <= data_length /\
        n * block_length % block_length = 0 /\
        (rem % block_length = data_length % block_length) /\
        n = data_length / block_length /\
        rem = data_length % block_length /\
        0 <= rem /\ rem < block_length /\
        data_length = n * block_length + rem) =
  let n = data_length / block_length in
  let rem = data_length % block_length in
  Math.Lemmas.nat_over_pos_is_nat data_length block_length;
  split_nb_lem block_length data_length n;
  Math.Lemmas.euclidean_division_definition data_length block_length;
  n, rem
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last
  (block_length: pos)
  (data: S.seq uint8) :
  Pure (S.seq uint8 & S.seq uint8)
    (requires True)
    (ensures fun (l, r) ->
      S.length l % block_length = 0 /\
      (S.length data % block_length = 0 ==> S.length r % block_length = 0) /\
      Seq.length r = Seq.length data % block_length /\
      0 <= Seq.length r /\ Seq.length r < block_length /\
      Seq.length data = Seq.length l + Seq.length r /\
      S.append l r == data) =
 let n, rem = split_at_last_nb_rem block_length (Seq.length data) in
 let l, r = split_block block_length data n in
 l, r
#pop-options

/// Second version: the remainder is smaller or equal to a block. We call this
/// version "lazy" because it is used to differ the processing of the last full
/// block in the hash implementations (incremental, streaming...).

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_lazy_nb_rem
  (l: pos)
  (d: nat) :
  Pure (nat & nat)
    (requires True)
    (ensures (fun (n, rem) ->
      let blocks = n * l in
      rem <= l /\
      (rem % l = d % l) /\
      (rem =  d % l \/  rem = l) /\
      (rem = 0 <==> d == 0) /\
      (rem = l <==> (blocks = (d / l - 1) * l)) /\
      ((rem > 0 /\ rem < l) <==>  d % l <> 0) /\
      (rem = (d % l) <==> (blocks = (d / l) * l)) /\
       blocks % l = 0 /\
      (blocks / l) * l = blocks
  )) =
  let n, rem = split_at_last_nb_rem l d in
  (**) let blocks = n * l in
  (**) Math.Lemmas.euclidean_division_definition blocks l;
  (**) assert((blocks / l) * l = blocks);
  (**) Math.Lemmas.distributivity_sub_left (d / l) 1 l;
  (**) assert((d / l - 1) * l = (d / l) * l - l);
  if n > 0 && rem = 0 then
    begin
    let n' = n - 1 in
    (**) let blocks' = n' * l in
    let rem' = d - blocks' in
    (**) assert(rem = 0);
    (**) assert(blocks' = blocks - l);
    (**) assert(rem' = l);
    (**) Math.Lemmas.nat_times_nat_is_nat n' l;
    (**) assert(n' * l >= 0);
    (**) assert(d > 0);
    (**) Math.Lemmas.lemma_mod_sub_distr blocks l l;
    (**) assert(l % l = 0);
    (**) assert(blocks' % l = 0);
    (**) Math.Lemmas.euclidean_division_definition blocks' l;
    (**) assert((blocks' / l) * l = blocks');
    n', rem'
    end
  else
    begin
    (* Proof interlude *)
    (**) begin
    (**) assert(d % l <> 0 || n = 0);
    (**) if d % l <> 0 then
    (**)   begin
    (**)        assert(rem <> 0);
    (**)        Math.Lemmas.nat_times_nat_is_nat n l;
    (**)        assert(n * l >= 0)
    (**)   end
    (**) else
    (**)   begin
    (**)        assert(n = 0);
    (**)        assert(d = n * l + rem);
    (**)   Math.Lemmas.mul_zero_left_is_zero l;
    (**)        assert(n * l = 0);
    (**)        assert(d = rem)
    (**)   end
    (**) end;
    n, rem
    end
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_lazy
  (l: pos)
  (b: S.seq uint8) :
  Pure (S.seq uint8 & S.seq uint8)
    (requires True)
    (ensures (fun (blocks, rest) ->
      S.length rest <= l /\
      (S.length rest % l = S.length b % l) /\
      (S.length rest = S.length b % l \/ S.length rest = l) /\
      (S.length rest = 0 <==> S.length b == 0) /\
      (S.length rest = l <==>
        (S.length blocks = (S.length b / l - 1) * l)) /\
      ((S.length rest > 0 /\ S.length rest < l) <==> S.length b % l <> 0) /\
      (S.length rest = (S.length b % l) <==>
        (S.length blocks = (S.length b / l) * l)) /\
      S.equal (S.append blocks rest) b /\
      S.length blocks % l = 0 /\
      (S.length blocks / l) * l = S.length blocks))
=
  let n, rem = split_at_last_lazy_nb_rem l (Seq.length b) in
  Math.Lemmas.nat_times_nat_is_nat n l;
  let blocks, rest = S.split b (n * l) in
  blocks, rest
#pop-options

let update_t a block_length =
  a -> b:S.seq uint8 { S.length b = block_length } -> a

let rec mk_update_multi #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a)
  (blocks: S.seq uint8): Pure a
  (requires
    S.length blocks % block_length = 0)
  (ensures fun _ ->
    True)
  (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    acc
  else
    let block, rem = split_block block_length blocks 1 in
    let acc = update acc block in
    mk_update_multi block_length update acc rem

let update_full #a
  (block_length:pos)
  (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a)
  (update_last: a -> (s:S.seq uint8 { S.length s < block_length }) -> a)
  (acc: a)
  (input: S.seq uint8)
=
//  let n_blocks = S.length input / block_length in
//  let rem = S.length input % block_length in
//  let blocks, rest = S.split input (n_blocks * block_length) in
  let blocks, rest = split_at_last block_length input in
//  assert (S.length rest = S.length input % block_length);
//  Math.Lemmas.multiple_modulo_lemma n_blocks block_length;
//  assert (S.length blocks % block_length = 0);
//  assert (S.length rest < block_length);
  update_last (mk_update_multi block_length update acc blocks) rest

/// Same as [update_full] but we make sure the last block is not empty in order
/// to mimic the behavior of the streaming API where we lazily process the internal
/// block. Note that the length condition on update_last is not the same.
#push-options "--z3rlimit 100"
let update_full_lazy #a
  (block_length:pos)
  (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a)
  (update_last: a -> (s:S.seq uint8 { S.length s <= block_length }) -> a)
  (acc: a)
  (input: S.seq uint8)
=
//  let n_blocks = S.length input / block_length in
//  let rem = S.length input % block_length in
//  let n_blocks, rem = if rem = 0 && n_blocks > 0 then n_blocks - 1, block_length
//                                                 else n_blocks, rem in
//  let blocks, rest = S.split input (n_blocks * block_length) in
  let blocks, rest = split_at_last_lazy block_length input in
//  assert (S.length rest % block_length = S.length input % block_length);
//  Math.Lemmas.multiple_modulo_lemma n_blocks block_length;
//  assert (S.length blocks % block_length = 0);
//  assert (S.length rest <= block_length);
  update_last (mk_update_multi block_length update acc blocks) rest
#pop-options

/// Lemmas
/// ======

#push-options "--z3cliopt smt.arith.nl=false"
let concat_blocks_modulo (block_len: pos) (s1 s2: S.seq uint8): Lemma
  (requires
    S.length s1 % block_len = 0 /\
    S.length s2 % block_len = 0)
  (ensures
    S.length (S.append s1 s2) % block_len = 0)
=
  let input = S.append s1 s2 in
  let input1 = s1 in
  let input2 = s2 in
  calc (==) {
    S.length input % block_len;
  (==) { S.lemma_len_append input1 input2 }
    (S.length input1 + S.length input2) % block_len;
  (==) {
    FStar.Math.Lemmas.modulo_distributivity (S.length input1) (S.length input2) (block_len)
  }
    (S.length input1 % block_len + S.length input2 % block_len) % block_len;
  (==) { (* hyp *) }
    0 % block_len;
  (==) { FStar.Math.Lemmas.small_mod 0 block_len }
    0;
  }
#pop-options

#push-options "--fuel 1"
let update_multi_zero #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a):
  Lemma
    (ensures (mk_update_multi block_length update acc S.empty == acc))
=
  ()
#pop-options

#push-options "--fuel 1 --z3rlimit 50"
let rec update_multi_associative #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a)
  (input1 input2: S.seq uint8):
  Lemma
    (requires
      S.length input1 % block_length == 0 /\
      S.length input2 % block_length == 0)
    (ensures (
      let input = S.append input1 input2 in
      S.length input % block_length == 0 /\
      mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2 ==
        mk_update_multi block_length update acc input))
    (decreases (
      S.length input1 + S.length input2))
=
  let input = S.append input1 input2 in
  concat_blocks_modulo block_length input1 input2;
  if S.length input1 = 0 then
    calc (==) {
      mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2;
    (==) { update_multi_zero block_length update acc }
      mk_update_multi block_length update acc input2;
    (==) { S.lemma_eq_intro input2 (S.empty `S.append` input2) }
      mk_update_multi block_length update acc (S.empty `S.append` input2);
    (==) { S.lemma_eq_intro input1 S.empty }
      mk_update_multi block_length update acc (input1 `S.append` input2);
    }
  else
    let input1_hd, input1_tl = split_block block_length input1 1 in
    S.lemma_eq_intro input1 (input1_hd `S.append` input1_tl);
    update_multi_associative block_length update (update acc input1_hd) input1_tl input2;
    let s = input1_hd `S.append` (input1_tl `S.append` input2) in
    S.lemma_eq_intro (fst (S.split s (1 * block_length))) input1_hd;
    S.lemma_eq_intro (snd (S.split s (1 * block_length))) (input1_tl `S.append` input2);
    S.lemma_eq_intro (input1_hd `S.append` (input1_tl `S.append` input2)) input

#pop-options
