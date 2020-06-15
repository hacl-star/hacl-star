module Hacl.Streaming.Spec

/// This module contains all of the logical reasoning, calc statement included,
/// for the streaming functor.
///
/// The functor uses a ghost variable (named ``seen``) to reason about the
/// **past**, i.e. whatever bytes have been fed into the streaming functor. In
/// other words, we capture the history of calls that have been performed on the
/// functor state, i.e. the sequence of bytes that have been accumulated via
/// previous calls to ``Functor.update``, into the ghost ``seen``
/// variable.
///
/// To make things useful, we need to relate the present to the past, i.e. we
/// need to relate the values of ``block_state`` and ``buf`` (in a given heap)
/// to the ghost value ``seen``.
///
/// The central invariant of the streaming functor is that, if you split
/// ``seen`` at the last block boundary, then:
///
/// - ``block_state`` contains the accumulated result of calling ``update`` on
///   all of the blocks, and
/// - ``buf`` contains the rest of ``seen`` that is smaller or equal to a complete
///   block and is processed lazily to make sure there is some data left when we
///   call ``last_update`` 
///
/// The function that performs this splitting is called ``split_at_last``, and
/// we need to prove various properties about it, since the streaming functor
/// distinguishes three sub-situations to make the proof tractable and we need
/// helper lemmas for all three situations.

#set-options "--max_fuel 0 --max_ifuel 0 \
  --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2' --z3rlimit 50"

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open Hacl.Streaming.Interface
open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

noextract
let bytes = S.seq uint8

/// A lemma I could not find in FStar.Math.Lemmas
let mul_zero_left_is_zero (n : nat) : Lemma(0 * n = 0) = ()

/// Returns the number of blocks to process
#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last_num_blocks #index (c: block index) (i: index) (b: nat):
  Pure nat
    (requires True)
    (ensures (fun n ->
      let l = U32.v (c.block_len i) in
      let blocks = n * l in
      let rest = b - blocks in
      rest <= l /\
      (rest % l = b % l) /\
      (rest =  b % l \/  rest = l) /\
      (rest = 0 <==>  b == 0) /\
      (rest = l <==> (blocks = (b / l - 1) * l)) /\
      ((rest > 0 /\ rest < l) <==>  b % l <> 0) /\
      (rest = (b % l) <==> (blocks = (b / l) * l)) /\
       blocks % l = 0 /\
      (blocks / l) * l = blocks
  ))
=
  let l = U32.v (c.block_len i) in
  let n = b / l in
  let blocks = n * l in
  let rest = b - n * l in

  (**) Math.Lemmas.nat_over_pos_is_nat b l;
  (**) assert(n >= 0);
  (**) Math.Lemmas.euclidean_division_definition b l;
  (**) Math.Lemmas.modulo_range_lemma b l;
  (**) assert(rest < l);
  (**) Math.Lemmas.modulo_lemma rest l;
  (**) assert(rest = b % l);
  (**) assert(rest = rest % l);
  (**) Math.Lemmas.cancel_mul_mod n l;
  (**) assert(blocks % l = 0);
  (**) assert(b = n * l + rest);
  (**) Math.Lemmas.euclidean_division_definition blocks l;
  (**) assert((blocks / l) * l = blocks);
  (**) assert(blocks = (b / l) * l);
  (**) Math.Lemmas.distributivity_sub_left (b / l) 1 l;
  (**) assert((b / l - 1) * l = (b / l) * l - l);

  (* We always make sure [rest] is not empty (if possible) *)
  if b % l = 0 && n > 0 then
    begin
    let n' = n - 1 in
    let blocks' = n' * l in
    let rest' = b - blocks' in

    (**) assert(rest = 0);
    (**) assert(blocks' = blocks - l);
    (**) assert(rest' = l);
    (**) Math.Lemmas.nat_times_nat_is_nat n' l;
    (**) assert(n' * l >= 0);
    (**) assert(b > 0);
    (**) Math.Lemmas.lemma_mod_sub_distr blocks l l;
    (**) assert(l % l = 0);
    (**) assert(blocks' % l = 0);
    (**) Math.Lemmas.euclidean_division_definition blocks' l;
    (**) assert((blocks' / l) * l = blocks');
    n'
    end
  else
    begin
    (* Proof interlude *)
    (**) begin
    (**) assert(b % l <> 0 || n = 0);
    (**) if b % l <> 0 then
    (**)   begin
    (**)        assert(rest <> 0);
    (**)        Math.Lemmas.nat_times_nat_is_nat n l;
    (**)        assert(n * l >= 0)
    (**)   end
    (**) else
    (**)   begin
    (**)        assert(n = 0);
    (**)        assert(b = n * l + rest);
    (**)   mul_zero_left_is_zero l;
    (**)        assert(n * l = 0);
    (**)        assert(b = rest)
    (**)   end
    (**)end;
    n
    end
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last #index (c: block index) (i: index) (b: bytes):
  Pure (bytes & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      let l = U32.v (c.block_len i) in
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
      (S.length blocks / l) * l = S.length blocks
  ))
=
  let l = U32.v (c.block_len i) in
  let n = split_at_last_num_blocks c i (Seq.length b) in
  Math.Lemmas.nat_times_nat_is_nat n l;
  let blocks, rest = S.split b (n * l) in
  blocks, rest
#pop-options

/// The following lemmas characterize [split_at_last] with conditions which are easy to
/// reason about, and is very useful for the various lemmas in this file which
/// prove properties about how to update the internal buffer so that its content
/// is actually the correct remainder of the data seen so far.
/// TODO: this lemma was introduced lately, it might be good to update the proofs
/// to use it.
/// The proof strategy is to first prove that the blocks and rest sequences have the
/// correct lengths, and the equality between sequences is then trivial to get.

/// TODO: small lemmas I couldn't find in FStar.Math.Lemmas
let add_equal_zero (a b : nat) :
  Lemma
  (requires (a + b = 0))
  (ensures (a = 0 /\ b = 0)) = ()

let mul_equal_zero (a b : nat) :
  Lemma
  (requires (a * b = 0))
  (ensures (a = 0 \/ b = 0)) = ()

/// This first auxiliary lemma only manipulates the lengths of the sequences.
#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last_num_blocks_spec #index (c: block index) (i: index)
                                  (b n rest: nat):
  Lemma
  (requires (
    let l = U32.v (c.block_len i) in
    (rest <= l /\ (rest = 0 ==> b = 0) /\ b = n * l + rest)))
  (ensures (n = split_at_last_num_blocks c i b)) =
  let l = U32.v (c.block_len i) in
  if b = 0 then
    begin
    Math.Lemmas.nat_times_nat_is_nat n l;
    add_equal_zero (n * l) rest;
    mul_equal_zero n l;
    assert(n = 0)
    end
  else
    begin
    assert(b > 0);
    (* In order to prove the equality between all the lengths, we use the unicity
    * of the modulo to prove that the rests are equal, then that the numbers
    * of blocks are equal. *)
    let l = U32.v (c.block_len i) in
    let blocks = n * l in
    let rest = b - blocks in
    let n' = split_at_last_num_blocks c i b in
    let blocks' = n' * l in
    let rest' = b - blocks' in
    Math.Lemmas.cancel_mul_mod n l;
    assert(blocks % l = 0);
    assert(blocks' % l = 0); (* comes from the spec of [split_at_last] *)
    Math.Lemmas.euclidean_division_definition blocks l;

    (* First, prove that the lengths of the rests are equal modulo the size of
    * a block *)
    assert(rest' % l = b % l); (* comes from the spec of [split_at_last] *)
    assert(rest + n * l = b);
    Math.Lemmas.lemma_mod_plus rest n l; (* doesn't work inside a calc: typing problem with squash *)
    assert(b % l = rest % l);
    assert(rest % l = rest' % l);

    (* If both rests are stricly smaller than a block, we can directly apply
    * the modulo injectivity and the rest follows immediately *)
    if rest < l && rest' < l then
      begin
      Math.Lemmas.lemma_mod_injective l rest rest';
      assert(rest = rest');
      assert(n * l + rest = n' * l + rest');
      assert(n * l = n' * l);
      Math.Lemmas.lemma_cancel_mul n n' l;
      assert(n = n')
      end
    (* Otherwise, case one: both rests are equal to block length (even easier) *)
    else if rest = l && rest' = l then
      Math.Lemmas.lemma_cancel_mul n n' l
    (* Last two cases: one of the rests is smaller than a block, and the other is
    * of the size of a block. Because of modulo properties, the smaller rest
    * must be equal to 0, which gives us that both rests are equal, and thus that
    * the numbers of blocks are equal *)
    else
      begin
      assert((rest = l && rest' < l) \/ (rest < l && rest' = l));
      let rest, rest' = if rest = l then rest, rest' else rest', rest in
      assert(rest = l && rest' < l);
      (* [rest % l = 0] *)
      assert(rest = 1 * l);
      Math.Lemmas.cancel_mul_mod 1 l;
      assert(rest % l = 0);
      (* [rest' = 0 ] *)
      Math.Lemmas.modulo_lemma rest' l;
      assert(rest' = 0);
      Math.Lemmas.lemma_cancel_mul n n' l;
      assert(n = n')
      end
    end
#pop-options

/// This second lemma is the one we will use
#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last_spec #index (c: block index) (i: index)
                              (b blocks rest: bytes):
  Lemma
  (requires (
    let l = U32.v (c.block_len i) in
    (S.length blocks % l = 0 /\
     S.length rest <= l /\
     (S.length rest = 0 ==> S.length b = 0) /\
     b `Seq.equal` Seq.append blocks rest)))
  (ensures (
     (blocks, rest) == split_at_last c i b)) =
  (* We need to introduce the variables with which to call [split_at_last_num_blocks_spec] *)
  let l = U32.v (c.block_len i) in
  let b_l = Seq.length b in
  let blocks_l = Seq.length blocks in
  let rest_l = Seq.length rest in
  let blocks', rest' = split_at_last c i b in
  let n' = Seq.length blocks' / l in
  let n = blocks_l / l in
  Math.Lemmas.nat_over_pos_is_nat blocks_l l;
  assert(n >= 0);
  Math.Lemmas.euclidean_division_definition (S.length blocks) l;
  assert(blocks_l = l * n);
  assert(b_l = n * l + rest_l);
  split_at_last_num_blocks_spec c i b_l n rest_l;
  assert(n = split_at_last_num_blocks c i b_l);
  assert(n = n'); (* comes from the spec of [split_at_last] *)
  assert(rest_l = Seq.length rest');
  (* We have the equalities between the sequence lengths, so the rest follows
   * naturally *)
  assert(blocks `Seq.equal` blocks');
  assert(rest `Seq.equal` rest')
#pop-options

/// For the initialization of the streaming state.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_empty #index (c: block index) (i: index): Lemma
  (ensures (
    let blocks, rest = split_at_last c i S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  FStar.Math.Lemmas.multiple_division_lemma 0 (U32.v (c.block_len i))
#pop-options

/// "Small" case: not enough data to obtain strictly more than a complete block,
/// so it suffices to append the new input to the internal buffer. Note that we
/// don't process the resulting buffer because we have to make sure there is always
/// some data remaining in it (after the first call to update) so that [update_last]
/// is called on non-empty data at the very end.
///
/// There are many subcases that we prove in intermediate lemmas, until we can
/// get the final [split_at_last_small] theorem.
/// [b]: internal buffer
/// [d]: data to append

/// "Small" case: subcase 1: not enough data to obtain a complete block append the
/// new input to the internal buffer.

let split_at_last_small_strict #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d < U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in
  split_at_last_spec c i (S.append b d) blocks (S.append rest d)

/// "Small" case: subcase 2: exactly enough data to obtain a complete block, and the
/// internal buffer is empty.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_small_exact_empty_internal #index (c: block index) (i: index) (b: bytes) (d: bytes):
  Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i) /\
    S.length rest = 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  (* The proof is trivial because [b] is empty *)
  assert(b `Seq.equal` Seq.empty);
  assert(S.append b d `Seq.equal` d);
  assert(S.append rest d `Seq.equal` d)
#pop-options

/// "Small" case 3: exactly enough data to obtain a complete block, and the data to
/// add is empty.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_small_exact_empty_data #index (c: block index) (i: index) (b: bytes)
                                                (d: bytes):
  Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i) /\
    S.length d = 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  assert(S.append rest d `S.equal` rest);
  assert(S.append b d `S.equal` b)
#pop-options

/// "Small" case 4: exactly enough data to obtain a complete block, the internal
/// buffer is not empty and the data to add is not empty.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_small_exact #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i) /\
    S.length rest > 0 /\ S.length d > 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in
  let n = S.length blocks / l in

  assert(S.length blocks % l = 0); (* comes from the spec of [split_at_last] *)
  assert(S.length (S.append rest d) = l);  
  assert((S.append b d) `Seq.equal` Seq.append blocks (Seq.append rest d));
  split_at_last_spec c i (S.append b d) blocks (S.append rest d)
#pop-options

/// "Small" case: final theorem: not enough data to obtain strictly more than a
/// complete block, so it suffices to append the new input to the internal buffer.

let split_at_last_small #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d <= U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in
  
  if S.length rest + S.length d < l then
    split_at_last_small_strict c i b d
  else if S.length rest = 0 then
    split_at_last_small_exact_empty_internal c i b d
  else if S.length d = 0 then
    split_at_last_small_exact_empty_data c i b d
  else split_at_last_small_exact c i b d

/// For the initialization of the streaming state.

/// Second case: the data seen so far is empty or a multiple of the block size
/// meaning that the internal buffer is either empty or full, and the data to
/// append is not empty. This is a fast path: we can process the internal
/// buffer if it is non-empty, then process blocks without touching at the buffer
/// and finally copy the remaining data to the buffer. Of course, there must be
/// data remaining in the buffer in the end, which is why the data to append
/// musn't be empty.

#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let split_at_last_blocks #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let blocks, rest = split_at_last c i b in
    (S.length rest = 0 \/ S.length rest = U32.v (c.block_len i)) /\
    S.length d > 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i d in
    let blocks'', rest'' = split_at_last c i (S.append b d) in
    S.equal blocks'' (S.append b blocks') /\
    S.equal rest' rest''))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i d in
  let blocks'', rest'' = split_at_last c i (S.append b d) in
  let b' = S.append blocks rest in
  let d' = S.append blocks' rest' in
  let l = U32.v (c.block_len i) in

  (* We prove the non-trivial requirements of [split_at_last_spec] *)
  assert(S.length b % l = 0);
  Math.Lemmas.modulo_distributivity (S.length b) (S.length blocks') l;
  calc (==) {
    S.length (S.append b blocks') % l;
  (==) {}
    (S.length b + S.length blocks') % l;
  (==) { Math.Lemmas.modulo_distributivity (S.length b) (S.length blocks') l }
    ((S.length b % l) + (S.length blocks' % l)) % l;
  (==) {}
    0 % l;
  (==) { Math.Lemmas.modulo_lemma 0 l }
    0;
  };

  (* End of proof *)
  split_at_last_spec c i (S.append b d) (S.append b blocks') rest'
#pop-options
