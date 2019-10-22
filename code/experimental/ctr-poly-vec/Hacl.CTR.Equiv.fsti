module Hacl.CTR.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.CTR

module Lemmas = Hacl.CTR.Lemmas


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Lib.Sequence +FStar.Seq +Lib.IntTypes +Hacl.CTR +Hacl.CTR.Equiv +Math.Lemmas'"

///
///  To use this definition of the ctr_equivalence lemma in Hacl.Spec.Chacha20.Equiv,
///  we need to drop the implementation details of the encrypt_block function and
///  not introduce the kb function. It allows us to perform the xor operation on the state type,
///  and then store a result.
///

let ctr_equivalence_pre_v
  (#w:width_t)
  (k:key)
  (n:nonce)
  (ctr0:counter{ctr0 + w <= max_size_t})
  (ctr:counter{w * (ctr + 1) <= max_size_t})
  (b_v:lseq uint8 (w * blocksize))
  (j:nat{j < w * blocksize}) : prop
 =
  let st_v0 = init_v #w k n ctr0 in
  let st0 = init k n ctr0 in
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = Lemmas.get_block_s #_ #(w * blocksize) blocksize b_v j in
  div_mul_lt blocksize j w;
  (encrypt_block_v st_v0 ctr b_v).[j] ==
  (encrypt_block st0 (w * ctr + j / blocksize) b).[j % blocksize]


///
///  Define the ctr_equivalence_pre_v predicate in terms of the kb and init functions
///

let init_v_i_pre
  (#w:width_t)
  (k:key)
  (n:nonce)
  (ctr0:counter{ctr0 + w <= max_size_t})
  (i:nat{i < w}) : prop
 =
  transpose_state_i (init_v #w k n ctr0) i == init k n (ctr0 + i)


let kb_v_i_pre
  (#w:width_t)
  (k:key)
  (n:nonce)
  (ctr0:counter{ctr0 + w <= max_size_t})
  (ctr:counter{w * (ctr + 1) <= max_size_t})
  (i:nat{i < w})
 =
  let st_v0 = init_v #w k n ctr0 in
  assert ((i + 1) * blocksize <= w * blocksize);
  sub (kb_v st_v0 ctr) (i * blocksize) blocksize == kb (transpose_state_i st_v0 i) (w * ctr)


let kb_equiv_pre
  (#w:width_t)
  (k:key)
  (n:nonce)
  (ctr0:counter{ctr0 + w <= max_size_t})
  (ctr:counter{w * (ctr + 1) <= max_size_t})
  (i:nat{i < w})
 =
  kb (init k n ctr0) (w * ctr + i) == kb (init k n (ctr0 + i)) (w * ctr)


let ctr_equivalence_pre_kb_v
  (#w:width_t)
  (k:key)
  (n:nonce)
  (ctr0:counter{ctr0 + w <= max_size_t})
  (ctr:counter{w * (ctr + 1) <= max_size_t})
  (b_v:lseq uint8 (w * blocksize))
  (j:nat{j < w * blocksize}) : prop
 =
  Math.Lemmas.multiple_division_lemma w blocksize;
  let (i:nat{i < w}) = j / blocksize in
  init_v_i_pre #w k n ctr0 i /\
  kb_v_i_pre #w k n ctr0 ctr i /\
  kb_equiv_pre #w k n ctr0 ctr i


val ctr_equivalence_pre_v_kb_lemma:
     #w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> pre:squash (forall (ctr:counter{w * (ctr + 1) <= max_size_t}) (b_v:lseq uint8 (w * blocksize)) (j:nat{j < w * blocksize}).
                 ctr_equivalence_pre_kb_v #w k n ctr0 ctr b_v j)
  -> ctr:counter{w * (ctr + 1) <= max_size_t}
  -> b_v:lseq uint8 (w * blocksize)
  -> j:nat{j < w * blocksize} ->
  Lemma (ctr_equivalence_pre_v #w k n ctr0 ctr b_v j)

///
///  Specification equivalence lemma
///

val ctr_equivalence:
    w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:seq uint8 ->
  Lemma
  (requires
    ctr0 + w <= max_size_t /\
    length msg / blocksize <= max_size_t /\ w * (length msg / (w * blocksize) + 1) <= max_size_t /\
    (forall (ctr:counter{w * (ctr + 1) <= max_size_t}) (b_v:lseq uint8 (w * blocksize)) (j:nat{j < w * blocksize}).
     ctr_equivalence_pre_v #w k n ctr0 ctr b_v j))
  (ensures
    ctr_v #w k n ctr0 msg `Seq.equal` ctr k n ctr0 msg)


let ctr_equivalence_kb
  (#w:width_t)
  (k:key)
  (n:nonce)
  (ctr0:counter{ctr0 + w <= max_size_t})
  (msg:seq uint8) : Lemma
  (requires
    ctr0 + w <= max_size_t /\
    length msg / blocksize <= max_size_t /\ w * (length msg / (w * blocksize) + 1) <= max_size_t /\
    (forall (ctr:counter{w * (ctr + 1) <= max_size_t}) (b_v:lseq uint8 (w * blocksize)) (j:nat{j < w * blocksize}).
     ctr_equivalence_pre_kb_v #w k n ctr0 ctr b_v j))
  (ensures ctr_v #w k n ctr0 msg `Seq.equal` ctr k n ctr0 msg)
  =
  Classical.forall_intro_3 (ctr_equivalence_pre_v_kb_lemma #w k n ctr0 ());
  ctr_equivalence w k n ctr0 msg
