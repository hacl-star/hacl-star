module Hacl.CTR.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas

open Hacl.CTR


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val encrypt_block_lemma_st0_i:
     #w:width_t
  -> st_v0:state_v w
  -> c:counter{w * c <= max_size_t}
  -> b_v:block_v w
  -> j:nat{j < w * blocksize} -> Lemma
  (Math.Lemmas.multiple_division_lemma w blocksize;
   let b = get_block_s #_ #(w * blocksize) blocksize b_v j in
   div_mul_lt blocksize j w;
   (encrypt_block_v st_v0 c b_v).[j] ==
   (encrypt_block (transpose_state_i st_v0 (j / blocksize)) (w * c) b).[j % blocksize])

let encrypt_block_lemma_st0_i #w st_v0 c b_v j =
  // let blocksize_v = w * blocksize in
  // Math.Lemmas.multiple_division_lemma w blocksize;
  // let b = Lemmas.get_block_s #_ #blocksize_v blocksize b_v j in
  // div_mul_lt blocksize j w;

  // let k_v = kb_v st_v0 c in
  // let res_v = map2 (^.) k_v b_v in

  // let st0 = transpose_state_i st_v0 (j / blocksize) in
  // let k = kb st0 (w * c) in
  // let res = map2 (^.) k b in
  let i = j / blocksize in
  div_mul_lt blocksize j w;
  assert (i < w);
  kb_v_i #w c st_v0 (j / blocksize)


val encrypt_block_scalar_lemma_i:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w - 1 <= max_size_t}
  -> c:counter{w * c + w - 1 <= max_size_t}
  -> b:block
  -> i:nat{i < w} -> Lemma
  (let st_v0 = init_v #w k n c0 in
   let st0 = init k n c0 in
   encrypt_block st0 (w * c + i) b ==
   encrypt_block (transpose_state_i st_v0 i) (w * c) b)

let encrypt_block_scalar_lemma_i #w k n c0 c b i =
  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in
  init_v_i #w k n c0 i;
  assert (transpose_state_i (init_v #w k n c0) i == init k n (c0 + i));
  kb_equiv_lemma #w k n c0 c i


val encrypt_block_lemma_bs_i:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w - 1 <= max_size_t}
  -> c:counter{w * c + w - 1 <= max_size_t}
  -> b_v:block_v w
  -> j:nat{j < w * blocksize} -> Lemma
  (let st_v0 = init_v #w k n c0 in
   let st0 = init k n c0 in
   Math.Lemmas.multiple_division_lemma w blocksize;
   let b = get_block_s #_ #(w * blocksize) blocksize b_v j in
   div_mul_lt blocksize j w;
   (encrypt_block_v st_v0 c b_v).[j] ==
   (encrypt_block st0 (w * c + j / blocksize) b).[j % blocksize])

let encrypt_block_lemma_bs_i #w k n c0 c b_v j =
  let blocksize_v = w * blocksize in
  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = get_block_s #_ #blocksize_v blocksize b_v j in
  div_mul_lt blocksize j w;
  encrypt_block_lemma_st0_i #w st_v0 c b_v j;
  encrypt_block_scalar_lemma_i #w k n c0 c b (j / blocksize)


val lemma_aux: w:pos -> bs:pos -> len:nat -> i:nat{i <= len} -> Lemma
  (requires w * bs <= max_size_t /\ len / bs <= max_size_t)
  (ensures  i / (w * bs) * w <= len / bs)
let lemma_aux w bs len i =
  calc (<=) {
    i / (w * bs) * w;
    (==) { Math.Lemmas.swap_mul w bs;
           Math.Lemmas.division_multiplication_lemma i bs w }
    (i / bs) / w * w;
    (<=) { Math.Lemmas.multiply_fractions (i / bs) w }
    i / bs;
    (<=) { Math.Lemmas.lemma_div_le i len bs }
    len / bs;
  }


val encrypt_block_lemma_i:
    #w:width_t
  -> #len:nat{len / blocksize + w - 1 <= max_size_t /\ len / (w * blocksize) <= max_size_t}
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w - 1 <= max_size_t}
  -> i:nat{i <= len}
  -> b_v:block_v w -> Lemma
  (let st_v0 = init_v #w k n c0 in
   let st0 = init k n c0 in
   let j = i % (w * blocksize) in
   Math.Lemmas.multiple_division_lemma w blocksize;
   let b = get_block_s #_ #(w * blocksize) blocksize b_v j in
   (encrypt_block_v st_v0 (i / (w * blocksize)) b_v).[j] ==
   (encrypt_block st0 (i / blocksize) b).[i % blocksize])

let encrypt_block_lemma_i #w #len k n c0 i b_v =
  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in

  let blocksize_v = w * blocksize in
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = get_block_s #_ #(w * blocksize) blocksize b_v (i % blocksize_v) in
  let c = i / blocksize_v in
  let j = i % blocksize_v in
  lemma_aux w blocksize len i;
  encrypt_block_lemma_bs_i #w k n c0 c b_v j;
  lemma_i_div_bs w blocksize i;
  Math.Lemmas.modulo_modulo_lemma i blocksize w;
  assert  (w * c + j / blocksize == i / blocksize);
  lemma_mod_bs_v_bs i w blocksize


val lemma_map_blocks_ctr_vec_equiv_pre:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w - 1 <= max_size_t}
  -> msg:seq uint8{length msg / blocksize + w - 1 <= max_size_t /\ length msg / (w * blocksize) <= max_size_t}
  -> i:nat{i <= length msg}
  -> b_v:block_v w -> Lemma
  (let st_v0 = init_v #w k n c0 in
   let st0 = init k n c0 in

   let f_v = encrypt_block_v st_v0 in
   let f = encrypt_block st0 in
   map_blocks_ctr_vec_equiv_pre #_ #(length msg) w blocksize (w * blocksize) f f_v i b_v)

let lemma_map_blocks_ctr_vec_equiv_pre #w k n c0 msg i b_v =
  encrypt_block_lemma_i #w #(length msg) k n c0 i b_v


let ctr_equivalence w k n c0 msg =
  let len = length msg in
  let blocksize = blocksize in
  let blocksize_v = w * blocksize in

  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in

  let f_v = encrypt_block_v st_v0 in
  let f = encrypt_block st0 in

  Classical.forall_intro_2 (lemma_map_blocks_ctr_vec_equiv_pre #w k n c0 msg);
  lemma_map_blocks_ctr_vec #uint8 #len w blocksize msg f f_v (u8 0)
