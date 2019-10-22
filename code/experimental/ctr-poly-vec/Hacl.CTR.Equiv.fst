module Hacl.CTR.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.CTR

module Lemmas = Hacl.CTR.Lemmas


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
                --using_facts_from '-* +Prims +Lib.Sequence +FStar.Seq +Lib.IntTypes +Hacl.CTR +Hacl.CTR.Equiv +Math.Lemmas'"


val encrypt_block_lemma_index:
     #w:width_t
  -> st_v0:state_v w
  -> ctr:counter{w * ctr <= max_size_t}
  -> b_v:lseq uint8 (w * blocksize)
  -> j:nat{j < w * blocksize} -> Lemma
  (Math.Lemmas.multiple_division_lemma w blocksize;
   let b = Lemmas.get_block_s #_ #(w * blocksize) blocksize b_v j in
   div_mul_lt blocksize j w;
   (encrypt_block_v st_v0 ctr b_v).[j] ==
   (encrypt_block (transpose_state_i st_v0 (j / blocksize)) (w * ctr) b).[j % blocksize])

let encrypt_block_lemma_index #w st_v0 ctr b_v j =
  // let blocksize_v = w * blocksize in
  // Math.Lemmas.multiple_division_lemma w blocksize;
  // let b = Lemmas.get_block_s #_ #blocksize_v blocksize b_v j in
  // div_mul_lt blocksize j w;

  // let k_v = kb_v st_v0 ctr in
  // let res_v = map2 (^.) k_v b_v in

  // let st0 = transpose_state_i st_v0 (j / blocksize) in
  // let k = kb st0 (w * ctr) in
  // let res = map2 (^.) k b in

  kb_v_i #w ctr st_v0 (j / blocksize)


val encrypt_block_equiv_lemma_i:
    #w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> ctr:counter{w * (ctr + 1) <= max_size_t}
  -> b:lseq uint8 blocksize
  -> i:nat{i < w} -> Lemma
  (let st_v0 = init_v #w k n ctr0 in
   let st0 = init k n ctr0 in
   encrypt_block st0 (w * ctr + i) b ==
   encrypt_block (transpose_state_i st_v0 i) (w * ctr) b)

let encrypt_block_equiv_lemma_i #w k n ctr0 ctr b i =
  let st_v0 = init_v #w k n ctr0 in
  let st0 = init k n ctr0 in
  init_v_i #w k n ctr0 i;
  assert (transpose_state_i (init_v #w k n ctr0) i == init k n (ctr0 + i));
  kb_equiv_lemma #w k n ctr0 ctr i




val encrypt_block_equiv_lemma_index:
    #w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> ctr:counter{w * (ctr + 1) <= max_size_t}
  -> b_v:lseq uint8 (w * blocksize)
  -> j:nat{j < w * blocksize} -> Lemma
  (let st_v0 = init_v #w k n ctr0 in
   let st0 = init k n ctr0 in
   Math.Lemmas.multiple_division_lemma w blocksize;
   let b = Lemmas.get_block_s #_ #(w * blocksize) blocksize b_v j in
   div_mul_lt blocksize j w;
   (encrypt_block_v st_v0 ctr b_v).[j] ==
   (encrypt_block st0 (w * ctr + j / blocksize) b).[j % blocksize])

let encrypt_block_equiv_lemma_index #w k n ctr0 ctr b_v j =
  let blocksize_v = w * blocksize in
  let st_v0 = init_v #w k n ctr0 in
  let st0 = init k n ctr0 in
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = Lemmas.get_block_s #_ #blocksize_v blocksize b_v j in
  div_mul_lt blocksize j w;
  encrypt_block_lemma_index #w st_v0 ctr b_v j;
  encrypt_block_equiv_lemma_i #w k n ctr0 ctr b (j / blocksize)


val lemma_encrypt_block_vec_equiv:
    #w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> i:nat{i / blocksize <= max_size_t /\ w * (i / (w * blocksize) + 1) <= max_size_t}
  -> b_v:lseq uint8 (w * blocksize) -> Lemma
  (let st_v0 = init_v #w k n ctr0 in
   let st0 = init k n ctr0 in
   let j = i % (w * blocksize) in
   Math.Lemmas.multiple_division_lemma w blocksize;
   let b = Lemmas.get_block_s #_ #(w * blocksize) blocksize b_v j in
   (encrypt_block_v st_v0 (i / (w * blocksize)) b_v).[j] ==
   (encrypt_block st0 (i / blocksize) b).[i % blocksize])

let lemma_encrypt_block_vec_equiv #w k n ctr0 i b_v =
  let st_v0 = init_v #w k n ctr0 in
  let st0 = init k n ctr0 in
  let blocksize_v = w * blocksize in
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = Lemmas.get_block_s #_ #(w * blocksize) blocksize b_v (i % blocksize_v) in
  let ctr = i / blocksize_v in
  let j = i % blocksize_v in
  encrypt_block_equiv_lemma_index #w k n ctr0 ctr b_v j;
  Lemmas.lemma_i_div_bs w blocksize i;
  Math.Lemmas.modulo_modulo_lemma i blocksize w


val lemma_map_blocks_vec_equiv_pre_f_v:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> msg:seq uint8{w * (length msg / (w * blocksize) + 1) <= max_size_t /\ length msg / blocksize <= max_size_t}
  -> i:nat{i < length msg / (w * blocksize) * (w * blocksize)}
  -> b_v:lseq uint8 (w * blocksize) -> Lemma
  (let st_v0 = init_v #w k n c0 in
   let st0 = init k n c0 in

   let f_v = encrypt_block_v st_v0 in
   let f = encrypt_block st0 in
   Lemmas.map_blocks_vec_equiv_pre_f_v #_ #(length msg) w blocksize (w * blocksize) f f_v i b_v)

let lemma_map_blocks_vec_equiv_pre_f_v #w k n c0 msg i b_v =
  let len = length msg in
  let blocksize_v = w * blocksize in

  Lemmas.lemma_div_bs_v_le len w blocksize;
  div_mul_lt blocksize i (len / blocksize);
  div_mul_lt blocksize_v i (len / blocksize_v);
  lemma_encrypt_block_vec_equiv #w k n c0 i b_v



val lemma_j_blocksize: len:nat -> bs:pos -> j:nat{j < len / bs * bs} -> Lemma (j / bs * bs + bs <= len / bs * bs)
let lemma_j_blocksize len bs j =
  div_mul_lt bs j (len / bs);
  assert (j / bs + 1 <= len / bs);
  assert ((j / bs + 1) * bs <= len / bs * bs)


val encrypt_last_lemma_index1_slice:
    #w:width_t
  -> len:nat{len < w * blocksize}
  -> b_v:lseq uint8 len
  -> j:nat{j < len / blocksize * blocksize} -> Lemma
  (let blocksize_v = w * blocksize in
   let plain = create blocksize_v (u8 0) in
   let plain = update_sub plain 0 len b_v in
   div_mul_lt blocksize j w;
   Math.Lemmas.cancel_mul_div w blocksize;
   Lemmas.get_block_s #uint8 #blocksize_v blocksize plain j ==
   Lemmas.get_block_s #uint8 #len blocksize b_v j)

let encrypt_last_lemma_index1_slice #w len b_v j =
  let blocksize_v = w * blocksize in
  let plain = create blocksize_v (u8 0) in
  let plain = update_sub plain 0 len b_v in
  assert (slice plain 0 len == b_v);
  div_mul_lt blocksize j w;
  Math.Lemmas.cancel_mul_div w blocksize;
  //assert (j / blocksize < w);
  //assert (j < blocksize_v / blocksize * blocksize);
  let b_p = Lemmas.get_block_s #uint8 #blocksize_v blocksize plain j in
  lemma_j_blocksize len blocksize j;
  //assert (j / blocksize * blocksize + blocksize <= len);
  Seq.Properties.slice_slice plain 0 len (j / blocksize * blocksize) (j / blocksize * blocksize + blocksize);
  let b = Lemmas.get_block_s #uint8 #len blocksize b_v j in
  eq_intro b b_p


val encrypt_last_equiv_lemma_index1:
    #w:width_t
  -> blocksize_v:size_pos{blocksize_v == w * blocksize}
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> len:nat{w * (len / blocksize_v + 1) <= max_size_t /\ len / blocksize <= max_size_t}
  -> b_v:lseq uint8 (len % blocksize_v)
  -> i:nat{i % blocksize_v < (len % blocksize_v) / blocksize * blocksize /\
        len / blocksize_v * blocksize_v <= i /\ i < len} ->
  Lemma
  (let st_v0 = init_v #w k n ctr0 in
   let st0 = init k n ctr0 in
   let j = i % blocksize_v in
   let rem = len % blocksize_v in
   let b = Lemmas.get_block_s #uint8 #rem blocksize b_v j in
   assume (i % blocksize_v < len % blocksize_v /\ i / blocksize <= max_size_t /\ len / blocksize_v <= max_size_t);
   (encrypt_last_v st_v0 (len / blocksize_v) rem b_v).[j] ==
   (encrypt_block st0 (i / blocksize) b).[i % blocksize])

let encrypt_last_equiv_lemma_index1 #w blocksize_v k n ctr0 len b_v i =
  let st_v0 = init_v #w k n ctr0 in
  let st0 = init k n ctr0 in
  let j = i % blocksize_v in
  let rem = len % blocksize_v in

  let plain = create blocksize_v (u8 0) in
  let plain = update_sub plain 0 rem b_v in
  let ctr = i / blocksize_v in
  assume (i / blocksize_v == len / blocksize_v);
  let res = encrypt_last_v st_v0 ctr rem b_v in
  assert (res == sub (encrypt_block_v st_v0 ctr plain) 0 rem);
  assume (i % blocksize_v < len % blocksize_v /\ i / blocksize <= max_size_t /\ len / blocksize_v <= max_size_t);
  lemma_encrypt_block_vec_equiv #w k n ctr0 i plain;
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = Lemmas.get_block_s #uint8 #blocksize_v blocksize plain j in
  //assert ((encrypt_block_v st_v0 ctr plain).[j] == (encrypt_block st0 (i / blocksize) b).[i % blocksize]);
  encrypt_last_lemma_index1_slice #w rem b_v j


val encrypt_last_equiv_lemma_index2:
    #w:width_t
  -> blocksize_v:size_pos{blocksize_v == w * blocksize}
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> len:nat{w * (len / blocksize_v + 1) <= max_size_t /\ len / blocksize <= max_size_t}
  -> b_v:lseq uint8 (len % blocksize_v)
  -> i:nat{(len % blocksize_v) / blocksize * blocksize <= i % blocksize_v /\ i % blocksize_v < len % blocksize_v /\
         len / blocksize_v * blocksize_v <= i /\ i < len} ->
  Lemma
  (let st_v0 = init_v #w k n ctr0 in
   let st0 = init k n ctr0 in
   let j = i % blocksize_v in
   let rem = len % blocksize_v in
   let b : lseq uint8 (rem % blocksize) = Lemmas.get_last_s #uint8 #rem blocksize b_v in
   let rp : lseq uint8 (rem % blocksize) = encrypt_last st0 (len / blocksize) (rem % blocksize) b in
   assume (len / blocksize_v <= max_size_t /\ i % blocksize < rem % blocksize);
   (encrypt_last_v st_v0 (len / blocksize_v) rem b_v).[j] == rp.[i % blocksize])

let encrypt_last_equiv_lemma_index2 #w blocksize_v k n ctr0 len b_v i =
  let st_v0 = init_v #w k n ctr0 in
  let st0 = init k n ctr0 in
  let j = i % blocksize_v in
  let rem = len % blocksize_v in

  let plain = create blocksize_v (u8 0) in
  let plain = update_sub plain 0 rem b_v in
  let ctr = i / blocksize_v in
  assume (len / blocksize_v <= max_size_t);
  assume (i / blocksize_v == len / blocksize_v);
  let res = encrypt_last_v st_v0 ctr rem b_v in
  assert (res == sub (encrypt_block_v st_v0 ctr plain) 0 rem);
  assume (i / blocksize == len / blocksize);
  lemma_encrypt_block_vec_equiv #w k n ctr0 i plain;
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = Lemmas.get_block_s #_ #blocksize_v blocksize plain j in
  assert ((encrypt_block_v st_v0 ctr plain).[j] == (encrypt_block st0 (i / blocksize) b).[i % blocksize]);
  admit()


val lemma_map_blocks_vec_equiv_pre_g_v:
    #w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> msg:seq uint8{w * (length msg / (w * blocksize) + 1) <= max_size_t /\ length msg / blocksize <= max_size_t}
  -> i:nat{length msg / (w * blocksize) * (w * blocksize) <= i /\ i < length msg}
  -> b_v:lseq uint8 (length msg % (w * blocksize)) ->
  Lemma
  (let st_v0 = init_v #w k n ctr0 in
   let st0 = init k n ctr0 in

   let g_v = encrypt_last_v st_v0 in
   let f = encrypt_block st0 in
   let g = encrypt_last st0 in
   Lemmas.map_blocks_vec_equiv_pre_g_v #uint8 #(length msg) w blocksize (w * blocksize) f g g_v i b_v)

let lemma_map_blocks_vec_equiv_pre_g_v #w k n ctr0 msg i b_v =
  let len = length msg in
  let blocksize_v = w * blocksize in
  let rem_v = len % blocksize_v in
  let rem = len % blocksize in
  assume (rem_v % blocksize = rem);

  let j = i % blocksize_v in
  if j < (rem_v / blocksize) * blocksize then
    encrypt_last_equiv_lemma_index1 #w blocksize_v k n ctr0 len b_v i
  else begin
    assume (len / blocksize_v * blocksize_v <= i /\ i < len);
    mod_div_lt blocksize_v i len;
    assert (i % blocksize_v < len % blocksize_v);
    assume (i % blocksize < rem);
    encrypt_last_equiv_lemma_index2 #w blocksize_v k n ctr0 len b_v i end


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let ctr_equivalence w k n c0 msg =
  let len = length msg in
  let blocksize = blocksize in
  let blocksize_v = w * blocksize in

  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in

  let f_v = encrypt_block_v st_v0 in
  let g_v = encrypt_last_v st_v0 in

  let f = encrypt_block st0 in
  let g = encrypt_last st0 in

  Classical.forall_intro_2 (lemma_map_blocks_vec_equiv_pre_f_v #w k n c0 msg);
  Classical.forall_intro_2 (lemma_map_blocks_vec_equiv_pre_g_v #w k n c0 msg);

  Lemmas.lemma_map_blocks_vec #uint8 #len w blocksize msg f g f_v g_v
