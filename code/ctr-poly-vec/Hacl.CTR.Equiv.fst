module Hacl.CTR.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas
open Hacl.CTR

module VecLemmas = Lib.Vec.Lemmas


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

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
  -> c0:counter{c0 + w <= max_size_t}
  -> c:counter{w * c + w <= max_size_t}
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


val ctr_map_multi_blocks_vec_equiv_pre_k:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:nat // n == hi_fv == len / (w * blocksize)
  -> hi_f:size_nat{w * hi_fv <= hi_f}
  -> i:nat{i < hi_fv}
  -> b_v:block_v w
  -> j:nat{j < w * blocksize} -> Lemma
  (let st_v0 = init_v #w k n c0 in
   let st0 = init k n c0 in

   let f_v = encrypt_block_v st_v0 in
   let f = encrypt_block st0 in
   VecLemmas.map_blocks_multi_vec_equiv_pre_k w blocksize hi_fv hi_f f f_v i b_v j)

let ctr_map_multi_blocks_vec_equiv_pre_k #w k n c0 hi_fv hi_f i b_v j =
  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in

  let f_v = encrypt_block_v st_v0 in
  let f = encrypt_block st0 in
  encrypt_block_lemma_bs_i #w k n c0 i b_v j;
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = get_block_s #_ #(w * blocksize) blocksize b_v j in
  div_mul_lt blocksize j w;
  assert ((encrypt_block_v st_v0 i b_v).[j] ==
   (encrypt_block st0 (w * i + j / blocksize) b).[j % blocksize]); //?? Without this assert the proof doesn't go through
  assert (VecLemmas.map_blocks_multi_vec_equiv_pre_k w blocksize hi_fv hi_f f f_v i b_v j)


////////////////////////
// Start of proof of VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j
////////////////////////

val update_sub_is_append:
    #a:Type0
  -> zero:a
  -> blocksize:size_pos
  -> len:nat{len < blocksize}
  -> b_v:lseq a len ->
  Lemma
   (let plain = create blocksize zero in
    let plain = update_sub plain 0 len b_v in
    let zeros = create (blocksize - len) zero in
    plain == Seq.append b_v zeros)

let update_sub_is_append #a zero blocksize len b_v =
  let plain = create blocksize zero in
  let plain = update_sub plain 0 len b_v in
  let zeros = create (blocksize - len) zero in
  Seq.Properties.lemma_split plain len;
  Seq.Properties.lemma_split (Seq.append b_v zeros) len;
  eq_intro plain (Seq.append b_v zeros)


#set-options "--z3rlimit 100"

val update_sub_get_block_lemma_k:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{j < len / blocksize * blocksize}
  -> k:nat{k < blocksize} ->
  Lemma
   (let blocksize_v = w * blocksize in
    let plain_v = create blocksize_v zero in
    let plain_v = update_sub plain_v 0 len b_v in
    div_mul_lt blocksize j w;
    Math.Lemmas.cancel_mul_div w blocksize;

    Seq.index (get_block_s #a #blocksize_v blocksize plain_v j) k ==
    Seq.index (get_block_s #a #len blocksize b_v j) k)

let update_sub_get_block_lemma_k #a w blocksize zero len b_v j k =
  let blocksize_v = w * blocksize in
  let plain = create blocksize_v zero in
  let plain = update_sub plain 0 len b_v in
  let zeros = create (blocksize_v - len) zero in
  update_sub_is_append #a zero blocksize_v len b_v;
  assert (plain == Seq.append b_v zeros);

  div_mul_lt blocksize j w;
  Math.Lemmas.cancel_mul_div w blocksize;
  //assert (j / blocksize < w);
  //assert (j < blocksize_v / blocksize * blocksize);
  let b_p = get_block_s #a #blocksize_v blocksize plain j in
  let b = get_block_s #a #len blocksize b_v j in

  calc (<=) {
    (j / blocksize + 1) * blocksize;
    (<=) { div_mul_lt blocksize j (len / blocksize) }
    len / blocksize * blocksize;
    (<=) { Math.Lemmas.multiply_fractions len blocksize }
    len;
  };

  calc (==) {
    Seq.index b_p k;
    (==) { }
    Seq.index (Seq.slice plain (j / blocksize * blocksize) (j / blocksize * blocksize + blocksize)) k;
    (==) { Seq.lemma_index_slice plain (j / blocksize * blocksize) (j / blocksize * blocksize + blocksize) k }
    Seq.index plain (j / blocksize * blocksize + k);
    (==) { Seq.lemma_index_app1 b_v zeros (j / blocksize * blocksize + k) }
    Seq.index b_v (j / blocksize * blocksize + k);
    };

  Seq.lemma_index_slice b_v (j / blocksize * blocksize) (j / blocksize * blocksize + blocksize) k


val update_sub_get_block_lemma:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{j < len / blocksize * blocksize} ->
  Lemma
   (let blocksize_v = w * blocksize in
    let plain_v = create blocksize_v zero in
    let plain_v = update_sub plain_v 0 len b_v in
    div_mul_lt blocksize j w;
    Math.Lemmas.cancel_mul_div w blocksize;

    get_block_s #a #blocksize_v blocksize plain_v j ==
    get_block_s #a #len blocksize b_v j)

let update_sub_get_block_lemma #a w blocksize zero len b_v j =
  let blocksize_v = w * blocksize in
  let plain = create blocksize_v zero in
  let plain = update_sub plain 0 len b_v in

  div_mul_lt blocksize j w;
  Math.Lemmas.cancel_mul_div w blocksize;
  let b_p = get_block_s #a #blocksize_v blocksize plain j in
  let b = get_block_s #a #len blocksize b_v j in
  Classical.forall_intro (update_sub_get_block_lemma_k #a w blocksize zero len b_v j);
  eq_intro b b_p


val update_sub_get_last_lemma_plain_k:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{len / blocksize * blocksize <= j /\ j < len}
  -> k:nat{k < blocksize} ->
  Lemma
   (let block_l = get_last_s #a #len blocksize b_v in
    let plain = create blocksize zero in
    let plain = update_sub plain 0 (len % blocksize) block_l in

    Seq.index plain k == (if k < len % blocksize then Seq.index b_v (len / blocksize * blocksize + k) else zero))

let update_sub_get_last_lemma_plain_k #a w blocksize zero len b_v j k =
  let block_l = get_last_s #a #len blocksize b_v in
  let plain = create blocksize zero in
  let plain = update_sub plain 0 (len % blocksize) block_l in

  let zeros = create (blocksize - len % blocksize) zero in
  update_sub_is_append #a zero blocksize (len % blocksize) block_l;
  assert (plain == Seq.append block_l zeros);

  if k < len % blocksize then begin
    calc (==) {
      Seq.index plain k;
      (==) { Seq.lemma_index_app1 block_l zeros k }
      Seq.index block_l k;
      (==) { Seq.lemma_index_slice b_v (len - len % blocksize) len k }
      Seq.index b_v (len - len % blocksize + k);
      (==) { Math.Lemmas.euclidean_division_definition len blocksize }
      Seq.index b_v (len / blocksize * blocksize + k);
      } end
  else ()


val update_sub_get_last_lemma_plain_v_k:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{len / blocksize * blocksize <= j /\ j < len}
  -> k:nat{k < blocksize} ->
  Lemma
   (let blocksize_v = w * blocksize in
    let plain_v = create blocksize_v zero in
    let plain_v = update_sub plain_v 0 len b_v in
    div_mul_lt blocksize j w;
    Math.Lemmas.cancel_mul_div w blocksize;
    let b = get_block_s #a #blocksize_v blocksize plain_v j in
    div_interval blocksize (len / blocksize) j;

    Seq.index b k == (if k < len % blocksize then Seq.index b_v (len / blocksize * blocksize + k) else zero))

let update_sub_get_last_lemma_plain_v_k #a w blocksize zero len b_v j k =
  let blocksize_v = w * blocksize in
  let plain_v = create blocksize_v zero in
  let plain_v = update_sub plain_v 0 len b_v in
  let zeros_v = create (blocksize_v - len) zero in
  update_sub_is_append #a zero blocksize_v len b_v;
  assert (plain_v == Seq.append b_v zeros_v);

  div_mul_lt blocksize j w;
  //assert (j / blocksize < w);
  Math.Lemmas.cancel_mul_div w blocksize;
  let b = get_block_s #a #blocksize_v blocksize plain_v j in
  Math.Lemmas.lemma_mult_le_right blocksize (j / blocksize + 1) w;
  assert (j / blocksize * blocksize + blocksize <= blocksize_v);

  div_interval blocksize (len / blocksize) j;
  assert (j / blocksize * blocksize + k == len / blocksize * blocksize + k);

  calc (==) {
    //Seq.index b k;
    //(==) { }
    Seq.index (Seq.slice plain_v (j / blocksize * blocksize) (j / blocksize * blocksize + blocksize)) k;
    (==) { Seq.lemma_index_slice plain_v (j / blocksize * blocksize) (j / blocksize * blocksize + blocksize) k }
    Seq.index plain_v (j / blocksize * blocksize + k);
    (==) {  }
    Seq.index plain_v (len / blocksize * blocksize + k);
    }


val update_sub_get_last_lemma:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{len / blocksize * blocksize <= j /\ j < len} ->
  Lemma
   (let blocksize_v = w * blocksize in
    let plain_v = create blocksize_v zero in
    let plain_v = update_sub plain_v 0 len b_v in
    div_mul_lt blocksize j w;
    Math.Lemmas.cancel_mul_div w blocksize;

    let block_l = get_last_s #a #len blocksize b_v in
    let plain = create blocksize zero in
    let plain = update_sub plain 0 (len % blocksize) block_l in

    get_block_s #a #blocksize_v blocksize plain_v j == plain)

let update_sub_get_last_lemma #a w blocksize zero len b_v j =
  let blocksize_v = w * blocksize in
  let plain_v = create blocksize_v zero in
  let plain_v = update_sub plain_v 0 len b_v in
  div_mul_lt blocksize j w;
  Math.Lemmas.cancel_mul_div w blocksize;

  let block_l = get_last_s #a #len blocksize b_v in
  let plain = create blocksize zero in
  let plain = update_sub plain 0 (len % blocksize) block_l in
  let b = get_block_s #a #blocksize_v blocksize plain_v j in

  let aux (k:nat{k < blocksize}) : Lemma (Seq.index b k == Seq.index plain k) =
    update_sub_get_last_lemma_plain_k #a w blocksize zero len b_v j k;
    update_sub_get_last_lemma_plain_v_k #a w blocksize zero len b_v j k in

  Classical.forall_intro aux;
  eq_intro b plain


#set-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"

val ctr_map_blocks_vec_equiv_pre_k0:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:size_nat{w * hi_fv + w <= max_size_t} // n == hi_fv == len / (w * blocksize)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq uint8 rem
  -> j:nat{j < rem / blocksize * blocksize} ->
  Lemma
   (let st_v0 = init_v #w k n c0 in
    let st0 = init k n c0 in
    let g_v = encrypt_last_v st_v0 in
    let f = encrypt_block st0 in
    let g = encrypt_last st0 in
    VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j)

let ctr_map_blocks_vec_equiv_pre_k0 #w k n c0 hi_fv rem b_v j =
  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in
  let g_v = encrypt_last_v st_v0 in
  let f = encrypt_block st0 in
  let g = encrypt_last st0 in

  let blocksize_v = w * blocksize in
  let plain_v = create blocksize_v (u8 0) in
  let plain_v = update_sub plain_v 0 rem b_v in

  Math.Lemmas.cancel_mul_div w blocksize;
  let b = get_block_s #uint8 #blocksize_v blocksize plain_v j in
  let b1 = get_block_s #uint8 #rem blocksize b_v j in

  calc (==) {
    Seq.index (g_v hi_fv rem b_v) j;
    (==) { encrypt_block_lemma_bs_i #w k n c0 hi_fv plain_v j; div_mul_lt blocksize j w }
    Seq.index (f (w * hi_fv + j / blocksize) b) (j % blocksize);
    (==) { update_sub_get_block_lemma w blocksize (u8 0) rem b_v j }
    Seq.index (f (w * hi_fv + j / blocksize) b1) (j % blocksize);
    }


val ctr_map_blocks_vec_equiv_pre_k1:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:size_nat{w * hi_fv + w <= max_size_t} // n == hi_fv == len / (w * blocksize)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq uint8 rem
  -> j:nat{rem / blocksize * blocksize <= j /\ j < rem} ->
  Lemma
   (let st_v0 = init_v #w k n c0 in
    let st0 = init k n c0 in
    let g_v = encrypt_last_v st_v0 in
    let f = encrypt_block st0 in
    let g = encrypt_last st0 in
    VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j)

#push-options "--z3rlimit 150"
let ctr_map_blocks_vec_equiv_pre_k1 #w k n c0 hi_fv rem b_v j =
  let st_v0 = init_v #w k n c0 in
  let st0 = init k n c0 in
  let g_v = encrypt_last_v st_v0 in
  let f = encrypt_block st0 in
  let g = encrypt_last st0 in

  let blocksize_v = w * blocksize in
  let plain_v = create blocksize_v (u8 0) in
  let plain_v = update_sub plain_v 0 rem b_v in

  Math.Lemmas.cancel_mul_div w blocksize;
  let b = get_block_s #uint8 #blocksize_v blocksize plain_v j in
  let b1 = get_last_s #uint8 #rem blocksize b_v in

  let plain = create blocksize (u8 0) in
  let plain = update_sub plain 0 (rem % blocksize) b1 in
  div_mul_lt blocksize j w;
  mod_div_lt blocksize j rem;
  assert (j % blocksize < rem % blocksize);

  calc (==) {
    Seq.index (g_v hi_fv rem b_v) j;
    (==) { encrypt_block_lemma_bs_i #w k n c0 hi_fv plain_v j }
    Seq.index (f (w * hi_fv + j / blocksize) b) (j % blocksize);
    (==) { update_sub_get_last_lemma w blocksize (u8 0) rem b_v j}
    Seq.index (f (w * hi_fv + j / blocksize) plain) (j % blocksize);
    (==) { }
    Seq.index (g (w * hi_fv + j / blocksize) (rem % blocksize) b1) (j % blocksize);
    }
#pop-options


val ctr_map_blocks_vec_equiv_pre_k:
    #w:width_t
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:size_nat{w * hi_fv + w <= max_size_t} // n == hi_fv == len / (w * blocksize)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq uint8 rem
  -> j:nat{j < rem} ->
  Lemma
   (let st_v0 = init_v #w k n c0 in
    let st0 = init k n c0 in
    let g_v = encrypt_last_v st_v0 in
    let f = encrypt_block st0 in
    let g = encrypt_last st0 in
    VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j)

let ctr_map_blocks_vec_equiv_pre_k #w k n c0 hi_fv rem b_v j =
  if j < rem / blocksize * blocksize then
    ctr_map_blocks_vec_equiv_pre_k0 #w k n c0 hi_fv rem b_v j
  else
    ctr_map_blocks_vec_equiv_pre_k1 #w k n c0 hi_fv rem b_v j

////////////////////////
// End of proof of VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j
////////////////////////

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

  let hi_fv = length msg / blocksize_v in
  let hi_f = w * hi_fv in
  Classical.forall_intro_3 (ctr_map_multi_blocks_vec_equiv_pre_k #w k n c0 hi_fv hi_f);
  Classical.forall_intro_3 (ctr_map_blocks_vec_equiv_pre_k #w k n c0 hi_fv);
  VecLemmas.lemma_map_blocks_vec w blocksize msg hi_fv f g f_v g_v
