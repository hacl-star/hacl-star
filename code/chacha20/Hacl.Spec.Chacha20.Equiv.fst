module Hacl.Spec.Chacha20.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Scalar = Spec.Chacha20
module Lemmas = Hacl.Spec.Chacha20.Vec.Lemmas
module Loops = Lib.LoopCombinators

open Hacl.Spec.Chacha20.Vec

#reset-options "--z3rlimit 100 --max_fuel 0"

val lemma_i_div_bs_mul_w:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> len:size_nat
  -> i:nat{i < len} ->
  Lemma (i / bs * w <= max_size_t)
let lemma_i_div_bs_mul_w w bs len i = ()

val lemma_i_mod_bs_div_sb:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> i:nat ->
  Lemma ((i % bs) / size_block < w)
let lemma_i_mod_bs_div_sb w bs i = ()

val lemma_slice_slice_msg:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> i:nat ->
  Lemma (i / bs * bs + (i % bs) / size_block * size_block == i / size_block * size_block)
let lemma_slice_slice_msg w bs i = ()

val lemma_slice_slice_msg1:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> i:nat ->
  Lemma (i / bs * bs + ((i % bs) / size_block + 1) * size_block == (i / size_block + 1) * size_block)
let lemma_slice_slice_msg1 w bs i = ()

val lemma_bs_mod_sb_mod:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> i:nat ->
  Lemma (i % bs % size_block == i % size_block)
let lemma_bs_mod_sb_mod w bs i = ()

val lemma_i_div_sb:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> i:nat ->
  Lemma (w * (i / bs) + (i % bs) / size_block == i / size_block)
let lemma_i_div_sb w bs i = ()

val lemma_equiv_g_i_aux1:
    w:lanes
  -> len:nat
  -> bs:nat{bs == w * size_block}
  -> i:nat{len / bs * bs <= i /\ i < len /\ i % bs < (len % bs / size_block) * size_block} ->
  Lemma ((i / size_block + 1) * size_block <= len)
let lemma_equiv_g_i_aux1 w len bs i = ()

val lemma_equiv_g_i_aux2:
    w:lanes
  -> len:nat
  -> bs:nat{bs == w * size_block}
  -> i:nat{len / bs * bs <= i /\ i < len /\ i % bs >= (len % bs / size_block) * size_block} ->
  Lemma (len / size_block * size_block <= i)
let lemma_equiv_g_i_aux2 w len bs i = ()

val lemma_slice_slice_msg2:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> len:nat
  -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma (len / bs * bs + (i % bs) / size_block * size_block == i / size_block * size_block)
let lemma_slice_slice_msg2 w bs len i =
  assert (len / bs * bs == i / bs * bs);
  lemma_slice_slice_msg w bs i

val lemma_slice_slice_msg3:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> len:nat
  -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma (len / bs * bs + ((i % bs) / size_block + 1) * size_block == (i / size_block + 1) * size_block)
let lemma_slice_slice_msg3 w bs len i =
  assert (len / bs * bs == i / bs * bs);
  lemma_slice_slice_msg1 w bs i

val lemma_i_div_sb1:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> len:nat
  -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma (w * (len / bs) + i % bs / size_block == i / size_block)
let lemma_i_div_sb1 w bs len i = ()

val lemma_len_div_sb:
    w:lanes
  -> bs:nat{bs == w * size_block}
  -> len:nat ->
  Lemma (w * (len / bs) + len % bs / size_block == len / size_block)
let lemma_len_div_sb w bs len = ()

val chacha20_update_scalar_lemma_i:
    ctx:Scalar.state
  -> msg:bytes{length msg <= max_size_t}
  -> i:nat{i < length msg} ->
  Lemma (
    let len = length msg in
    let nb = len / size_block in
    let rem = len % size_block in
    let last = Seq.slice msg (nb * size_block) len in

    if i < nb * size_block then begin
      let j = i / size_block in
      let b_j = Seq.slice msg (j*size_block) ((j+1)*size_block) in
      Seq.index (Scalar.chacha20_update ctx msg) i ==
      Seq.index (Scalar.chacha20_encrypt_block ctx j b_j) (i % size_block) end
    else begin
      Seq.index (Scalar.chacha20_update ctx msg) i ==
      Seq.index (Scalar.chacha20_encrypt_last ctx nb rem last) (i % size_block) end)
let chacha20_update_scalar_lemma_i ctx msg i =
  index_map_blocks #uint8 size_block msg
    (Scalar.chacha20_encrypt_block ctx)
    (Scalar.chacha20_encrypt_last ctx) i

#reset-options "--z3rlimit 50 --max_fuel 0 --using_facts_from '* -FStar.Seq'"

val chacha20_update_vector_lemma_i:
    #w:lanes
  -> st0:state w
  -> msg:bytes{length msg <= max_size_t}
  -> i:nat{i < length msg} ->
  Lemma (
    let len = length msg in
    let bs = w * size_block in
    let nb = len / bs in
    let rem = len % bs in
    FStar.Seq.lemma_len_slice msg (nb * bs) len;
    let last : lseq uint8 rem = Seq.slice msg (nb * bs) len in

    lemma_i_div_bs_mul_w w bs len i;
    //assert (i / bs * w <= max_size_t);
    if i < nb * bs then begin
      FStar.Math.Lemmas.cancel_mul_div nb bs;
      let j: j:nat{j < nb} = i / bs in
      FStar.Seq.lemma_len_slice msg (j*bs) ((j+1)*bs);
      let b_j : lseq uint8 bs = Seq.slice msg (j*bs) ((j+1)*bs) in
      Seq.index (chacha20_update st0 msg) i ==
      Seq.index (chacha20_encrypt_block st0 j b_j) (i % bs) end
    else begin
      FStar.Math.Lemmas.modulo_lemma (i - nb * bs) bs;
      FStar.Math.Lemmas.lemma_mod_sub i bs nb;
      Seq.index (chacha20_update st0 msg) i ==
      Seq.index (chacha20_encrypt_last st0 nb rem last) (i % bs) end)
let chacha20_update_vector_lemma_i #w st0 msg i =
  index_map_blocks (w * size_block) msg
    (chacha20_encrypt_block st0)
    (chacha20_encrypt_last st0) i

val chacha20_update_vector_lemma_equiv_f_i_aux:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> i:nat{i < length msg / (w * size_block) * (w * size_block)} ->
  Lemma (
    let len = length msg in
    let bs = w * size_block in

    let j = i / bs in
    FStar.Seq.lemma_len_slice msg (j*bs) ((j+1)*bs);
    let b_j : lseq uint8 bs = Seq.slice msg (j*bs) ((j+1)*bs) in
    let j_s = i / size_block in
    FStar.Seq.lemma_len_slice msg (j_s*size_block) ((j_s+1)*size_block);
    let b_j_s : lseq uint8 size_block = Seq.slice msg (j_s*size_block) ((j_s+1)*size_block) in

    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    Seq.index (chacha20_encrypt_block st0 j b_j) (i % bs) ==
    Seq.index (Scalar.chacha20_encrypt_block ctx j_s b_j_s) (i % size_block))
let chacha20_update_vector_lemma_equiv_f_i_aux #w k n ctr0 msg i =
  let len = length msg in
  let bs = w * size_block in

  let j = i / bs in
  FStar.Seq.lemma_len_slice msg (j*bs) ((j+1)*bs);
  let b_j : lseq uint8 bs = Seq.slice msg (j*bs) ((j+1)*bs) in
  let i1 = i % bs in
  Lemmas.chacha20_encrypt_block_equiv_lemma_index #w k n ctr0 j b_j i1;

  let j1 = i1 / size_block in
  lemma_i_mod_bs_div_sb w bs i;
  assert (j1 < w);
  FStar.Seq.lemma_len_slice b_j (j1*size_block) ((j1+1)*size_block);
  let b_j1 = Seq.slice b_j (j1*size_block) ((j1+1)*size_block) in
  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  assert (
    Seq.index (chacha20_encrypt_block st0 j b_j) i1 ==
    Seq.index (Scalar.chacha20_encrypt_block ctx (w * j + j1) b_j1) (i1 % size_block));

  lemma_bs_mod_sb_mod w bs i;
  assert (i1 % size_block == i % size_block);
  assert (
    Seq.index (chacha20_encrypt_block st0 j b_j) i1 ==
    Seq.index (Scalar.chacha20_encrypt_block ctx (w * j + j1) b_j1) (i % size_block));

  let j_s = i / size_block in
  lemma_slice_slice_msg w bs i;
  //assert (j*bs+j1*size_block==j_s*size_block);
  lemma_slice_slice_msg1 w bs i;
  //assert (j*bs+(j1+1)*size_block==(j_s+1)*size_block);
  FStar.Seq.slice_slice msg (j*bs) ((j+1)*bs) (j1*size_block) ((j1+1)*size_block);
  FStar.Seq.lemma_len_slice msg (j_s*size_block) ((j_s+1)*size_block);
  let b_j_s = Seq.slice msg (j_s*size_block) ((j_s+1)*size_block) in
  assert (b_j_s == b_j1);
  lemma_i_div_sb w bs i

val chacha20_update_vector_lemma_equiv_f_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> i:nat{i < length msg / (w * size_block) * (w * size_block)} ->
  Lemma (
    let len = length msg in
    let bs = w * size_block in
    let nb = len / bs in
    let j = i / size_block in
    FStar.Seq.lemma_len_slice msg (j*size_block) ((j+1)*size_block);
    let b_j : lseq uint8 size_block = Seq.slice msg (j*size_block) ((j+1)*size_block) in

    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    Seq.index (chacha20_update st0 msg) i ==
    Seq.index (Scalar.chacha20_encrypt_block ctx j b_j) (i % size_block))
let chacha20_update_vector_lemma_equiv_f_i #w k n ctr0 msg i =
  let st0 = chacha20_init #w k n ctr0 in
  chacha20_update_vector_lemma_i #w st0 msg i;
  chacha20_update_vector_lemma_equiv_f_i_aux #w k n ctr0 msg i

val chacha20_update_vector_lemma_equiv_g_f_i_aux:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> bs:nat{bs == w * size_block}
  -> i:nat{length msg / bs * bs <= i /\ i < length msg /\ i % bs < (length msg % bs) / size_block * size_block} ->
  Lemma (
    let len = length msg in
    let nb_v = len / bs in
    let rem_v = len % bs in
    FStar.Seq.lemma_len_slice msg (nb_v * bs) len;
    let last_v : lseq uint8 rem_v = Seq.slice msg (nb_v * bs) len in

    let j_s = i / size_block in
    lemma_equiv_g_i_aux1 w len bs i;
    //assert ((j_s+1)*size_block <= len);
    FStar.Seq.lemma_len_slice msg (j_s*size_block) ((j_s+1)*size_block);
    let b_j_s = Seq.slice msg (j_s*size_block) ((j_s+1)*size_block) in

    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    Seq.index (chacha20_encrypt_last st0 nb_v rem_v last_v) (i % bs) ==
    Seq.index (Scalar.chacha20_encrypt_block ctx j_s b_j_s) (i % size_block))
let chacha20_update_vector_lemma_equiv_g_f_i_aux #w k n ctr0 msg bs i =
  let len = length msg in
  let nb_v = len / bs in
  let rem_v = len % bs in
  FStar.Seq.lemma_len_slice msg (nb_v * bs) len;
  let last_v : lseq uint8 rem_v = Seq.slice msg (nb_v * bs) len in

  let j = i % bs in
  FStar.Math.Lemmas.modulo_lemma (i - nb_v * bs) bs;
  FStar.Math.Lemmas.lemma_mod_sub i bs nb_v;
  assert (j < rem_v);

  let nb_s = rem_v / size_block in
  assert (j < nb_s * size_block);
  let j1 = j / size_block in
  FStar.Seq.lemma_len_slice last_v (j1*size_block) ((j1+1)*size_block);
  let b_j1 : lseq uint8 size_block = Seq.slice last_v (j1*size_block) ((j1+1)*size_block) in

  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  Lemmas.chacha20_encrypt_last_equiv_lemma_index #w k n ctr0 nb_v rem_v last_v j;
  //assert (
    //Seq.index (chacha20_encrypt_last st0 nb_v rem_v last_v) j ==
    //Seq.index (Scalar.chacha20_encrypt_block ctx (w * nb_v + j1) b_j1) (j % size_block));

  lemma_bs_mod_sb_mod w bs i;
  assert (j % size_block == i % size_block);

  assert (
    Seq.index (chacha20_encrypt_last st0 nb_v rem_v last_v) j ==
    Seq.index (Scalar.chacha20_encrypt_block ctx (w * nb_v + j1) b_j1) (i % size_block));

  let j_s = i / size_block in
  lemma_slice_slice_msg2 w bs len i;
  //assert (nb_v * bs + j1 * size_block == j_s * size_block);
  lemma_slice_slice_msg3 w bs len i;
  //assert (nb_v * bs + (j1+1) * size_block == (j_s+1)* size_block);
  FStar.Seq.slice_slice msg (nb_v * bs) len (j1*size_block) ((j1+1)*size_block);
  FStar.Seq.lemma_len_slice msg (j_s*size_block) ((j_s+1)*size_block);
  let b_j_s = Seq.slice msg (j_s*size_block) ((j_s+1)*size_block) in
  assert (b_j_s == b_j1);
  lemma_i_div_sb1 w bs len i
  //assert (w * nb_v + j1 == j_s);

#push-options "--z3rlimit 100"
val chacha20_update_vector_lemma_equiv_g_f_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> bs:nat{bs == w * size_block}
  -> i:nat{length msg / bs * bs <= i /\ i < length msg /\ i % bs < (length msg % bs) / size_block * size_block} ->
  Lemma (
    let len = length msg in
    let j_s = i / size_block in
    FStar.Seq.lemma_len_slice msg (j_s*size_block) ((j_s+1)*size_block);
    let b_j_s = Seq.slice msg (j_s*size_block) ((j_s+1)*size_block) in

    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    Seq.index (chacha20_update st0 msg) i ==
    Seq.index (Scalar.chacha20_encrypt_block ctx j_s b_j_s) (i % size_block))
let chacha20_update_vector_lemma_equiv_g_f_i #w k n ctr0 msg bs i =
  let st0 = chacha20_init #w k n ctr0 in
  chacha20_update_vector_lemma_i #w st0 msg i;
  chacha20_update_vector_lemma_equiv_g_f_i_aux #w k n ctr0 msg bs i
#pop-options

#push-options "--z3rlimit 100"
val chacha20_update_vector_lemma_equiv_g_g_i_aux:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> bs:nat{bs == w * size_block}
  -> i:nat{length msg / bs * bs <= i /\ i < length msg /\ i % bs >= (length msg % bs) / size_block * size_block} ->
  Lemma (
    let len = length msg in
    let nb_v = len / bs in
    let rem_v = len % bs in
    FStar.Seq.lemma_len_slice msg (nb_v * bs) len;
    let last_v : lseq uint8 rem_v = Seq.slice msg (nb_v * bs) len in

    let nb = len / size_block in
    let rem = len % size_block in
    FStar.Seq.lemma_len_slice msg (nb * size_block) len;
    let last = Seq.slice msg (nb * size_block) len in

    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    lemma_equiv_g_i_aux2 w len bs i;
    //assert (nb * size_block <= i /\ i < length msg);
    FStar.Math.Lemmas.modulo_lemma (i - nb * size_block) size_block;
    FStar.Math.Lemmas.lemma_mod_sub i size_block nb;

    FStar.Math.Lemmas.modulo_lemma (i - nb_v * bs) bs;
    FStar.Math.Lemmas.lemma_mod_sub i bs nb_v;
    Seq.index (chacha20_encrypt_last st0 nb_v rem_v last_v) (i % bs) ==
    Seq.index (Scalar.chacha20_encrypt_last ctx nb rem last) (i % size_block))
let chacha20_update_vector_lemma_equiv_g_g_i_aux #w k n ctr0 msg bs i =
  let len = length msg in
  let nb_v = len / bs in
  let rem_v = len % bs in
  FStar.Seq.lemma_len_slice msg (nb_v * bs) len;
  let last_v : lseq uint8 rem_v = Seq.slice msg (nb_v * bs) len in

  let j = i % bs in
  FStar.Math.Lemmas.modulo_lemma (i - nb_v * bs) bs;
  FStar.Math.Lemmas.lemma_mod_sub i bs nb_v;
  assert (j < rem_v);

  let nb_s = rem_v / size_block in
  let rem_s = rem_v % size_block in
  FStar.Seq.lemma_len_slice last_v (nb_s * size_block) rem_v;
  let last_s : lseq uint8 rem_s = Seq.slice last_v (nb_s * size_block) rem_v in

  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  Lemmas.chacha20_encrypt_last_equiv_lemma_index #w k n ctr0 nb_v rem_v last_v j;
  //assert (
    //Seq.index (chacha20_encrypt_last st0 nb_v rem_v last_v) j ==
    //Seq.index (Scalar.chacha20_encrypt_last ctx (w * nb_v + nb_s) rem_s last_s) (j % size_block));

  lemma_bs_mod_sb_mod w bs i;
  assert (j % size_block == i % size_block);

  assert (
    Seq.index (chacha20_encrypt_last st0 nb_v rem_v last_v) j ==
    Seq.index (Scalar.chacha20_encrypt_last ctx (w * nb_v + nb_s) rem_s last_s) (i % size_block));

  let nb = len / size_block in
  let rem = len % size_block in
  lemma_bs_mod_sb_mod w bs len;
  assert (rem == rem_s);

  lemma_slice_slice_msg w bs len;
  //assert (nb_v * bs + nb_s * size_block == nb * size_block);
  assert (nb_v * bs + rem_v = len);
  FStar.Seq.slice_slice msg (nb_v * bs) len (nb_s * size_block) rem_v;
  FStar.Seq.lemma_len_slice msg (nb*size_block) len;
  let last = Seq.slice msg (nb*size_block) len in
  assert (last_s == last);
  lemma_len_div_sb w bs len;
  assert (w * nb_v + nb_s == nb)
#pop-options

val chacha20_update_vector_lemma_equiv_g_g_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> bs:nat{bs == w * size_block}
  -> i:nat{length msg / bs * bs <= i /\ i < length msg /\ i % bs >= (length msg % bs) / size_block * size_block} ->
  Lemma (
    let len = length msg in
    let nb = len / size_block in
    let rem = len % size_block in
    FStar.Seq.lemma_len_slice msg (nb * size_block) len;
    let last = Seq.slice msg (nb * size_block) len in

    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    lemma_equiv_g_i_aux2 w len bs i;
    //assert (nb * size_block <= i /\ i < length msg);
    FStar.Math.Lemmas.modulo_lemma (i - nb * size_block) size_block;
    FStar.Math.Lemmas.lemma_mod_sub i size_block nb;
    Seq.index (chacha20_update st0 msg) i ==
    Seq.index (Scalar.chacha20_encrypt_last ctx nb rem last) (i % size_block))
let chacha20_update_vector_lemma_equiv_g_g_i #w k n ctr0 msg bs i =
  let st0 = chacha20_init #w k n ctr0 in
  chacha20_update_vector_lemma_i #w st0 msg i;
  chacha20_update_vector_lemma_equiv_g_g_i_aux #w k n ctr0 msg bs i

#push-options "--z3rlimit 100"
val chacha20_update_vector_lemma_equiv_join_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> st0:state w{st0 == chacha20_init #w k n ctr0}
  -> ctx:Scalar.state{ctx == Scalar.chacha20_init k n ctr0}
  -> msg:bytes{length msg <= max_size_t /\ ctr0 + w <= max_size_t}
  -> i:nat{i < length msg} ->
  Lemma (
    let len = length msg in
    let nb = len / size_block in
    let rem = len % size_block in
    FStar.Seq.lemma_len_slice msg (nb * size_block) len;
    let last = Seq.slice msg (nb * size_block) len in

    if i < nb * size_block then begin
      let j = i / size_block in
      FStar.Seq.lemma_len_slice msg (j*size_block) ((j+1)*size_block);
      let b_j : lseq uint8 size_block = Seq.slice msg (j*size_block) ((j+1)*size_block) in
      Seq.index (chacha20_update st0 msg) i ==
      Seq.index (Scalar.chacha20_encrypt_block ctx j b_j) (i % size_block) end
    else begin
      FStar.Math.Lemmas.modulo_lemma (i - nb * size_block) size_block;
      FStar.Math.Lemmas.lemma_mod_sub i size_block nb;
      Seq.index (chacha20_update st0 msg) i ==
      Seq.index (Scalar.chacha20_encrypt_last ctx nb rem last) (i % size_block) end)
let chacha20_update_vector_lemma_equiv_join_i #w k n ctr0 st0 ctx msg i =
  let len = length msg in
  let bs = w * size_block in
  assert (len == len / bs * bs + len % bs);
  let rem_v = len % bs in
  assert (rem_v == rem_v / size_block * size_block + rem_v % size_block);
  lemma_bs_mod_sb_mod w bs len;
  assert (rem_v % size_block == len % size_block);
  assert (len == len / bs * bs + rem_v / size_block * size_block + len % size_block);
  assert (len / size_block * size_block == len / bs * bs + rem_v / size_block * size_block);
  if i < len / size_block * size_block then begin
    if i < len / bs * bs then
      chacha20_update_vector_lemma_equiv_f_i #w k n ctr0 msg i
    else
      chacha20_update_vector_lemma_equiv_g_f_i #w k n ctr0 msg bs i end
  else
    chacha20_update_vector_lemma_equiv_g_g_i #w k n ctr0 msg bs i
#pop-options

#reset-options "--z3rlimit 100 --max_fuel 0"

val chacha20_encrypt_bytes_lemma_equiv:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:bytes{length msg <= max_size_t /\ c + w <= max_size_t}
  -> Lemma (
      chacha20_encrypt_bytes #w k n c msg == Scalar.chacha20_encrypt_bytes k n c msg)
let chacha20_encrypt_bytes_lemma_equiv #w key nonce ctr0 msg =
  let st0 = chacha20_init #w key nonce ctr0 in
  let ctx = Scalar.chacha20_init key nonce ctr0 in

  assert (chacha20_encrypt_bytes #w key nonce ctr0 msg == chacha20_update st0 msg);
  assert (Scalar.chacha20_encrypt_bytes key nonce ctr0 msg == Scalar.chacha20_update ctx msg);

  Classical.forall_intro (chacha20_update_scalar_lemma_i ctx msg);
  Classical.forall_intro (chacha20_update_vector_lemma_equiv_join_i #w key nonce ctr0 st0 ctx msg);
  Seq.lemma_eq_intro
    (chacha20_update st0 msg)
    (Scalar.chacha20_update ctx msg)
