module Hacl.CTR.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Hacl.CTR.Lemmas +Lib.Sequence +FStar.Seq +Math.Lemmas'"


let get_block_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len})
  (i:nat{i < (len / blocksize) * blocksize}) :
  lseq a blocksize
=
  div_mul_lt blocksize i (len / blocksize);
  let j: block len blocksize = i / blocksize in
  let b: lseq a blocksize = Seq.slice inp (j * blocksize) ((j + 1) * blocksize) in
  b

let get_last_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len}) :
  lseq a (len % blocksize)
=
  let rem = len % blocksize in
  let b: lseq a rem = Seq.slice inp (len - rem) len in
  b


val lemma_i_div_bs: w:pos -> bs:pos -> i:nat ->
  Lemma (i / bs == w * (i / (w * bs)) + i % (w * bs) / bs)

val lemma_len_div_bs_v: w:pos -> bs:pos -> len:nat -> i:nat{len / (w * bs) * (w * bs) <= i /\ i < len} ->
  Lemma (len / (w * bs) == i / (w * bs))

val lemma_len_div_bs: w:pos -> bs:pos -> len:nat -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma (len / bs == i / bs)

val lemma_mod_bs_v_bs: a:nat -> w:pos -> bs:pos ->
  Lemma (a % (w * bs) % bs == a % bs)

val lemma_div_bs_v_le: a:nat -> w:pos -> bs:pos ->
  Lemma (a / (w * bs) * (w * bs) <= a / bs * bs)

val lemma_i_div_bs_lt: w:pos -> bs:pos -> len:nat -> i:nat -> Lemma
  (requires
    len / (w * bs) * (w * bs) <= i /\ i < len /\
    i % (w * bs) < (len % (w * bs) / bs) * bs)
  (ensures  i / bs < len / bs)

val lemma_i_mod_bs_lt: w:pos -> bs:pos -> len:nat -> i:nat -> Lemma
  (requires
    len / (w * bs) * (w * bs) <= i /\ i < len /\
    (len % (w * bs) / bs) * bs <= i % (w * bs) /\ i % (w * bs) < len % (w * bs))
  (ensures  i % bs < len % bs)


let map_blocks_vec_equiv_pre_f_v
  (#a:Type)
  (#len:nat)
  (w:size_pos)
  (blocksize:size_pos)
  (blocksize_v:size_pos{blocksize_v == w * blocksize})
  (f:(block len blocksize -> lseq a blocksize -> lseq a blocksize))
  (f_v:(block len blocksize_v -> lseq a blocksize_v -> lseq a blocksize_v))
  (i:nat{i < len / blocksize_v * blocksize_v})
  (b_v:lseq a blocksize_v)
  : prop
=
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = get_block_s #_ #blocksize_v blocksize b_v (i % blocksize_v) in
  lemma_div_bs_v_le len w blocksize;
  div_mul_lt blocksize i (len / blocksize);
  div_mul_lt blocksize_v i (len / blocksize_v);
  (f_v (i / blocksize_v) b_v).[i % blocksize_v] == (f (i / blocksize) b).[i % blocksize]


let map_blocks_vec_equiv_pre_g_v
  (#a:Type)
  (#len:nat)
  (w:size_pos)
  (blocksize:size_pos)
  (blocksize_v:size_pos{blocksize_v == w * blocksize})
  (f:(block len blocksize -> lseq a blocksize -> lseq a blocksize))
  (g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (g_v:(last len blocksize_v -> rem:size_nat{rem < blocksize_v} -> lseq a rem -> lseq a rem))
  (i:nat{len / blocksize_v * blocksize_v <= i /\ i < len})
  (b_v:lseq a (len % blocksize_v))
  : prop
=
  let rem_v = len % blocksize_v in
  let rem = len % blocksize in
  lemma_mod_bs_v_bs len w blocksize;
  assert (rem_v % blocksize = rem);

  let j = i % blocksize_v in
  let gv_b = g_v (len / blocksize_v) rem_v b_v in

  if j < (rem_v / blocksize) * blocksize then begin
    let b = get_block_s #a #rem_v blocksize b_v j in
    lemma_i_div_bs_lt w blocksize len i;
    let f_b = f (i / blocksize) b in
    (gv_b).[j] == f_b.[i % blocksize] end
  else begin
    let b : lseq a rem = get_last_s #a #rem_v blocksize b_v in
    let g_b : lseq a rem = g (len / blocksize) rem b in
    mod_div_lt blocksize_v i len;
    assert (i % blocksize_v < len % blocksize_v);
    lemma_i_mod_bs_lt w blocksize len i;
    (gv_b).[j] == g_b.[i % blocksize] end


val lemma_map_blocks_multi_vec:
     #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp == len /\ len % (w * blocksize) == 0 /\ len % blocksize == 0}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize)) ->
  Lemma
  (requires
   (Math.Lemmas.div_exact_r len (w * blocksize);
    forall (i:nat{i < len}) (b_v:lseq a (w * blocksize)).
     map_blocks_vec_equiv_pre_f_v #a #len w blocksize (w * blocksize) f f_v i b_v))
  (ensures
   (let blocksize_v = w * blocksize in
    let nb_v = len / blocksize_v in
    let nb = len / blocksize in

    map_blocks_multi blocksize_v nb_v nb_v inp f_v `Seq.equal`
    map_blocks_multi blocksize nb nb inp f))


val lemma_map_blocks_vec:
     #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp == len}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma
  (requires
   (let blocksize_v = w * blocksize in
    (forall (i:nat{i < len / blocksize_v * blocksize_v}) (b_v:lseq a blocksize_v).
      map_blocks_vec_equiv_pre_f_v #a #len w blocksize blocksize_v f f_v i b_v) /\
    (forall (i:nat{len / blocksize_v * blocksize_v <= i /\ i < len}) (b_v:lseq a (len % blocksize_v)).
      map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v)))
  (ensures
    map_blocks (w * blocksize) inp f_v g_v `Seq.equal`
    map_blocks blocksize inp f g)
