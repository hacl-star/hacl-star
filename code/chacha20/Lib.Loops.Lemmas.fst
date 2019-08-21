module Lib.Loops.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector


noextract
let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


inline_for_extraction noextract
val get_block_s:
    #a:Type0
  -> size_block:size_pos
  -> inp:Seq.seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / size_block} -> lseq a size_block -> lseq a size_block)
  -> i:nat{i < len / size_block * size_block} ->
  lseq a size_block

let get_block_s #a sb inp len f i =
  let j_s = i / sb in
  FStar.Math.Lemmas.cancel_mul_div (len / sb) sb;
  assert ((j_s + 1) * sb <= len);

  FStar.Seq.lemma_len_slice inp (j_s * sb) ((j_s + 1) * sb);
  let b_s : lseq a sb = Seq.slice inp (j_s * sb) ((j_s + 1) * sb) in
  f j_s b_s


inline_for_extraction noextract
val get_block_s_last:
    #a:Type0
  -> size_block:size_pos
  -> inp:Seq.seq a
  -> len:nat{len == length inp}
  -> g:(i:nat{i == len / size_block} -> rem:nat{rem < size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{len / size_block * size_block <= i /\ i < len} ->
  lseq a (len % size_block)

let get_block_s_last #a sb inp len g i =
  let rem = len % sb in
  FStar.Seq.lemma_len_slice inp (len - rem) len;
  let b_last : lseq a rem = Seq.slice inp (len - rem) len in
  g (len / sb) rem b_last


inline_for_extraction noextract
val get_block_vec:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f_vec:(i:nat{i < len / (w * size_block)} -> lseq a (w * size_block) -> lseq a (w * size_block))
  -> i:nat{i < len / (w * size_block) * (w * size_block)} ->
  lseq a (w * size_block)

let get_block_vec #a w size_block inp len f_vec i =
  let bs = w * size_block in
  let j_vec = i / bs in
  FStar.Math.Lemmas.lemma_div_le (i + 1) (len / bs * bs) bs;
  FStar.Math.Lemmas.cancel_mul_div (len / bs) bs;
  assert ((i + 1) / bs <= len / bs);
  assert (j_vec <= len / bs);
  assert ((j_vec + 1) * bs <= len);
  FStar.Seq.lemma_len_slice inp (j_vec * bs) ((j_vec + 1) * bs);
  let b_vec : lseq a bs = Seq.slice inp (j_vec * bs) ((j_vec + 1) * bs) in
  f_vec j_vec b_vec


inline_for_extraction noextract
val get_block_vec_last:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> g_vec:(i:nat{i == len / (w * size_block)} -> rem:nat{rem < w * size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{len / (w * size_block) * (w * size_block) <= i /\ i < len} ->
  lseq a (len % (w * size_block))

let get_block_vec_last #a w size_block inp len g_vec i =
  let bs = w * size_block in
  let rem = len % bs in
  FStar.Seq.lemma_len_slice inp (len - rem) len;
  let b_last : lseq a rem = Seq.slice inp (len - rem) len in
  g_vec (len / bs) rem b_last


val lemma_map_blocks_s_i:
    #a:Type0
  -> size_block:size_pos
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / size_block} -> lseq a size_block -> lseq a size_block)
  -> g:(i:nat{i == len / size_block} -> rem:nat{rem < size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len} ->
  Lemma
  (if i < len / size_block * size_block then
    Seq.index (map_blocks size_block inp f g) i ==
    Seq.index (get_block_s #a size_block inp len f i) (i % size_block)
   else begin
    FStar.Math.Lemmas.modulo_lemma (i - len / size_block * size_block) size_block;
    FStar.Math.Lemmas.lemma_mod_sub i size_block (len / size_block);
    Seq.index (map_blocks size_block inp f g) i ==
    Seq.index (get_block_s_last #a size_block inp len g i) (i % size_block) end)

let lemma_map_blocks_s_i #a size_block inp len f g i =
  index_map_blocks size_block inp f g i


val lemma_map_blocks_vec_i:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f_vec:(i:nat{i < len / (w * size_block)} -> lseq a (w * size_block) -> lseq a (w * size_block))
  -> g_vec:(i:nat{i == len / (w * size_block)} -> rem:nat{rem < w * size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len} ->
  Lemma
 (let bs = w * size_block in
  if i < len / bs * bs then
    Seq.index (map_blocks bs inp f_vec g_vec) i ==
    Seq.index (get_block_vec #a w size_block inp len f_vec i) (i % bs)
   else begin
    FStar.Math.Lemmas.modulo_lemma (i - len / bs * bs) bs;
    FStar.Math.Lemmas.lemma_mod_sub i bs (len / bs);
    Seq.index (map_blocks bs inp f_vec g_vec) i ==
    Seq.index (get_block_vec_last #a w size_block inp len g_vec i) (i % bs) end)

let lemma_map_blocks_vec_i #a w size_block inp len f_vec g_vec i =
  index_map_blocks (w * size_block) inp f_vec g_vec i


val map_blocks_vec_equiv_t:
    #a:Type0
  -> w:lanes
  -> sb:size_pos{w * sb <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / sb} -> lseq a sb -> lseq a sb)
  -> g:(i:nat{i == len / sb} -> rem:nat{rem < sb} -> lseq a rem -> lseq a rem)
  -> f_vec:(i:nat{i < len / (w * sb)} -> lseq a (w * sb) -> lseq a (w * sb))
  -> g_vec:(i:nat{i == len / (w * sb)} -> rem:nat{rem < w * sb} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len} ->
  Type0

let map_blocks_vec_equiv_t #a w sb inp len f g f_vec g_vec i =
  let sb_v = w * sb in
  if i < len / sb * sb then begin
    if i < len / sb_v * sb_v then
      Seq.index (get_block_vec #a w sb inp len f_vec i) (i % sb_v) ==
      Seq.index (get_block_s #a sb inp len f i) (i % sb)
    else begin
      FStar.Math.Lemmas.modulo_lemma (i - len / sb_v * sb_v) sb_v;
      FStar.Math.Lemmas.lemma_mod_sub i sb_v (len / sb_v);
      Seq.index (get_block_vec_last #a w sb inp len g_vec i) (i % sb_v) ==
      Seq.index (get_block_s #a sb inp len f i) (i % sb) end end
  else begin
    assert (i / sb_v * sb_v <= i /\ i < len);

    let lp = get_block_vec_last w sb inp len g_vec i in
    let rp = get_block_s_last sb inp len g i in
    Seq.index lp (i % sb_v) == Seq.index rp (i % sb) end


val lemma_map_blocks_vec_i_aux0:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / size_block} -> lseq a size_block -> lseq a size_block)
  -> g:(i:nat{i == len / size_block} -> rem:nat{rem < size_block} -> lseq a rem -> lseq a rem)
  -> f_vec:(i:nat{i < len / (w * size_block)} -> lseq a (w * size_block) -> lseq a (w * size_block))
  -> g_vec:(i:nat{i == len / (w * size_block)} -> rem:nat{rem < w * size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len / size_block * size_block} ->
  Lemma
  (requires
    map_blocks_vec_equiv_t #a w size_block inp len f g f_vec g_vec i)
  (ensures
    Seq.index (map_blocks (w * size_block) inp f_vec g_vec) i ==
    Seq.index (get_block_s #a size_block inp len f i) (i % size_block))

let lemma_map_blocks_vec_i_aux0 #a w size_block inp len f g f_vec g_vec i =
  lemma_map_blocks_vec_i #a w size_block inp len f_vec g_vec i


val lemma_map_blocks_vec_i_aux1:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / size_block} -> lseq a size_block -> lseq a size_block)
  -> g:(i:nat{i == len / size_block} -> rem:nat{rem < size_block} -> lseq a rem -> lseq a rem)
  -> f_vec:(i:nat{i < len / (w * size_block)} -> lseq a (w * size_block) -> lseq a (w * size_block))
  -> g_vec:(i:nat{i == len / (w * size_block)} -> rem:nat{rem < w * size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len /\ map_blocks_vec_equiv_t #a w size_block inp len f g f_vec g_vec i} ->
  Lemma
  (if i < len / size_block * size_block then
    Seq.index (map_blocks (w * size_block) inp f_vec g_vec) i ==
    Seq.index (get_block_s #a size_block inp len f i) (i % size_block)
  else begin
    FStar.Math.Lemmas.modulo_lemma (i - len / size_block * size_block) size_block;
    FStar.Math.Lemmas.lemma_mod_sub i size_block (len / size_block);
    Seq.index (map_blocks (w * size_block) inp f_vec g_vec) i ==
    Seq.index (get_block_s_last #a size_block inp len g i) (i % size_block) end)

let lemma_map_blocks_vec_i_aux1 #a w size_block inp len f g f_vec g_vec i =
  lemma_map_blocks_vec_i #a w size_block inp len f_vec g_vec i;
  if i < len / size_block * size_block then
    lemma_map_blocks_vec_i_aux0 #a w size_block inp len f g f_vec g_vec i
  else admit()


val lemma_map_blocks_vec_i_aux:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / size_block} -> lseq a size_block -> lseq a size_block)
  -> g:(i:nat{i == len / size_block} -> rem:nat{rem < size_block} -> lseq a rem -> lseq a rem)
  -> f_vec:(i:nat{i < len / (w * size_block)} -> lseq a (w * size_block) -> lseq a (w * size_block))
  -> g_vec:(i:nat{i == len / (w * size_block)} -> rem:nat{rem < w * size_block} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len /\ map_blocks_vec_equiv_t #a w size_block inp len f g f_vec g_vec i} ->
  Lemma
  (Seq.index (map_blocks (w * size_block) inp f_vec g_vec) i ==
   Seq.index (map_blocks size_block inp f g) i)

let lemma_map_blocks_vec_i_aux #a w size_block inp len f g f_vec g_vec i =
  lemma_map_blocks_s_i #a size_block inp len f g i;
  lemma_map_blocks_vec_i_aux1 #a w size_block inp len f g f_vec g_vec i


val lemma_map_blocks_vec:
    #a:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a
  -> len:nat{len == length inp}
  -> f:(i:nat{i < len / size_block} -> lseq a size_block -> lseq a size_block)
  -> g:(i:nat{i == len / size_block} -> rem:nat{rem < size_block} -> lseq a rem -> lseq a rem)
  -> f_vec:(i:nat{i < len / (w * size_block)} -> lseq a (w * size_block) -> lseq a (w * size_block))
  -> g_vec:(i:nat{i == len / (w * size_block)} -> rem:nat{rem < w * size_block} -> lseq a rem -> lseq a rem) ->
  Lemma
  (requires
    (forall (i:nat{i < len}). map_blocks_vec_equiv_t #a w size_block inp len f g f_vec g_vec i))
  (ensures
    Seq.equal (map_blocks (w * size_block) inp f_vec g_vec) (map_blocks size_block inp f g))

let lemma_map_blocks_vec #a w size_block inp len f g f_vec g_vec =
  Classical.forall_intro (lemma_map_blocks_vec_i_aux #a w size_block inp len f g f_vec g_vec);
  Seq.lemma_eq_intro (map_blocks (w * size_block) inp f_vec g_vec) (map_blocks size_block inp f g)
