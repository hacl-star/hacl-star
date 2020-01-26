module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Lib.Sequence.Lemmas +Lib.Sequence +FStar.Seq'"

let get_block_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len})
  (i:nat{i < len / blocksize * blocksize}) :
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


///
/// Equivalence of (map_blocks blocksize) and (map_blocks (w * blocksize))
///

(*
   Conditions for (map_blocks blocksize len input f g)
   to be equivalent to (map_blocks (w * blocksize) len input f_v g_v)
*)
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
    (f (i / blocksize) b).[i % blocksize] == gv_b.[j] end
  else begin
    let b : lseq a rem = get_last_s #a #rem_v blocksize b_v in
    mod_div_lt blocksize_v i len;
    assert (i % blocksize_v < len % blocksize_v);
    lemma_i_mod_bs_lt w blocksize len i;
    (g (len / blocksize) rem b).[i % blocksize] == gv_b.[j] end


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
    map_blocks (w * blocksize) inp f_v g_v `Seq.equal` map_blocks blocksize inp f g)


///
///  Special case of the lemma_map_blocks_vec lemma which is used in the CTR mode
///

unfold
let block_ctr (len:nat) (blocksize:size_pos) = i:nat{i <= len / blocksize}

let f_last_ctr (#a:Type0) (#len:nat)
  (blocksize:size_pos)
  (f:(block_ctr len blocksize -> lseq a blocksize -> lseq a blocksize))
  (zero:a)
  (c:block_ctr len blocksize)
  (rem:nat{rem < blocksize})
  (r:lseq a rem) : lseq a rem
 =
  let b = create blocksize zero in
  let b = update_sub b 0 rem r in
  sub (f c b) 0 rem

let map_blocks_ctr (#a:Type0)
  (blocksize:size_pos)
  (inp:seq a{length inp / blocksize <= max_size_t})
  (f:(block_ctr (length inp) blocksize -> lseq a blocksize -> lseq a blocksize))
  (zero:a) : out:seq a{length out == length inp}
 =
  map_blocks blocksize inp f (f_last_ctr #a #(length inp) blocksize f zero)


let map_blocks_ctr_vec_equiv_pre
  (#a:Type)
  (#len:nat)
  (w:size_pos)
  (blocksize:size_pos)
  (blocksize_v:size_pos{blocksize_v == w * blocksize})
  (f:(block_ctr len blocksize -> lseq a blocksize -> lseq a blocksize))
  (f_v:(block_ctr len blocksize_v -> lseq a blocksize_v -> lseq a blocksize_v))
  (i:nat{i <= len})
  (b_v:lseq a blocksize_v)
  : prop
=
  Math.Lemmas.modulo_range_lemma i blocksize_v;
  Math.Lemmas.multiple_division_lemma w blocksize;
  let b = get_block_s #_ #blocksize_v blocksize b_v (i % blocksize_v) in
  Math.Lemmas.lemma_div_le i len blocksize;
  Math.Lemmas.lemma_div_le i len blocksize_v;
  (f_v (i / blocksize_v) b_v).[i % blocksize_v] == (f (i / blocksize) b).[i % blocksize]


val lemma_map_blocks_ctr_vec:
     #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp == len /\ len / blocksize <= max_size_t /\ len / (w * blocksize) <= max_size_t}
  -> f:(block_ctr len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(block_ctr len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> zero:a ->
  Lemma
  (requires
    (forall (i:nat{i <= len}) (b_v:lseq a (w * blocksize)).
      map_blocks_ctr_vec_equiv_pre #a #len w blocksize (w * blocksize) f f_v i b_v))
  (ensures
    map_blocks_ctr (w * blocksize) inp f_v zero `Seq.equal` map_blocks_ctr blocksize inp f zero)


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val repeati_extensionality:
    #a:Type0
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures  (Loops.repeati n f acc0 == Loops.repeati n g acc0))


val repeati_right_extensionality:
    #a:Type
  -> n:nat
  -> lo_g:nat
  -> hi_g:nat{lo_g + n <= hi_g}
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{lo_g <= i /\ i < hi_g} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (lo_g + i) acc))
  (ensures (Loops.repeat_right 0 n (Loops.fixed_a a) f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0))


val repeat_blocks_multi_split:
     #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
    assert (len % blocksize == (len - len0) % blocksize);
    repeat_blocks_multi blocksize inp f acc0 ==
    repeat_blocks_multi blocksize (Seq.slice inp len0 len) f
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))


val repeat_blocks_split:
     #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
    assert (len % blocksize == (len - len0) % blocksize);
    repeat_blocks blocksize inp f l acc0 ==
    repeat_blocks blocksize (Seq.slice inp len0 len) f l
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))

noextract
let lanes = w:size_pos{w == 1 \/ w == 2 \/ w == 4}


noextract
let repeat_w (#a:Type0) (w:lanes) (n:nat) (f:(i:nat{i < w * n} -> a -> a)) (i:nat{i < n}) (acc:a) : Tot a =
  match w with
  | 1 -> f i acc
  | 2 -> f (2*i+1) (f (2*i) acc)
  | 4 -> f (4*i+3) (f (4*i+2) (f (4*i+1) (f (4*i) acc)))


val unfold_repeatw:
    #a:Type0
  -> w:lanes
  -> n:pos
  -> f:(i:nat{i < w * n} -> a -> a)
  -> acc0:a ->
  Lemma (Loops.repeati (w*n) f acc0 == repeat_w w n f (n-1) (Loops.repeati (w*(n-1)) f acc0))


val lemma_repeati_vec:
    #a:Type0
  -> #a_vec:Type0
  -> w:lanes
  -> n:nat
  -> normalize_n:(a_vec -> a)
  -> f:(i:nat{i < n * w} -> a -> a)
  -> f_vec:(i:nat{i < n} -> a_vec -> a_vec)
  -> acc0_vec:a_vec ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_vec:a_vec). normalize_n (f_vec i acc_vec) == repeat_w w n f i (normalize_n acc_vec)))
  (ensures  (normalize_n (Loops.repeati n f_vec acc0_vec) == Loops.repeati (w * n) f (normalize_n acc0_vec)))


private
val lemma_aux1: w:pos -> blocksize:pos -> len:pos ->
  Lemma
  (requires (w * blocksize <= len /\ len % (w * blocksize) = 0 /\ len % blocksize = 0))
  (ensures  ((len - w * blocksize) / blocksize == w * ((len - w * blocksize) / (w * blocksize))))


#set-options "--initial_ifuel 1 --max_ifuel 1"

val lemma_repeat_blocks_multi_vec:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:lanes
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{w * blocksize <= length inp /\ length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> f_vec:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_n:(b_vec -> b)
  -> load_acc:(lseq a (w * blocksize) -> b -> b_vec)
  -> acc0:b ->
  Lemma
  (requires
   (let len = length inp in
    let len0 = w * blocksize in
    let len1 = len - len0 in
    FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
    assert (len % len0 == len1 % len0);
    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    let nb_vec = len1 / (w * blocksize) in
    let nb = len1 / blocksize in
    lemma_aux1 w blocksize len;
    assert (nb == w * nb_vec);
    let repeat_bf_vec = repeat_blocks_f (w * blocksize) t1 f_vec nb_vec in
    let repeat_bf_t0 = repeat_blocks_f blocksize t0 f w in
    let repeat_bf_t1 = repeat_blocks_f blocksize t1 f nb in

    normalize_n (load_acc t0 acc0) == repeat_w #b w 1 repeat_bf_t0 0 acc0 /\
    (forall (i:nat{i < nb_vec}) (acc_vec:b_vec).
      normalize_n (repeat_bf_vec i acc_vec) == repeat_w #b w nb_vec repeat_bf_t1 i (normalize_n acc_vec))))
  (ensures
   (let len = length inp in
    let len0 = w * blocksize in
    FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
    assert (len % len0 == (len - len0) % len0);

    let acc_vec = load_acc (Seq.slice inp 0 len0) acc0 in
    normalize_n (repeat_blocks_multi #a #b_vec (w * blocksize) (Seq.slice inp len0 len) f_vec acc_vec) ==
    repeat_blocks_multi #a #b blocksize inp f acc0))
