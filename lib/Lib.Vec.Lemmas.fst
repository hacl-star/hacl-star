module Lib.Vec.Lemmas


let rec lemma_repeat_gen_vec w n a a_vec normalize_v f f_v acc_v0 =
  let lp = Loops.repeat_right 0 n a_vec f_v acc_v0 in
  let rp = Loops.repeat_right 0 (w * n) a f (normalize_v 0 acc_v0) in
  if n = 0 then begin
    Loops.eq_repeat_right 0 n a_vec f_v acc_v0;
    Loops.eq_repeat_right 0 (w * n) a f (normalize_v 0 acc_v0);
    () end
  else begin
    lemma_repeat_gen_vec w (n - 1) a a_vec normalize_v f f_v acc_v0;
    let next_p = Loops.repeat_right 0 (n - 1) a_vec f_v acc_v0 in
    let next_v = Loops.repeat_right 0 (w * (n - 1)) a f (normalize_v 0 acc_v0) in
    assert (normalize_v (n - 1) next_p == next_v);
    Loops.unfold_repeat_right 0 n a_vec f_v acc_v0 (n - 1);
    assert (lp == f_v (n - 1) next_p);
    Loops.repeat_right_plus 0 (w * (n - 1)) (w * n) a f (normalize_v 0 acc_v0);
    assert (rp == Loops.repeat_right (w * (n - 1)) (w * n) a f next_v);
    assert (normalize_v n lp == Loops.repeat_right (w * (n - 1)) (w * n) a f next_v);
    () end


let lemma_repeati_vec #a #a_vec w n normalize_v f f_v acc_v0 =
  lemma_repeat_gen_vec w n (Loops.fixed_a a) (Loops.fixed_a a_vec) (Loops.fixed_i normalize_v) f f_v acc_v0;
  Loops.repeati_def n f_v acc_v0;
  Loops.repeati_def (w * n) f (normalize_v acc_v0)


val len_div_bs_w: w:pos -> blocksize:pos -> len:nat -> Lemma
  (requires len % (w * blocksize) = 0 /\ len % blocksize = 0)
  (ensures  len / blocksize == len / (w * blocksize) * w)

let len_div_bs_w w blocksize len =
  let blocksize_v = w * blocksize in
  calc (==) {
    len / blocksize;
    (==) { Math.Lemmas.lemma_div_exact len blocksize_v }
    (len / blocksize_v * blocksize_v) / blocksize;
    (==) { Math.Lemmas.paren_mul_right (len / blocksize_v) w blocksize }
    ((len / blocksize_v * w) * blocksize) / blocksize;
    (==) { Math.Lemmas.multiple_division_lemma (len / blocksize_v * w) blocksize }
    len / blocksize_v * w;
  }


val len_div_bs_w_n: w:pos -> blocksize:pos -> n:nat -> Lemma
  (let len = n * (w * blocksize) in
   len / blocksize == len / (w * blocksize) * w /\
   len % blocksize == 0 /\ len % (w * blocksize) = 0)

let len_div_bs_w_n w blocksize n =
  let len = n * (w * blocksize) in
  Math.Lemmas.cancel_mul_mod n (w * blocksize);
  assert (len % (w * blocksize) = 0);

  calc (==) {
    n * (w * blocksize) % blocksize;
    (==) { Math.Lemmas.paren_mul_right n w blocksize }
    n * w * blocksize % blocksize;
    (==) { Math.Lemmas.cancel_mul_mod (n * w) blocksize }
    0;
  };
  len_div_bs_w w blocksize len



////////////////////////
// Start of proof of lemma_repeat_gen_blocks_multi_vec
////////////////////////

// val repeat_gen_blocks_slice:
//     #inp_t:Type0
//   -> w:size_pos
//   -> blocksize:size_pos{w * blocksize <= max_size_t}
//   -> n:nat
//   -> hi_f:nat{w * n <= hi_f}
//   -> inp:seq inp_t{length inp == n * (w * blocksize)}
//   -> a:(i:nat{i <= hi_f} -> Type)
//   -> a_vec:(i:nat{i <= n} -> Type)
//   -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a i -> a (i + 1))
//   -> f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1))
//   -> i:nat{i < n}
//   -> acc:a (w * i) ->
//   Lemma
//    (len_div_bs_w_n w blocksize n;
//     let blocksize_v = w * blocksize in
//     Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) n;
//     let b_v = Seq.slice inp (i * blocksize_v) ((i + 1) * blocksize_v) in

//     Math.Lemmas.lemma_mult_le_right w (i + 1) n;
//     let f_rep_s = repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f in
//     let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in

//     Loops.repeat_right (w * i) (w * i + w) a f_rep acc ==
//     Loops.repeat_right (w * i) (w * i + w) a f_rep_s acc)

// let repeat_gen_blocks_slice #inp_t w blocksize n hi_f inp a a_vec f f_v i acc =
//   admit()


// val repeat_gen_blocks_multi_vec_step:
//     #inp_t:Type0
//   -> w:size_pos
//   -> blocksize:size_pos{w * blocksize <= max_size_t}
//   -> n:nat
//   -> hi_f:nat{w * n <= hi_f}
//   -> inp:seq inp_t{length inp == n * (w * blocksize)}
//   -> a:(i:nat{i <= hi_f} -> Type)
//   -> a_vec:(i:nat{i <= n} -> Type)
//   -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a i -> a (i + 1))
//   -> f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1))
//   -> normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i))
//   -> pre:squash(forall (i:nat{i < n}) (b_v:lseq inp_t (w * blocksize)) (acc_v:a_vec i).
//       repeat_gen_blocks_multi_vec_equiv_pre w blocksize n hi_f a a_vec f f_v normalize_v i b_v acc_v)
//   -> i:nat{i < n}
//   -> acc_v:a_vec i ->
//   Lemma
//    (let blocksize_v = w * blocksize in
//     len_div_bs_w_n w blocksize n;

//     let f_rep_v = repeat_gen_blocks_f blocksize_v 0 n n inp a_vec f_v in
//     let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in
//     Math.Lemmas.lemma_mult_le_right w (i + 1) n;

//     normalize_v (i + 1) (f_rep_v i acc_v) ==
//     Loops.repeat_right (w * i) (w * i + w) a f_rep (normalize_v i acc_v))

// let repeat_gen_blocks_multi_vec_step #inp_t w blocksize n hi_f inp a a_vec f f_v normalize_v pre i acc_v = admit();
//   let blocksize_v = w * blocksize in
//   len_div_bs_w_n w blocksize n;

//   let f_rep_v = repeat_gen_blocks_f blocksize_v 0 n n inp a_vec f_v in
//   let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in
//   Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) n;
//   let b_v = Seq.slice inp (i * blocksize_v) ((i + 1) * blocksize_v) in

//   Math.Lemmas.lemma_mult_le_right w (i + 1) n;
//   Math.Lemmas.cancel_mul_mod w blocksize;
//   Math.Lemmas.cancel_mul_div w blocksize;

//   calc (==) {
//     normalize_v (i + 1) (f_rep_v i acc_v);
//     (==) { }
//     normalize_v (i + 1) (f_v i b_v acc_v);
//     (==) { assert (repeat_gen_blocks_multi_vec_equiv_pre w blocksize n hi_f a a_vec f f_v normalize_v i b_v acc_v) }
//     repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v a f (normalize_v i acc_v);
//     (==) { lemma_repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v a f (normalize_v i acc_v) }
//     Loops.repeat_right (w * i) (w * i + w) a (repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f) (normalize_v i acc_v);
//     (==) { repeat_gen_blocks_slice #inp_t w blocksize n hi_f inp a a_vec f f_v normalize_v i acc_v }
//     Loops.repeat_right (w * i) (w * i + w) a f_rep (normalize_v i acc_v);
//   }


let lemma_repeat_gen_blocks_multi_vec #inp_t w blocksize n hi_f inp a a_vec f f_v normalize_v acc_v0 = admit()
  // let len = length inp in
  // let blocksize_v = w * blocksize in

  // let nb = len / blocksize in
  // len_div_bs_w_n w blocksize n;

  // let f_rep_v = repeat_gen_blocks_f blocksize_v 0 n n inp a_vec f_v in
  // let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in

  // calc (==) {
  //   normalize_v n (repeat_gen_blocks_multi blocksize_v 0 n n inp a_vec f_v acc_v0);
  //   (==) { lemma_repeat_gen_blocks_multi blocksize_v 0 n n inp a_vec f_v acc_v0 }
  //   normalize_v n (Loops.repeat_right 0 n a_vec f_rep_v acc_v0);
  //   (==) { Classical.forall_intro_2 (repeat_gen_blocks_multi_vec_step w blocksize n hi_f inp a a_vec f f_v normalize_v ());
  //          lemma_repeat_gen_vec w n a a_vec normalize_v f_rep f_rep_v acc_v0 }
  //   Loops.repeat_right 0 (w * n) a f_rep (normalize_v 0 acc_v0);
  //   (==) { lemma_repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp a f (normalize_v 0 acc_v0) }
  //   repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp a f (normalize_v 0 acc_v0);
  //   (==) { repeat_gen_blocks_multi_extensionality_zero blocksize 0 (w * n) hi_f (w * n) inp a a f f (normalize_v 0 acc_v0) }
  //   repeat_gen_blocks_multi blocksize 0 hi_f (w * n) inp a f (normalize_v 0 acc_v0);
  // }


////////////////////////
// End of proof of lemma_repeat_gen_blocks_multi_vec
////////////////////////

let lemma_repeat_gen_blocks_vec #inp_t #c w blocksize inp n a a_vec f l f_v l_v normalize_v acc_v0 =
  let len = length inp in
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let rem_v = len % blocksize_v in

  let res_v = repeat_gen_blocks blocksize_v 0 n inp a_vec f_v l_v acc_v0 in
  lemma_repeat_gen_blocks blocksize_v 0 n inp a_vec f_v l_v acc_v0;

  let blocks_v = Seq.slice inp 0 (nb_v * blocksize_v) in
  let last_v = Seq.slice inp (nb_v * blocksize_v) len in
  Math.Lemmas.cancel_mul_div nb_v blocksize_v;
  Math.Lemmas.cancel_mul_mod nb_v blocksize_v;
  let acc_v = repeat_gen_blocks_multi blocksize_v 0 n nb_v blocks_v a_vec f_v acc_v0 in
  assert (res_v == l_v nb_v rem_v last_v acc_v);

  let acc0 = normalize_v 0 acc_v0 in
  let len0 = nb_v * blocksize_v in
  Math.Lemmas.paren_mul_right nb_v w blocksize;
  Math.Lemmas.cancel_mul_mod (nb_v * w) blocksize;
  assert (len0 % blocksize = 0);
  let n0 = len0 / blocksize in
  Math.Lemmas.cancel_mul_div (nb_v * w) blocksize;
  assert (n0 == w * nb_v);

  calc (==) {
    l_v nb_v rem_v last_v acc_v;
    (==) { assert (repeat_gen_blocks_vec_equiv_pre w blocksize nb_v a a_vec f l l_v normalize_v rem_v last_v acc_v) }
    repeat_gen_blocks #inp_t #c blocksize (w * nb_v) (w * nb_v + w) last_v a f l (normalize_v n acc_v);
    (==) { lemma_repeat_gen_blocks_multi_vec w blocksize nb_v (w * nb_v + w) blocks_v a a_vec f f_v normalize_v acc_v0 }
    repeat_gen_blocks #inp_t #c blocksize (w * nb_v) (w * nb_v + w) last_v a f l
      (repeat_gen_blocks_multi blocksize 0 (w * nb_v + w) (w * nb_v) blocks_v a f acc0);
    (==) { repeat_gen_blocks_split blocksize len0 (w * nb_v + w) 0 inp a f l acc0 }
    repeat_gen_blocks #inp_t #c blocksize 0 (w * nb_v + w) inp a f l acc0;
  }


val lemma_repeat_blocks_multi_vec_equiv_pre:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> f:(lseq a blocksize -> b -> b)
  -> f_v:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_v:(b_vec -> b)
  -> pre:squash (forall (b_v:lseq a (w * blocksize)) (acc_v:b_vec).
         repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v)
  -> i:nat{i < n}
  -> b_v:lseq a (w * blocksize)
  -> acc_v:b_vec ->
  Lemma
   (repeat_gen_blocks_multi_vec_equiv_pre #a w blocksize n hi_f
     (Loops.fixed_a b) (Loops.fixed_a b_vec)
     (Loops.fixed_i f) (Loops.fixed_i f_v)
     (Loops.fixed_i normalize_v) i b_v acc_v)

let lemma_repeat_blocks_multi_vec_equiv_pre #a #b #b_vec w blocksize n hi_f f f_v normalize_v pre i b_v acc_v =
  assert (repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v);
  Math.Lemmas.cancel_mul_mod w blocksize;
  assert (normalize_v (f_v b_v acc_v) == repeat_blocks_multi blocksize b_v f (normalize_v acc_v));
  Math.Lemmas.cancel_mul_div w blocksize;

  Math.Lemmas.lemma_mult_le_right w (i + 1) n;

  calc (==) {
    repeat_blocks_multi blocksize b_v f (normalize_v acc_v);
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi w blocksize b_v f (normalize_v acc_v) }
    repeat_gen_blocks_multi blocksize 0 w w b_v (Loops.fixed_a b) (Loops.fixed_i f) (normalize_v acc_v);
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize (w * i) hi_f w w b_v
           (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) (normalize_v acc_v) }
    repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v (Loops.fixed_a b) (Loops.fixed_i f) (normalize_v acc_v);
    }


let lemma_repeat_blocks_multi_vec #a #b #b_vec w blocksize inp f f_v normalize_v acc_v0 =
  let blocksize_v = w * blocksize in
  let len = length inp in
  let nw = len / blocksize_v in
  len_div_bs_w w blocksize len;
  assert (nw * w == len / blocksize);
  Math.Lemmas.cancel_mul_mod (nw * w) blocksize;
  Math.Lemmas.cancel_mul_div (nw * w) blocksize;

  let acc0 = normalize_v acc_v0 in

  calc (==) {
    normalize_v (repeat_blocks_multi #a #b_vec blocksize_v inp f_v acc_v0);
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi nw blocksize_v inp f_v acc_v0 }
    normalize_v (repeat_gen_blocks_multi blocksize_v 0 nw nw inp (Loops.fixed_a b_vec) (Loops.fixed_i f_v) acc_v0);
    (==) {
      Classical.forall_intro_3 (lemma_repeat_blocks_multi_vec_equiv_pre w blocksize nw (w * nw) f f_v normalize_v ());
      lemma_repeat_gen_blocks_multi_vec w blocksize nw (w * nw) inp (Loops.fixed_a b) (Loops.fixed_a b_vec)
	(Loops.fixed_i f) (Loops.fixed_i f_v) (Loops.fixed_i normalize_v) acc_v0 }
    repeat_gen_blocks_multi blocksize 0 (nw * w) (nw * w) inp (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi (nw * w) blocksize inp f acc0 }
    repeat_blocks_multi blocksize inp f acc0;
    }


val lemma_repeat_blocks_vec_equiv_pre:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> #c:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> lseq a len -> b -> c)
  -> l_v:(len:nat{len < w * blocksize} -> lseq a len -> b_vec -> c)
  -> normalize_v:(b_vec -> b)
  -> pre:squash (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (acc_v:b_vec).
      repeat_blocks_vec_equiv_pre w blocksize f l l_v normalize_v rem b_v acc_v)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq a rem
  -> acc_v:b_vec ->
  Lemma
   (repeat_gen_blocks_vec_equiv_pre #a #c w blocksize n
     (Loops.fixed_a b) (Loops.fixed_a b_vec)
     (Loops.fixed_i f) (Loops.fixed_i l) (Loops.fixed_i l_v)
     (Loops.fixed_i normalize_v) rem b_v acc_v)

let lemma_repeat_blocks_vec_equiv_pre #a #b #b_vec #c w blocksize n f l l_v normalize_v pre rem b_v acc_v =
  let nb_rem = rem / blocksize in
  div_mul_lt blocksize rem w;
  assert (nb_rem < w);

  let acc0 = normalize_v acc_v in

  calc (==) {
    Loops.fixed_i l_v n rem b_v acc_v;
    (==) { }
    l_v rem b_v acc_v;
    (==) { assert (repeat_blocks_vec_equiv_pre w blocksize f l l_v normalize_v rem b_v acc_v) }
    repeat_blocks blocksize b_v f l acc0;
    (==) { repeat_blocks_is_repeat_gen_blocks nb_rem blocksize b_v f l acc0 }
    repeat_gen_blocks blocksize 0 nb_rem b_v (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    (==) { repeat_gen_blocks_extensionality_zero blocksize (w * n) (w * n + w) nb_rem nb_rem b_v
           (Loops.fixed_a b) (Loops.fixed_a b)
	   (Loops.fixed_i f) (Loops.fixed_i l)
	   (Loops.fixed_i f) (Loops.fixed_i l) acc0 }
    repeat_gen_blocks blocksize (w * n) (w * n + w) b_v (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    }


let lemma_repeat_blocks_vec #a #b #b_vec #c w blocksize inp f l f_v l_v normalize_v acc_v0 =
  let blocksize_v = w * blocksize in
  let nb_v = length inp / blocksize_v in

  calc (==) {
    repeat_blocks blocksize_v inp f_v l_v acc_v0;
    (==) { repeat_blocks_is_repeat_gen_blocks nb_v blocksize_v inp f_v l_v acc_v0 }
    repeat_gen_blocks blocksize_v 0 nb_v inp (Loops.fixed_a b_vec) (Loops.fixed_i f_v) (Loops.fixed_i l_v) acc_v0;
    (==) { Classical.forall_intro_3 (lemma_repeat_blocks_multi_vec_equiv_pre w blocksize nb_v (w * nb_v + w) f f_v normalize_v ());
           Classical.forall_intro_3 (lemma_repeat_blocks_vec_equiv_pre #a #b #b_vec #c w blocksize nb_v f l l_v normalize_v ());
           lemma_repeat_gen_blocks_vec w blocksize inp nb_v
             (Loops.fixed_a b) (Loops.fixed_a b_vec) (Loops.fixed_i f) (Loops.fixed_i l)
             (Loops.fixed_i f_v) (Loops.fixed_i l_v) (Loops.fixed_i normalize_v) acc_v0 }
    repeat_gen_blocks blocksize 0 (w * nb_v + w) inp (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) (normalize_v acc_v0);
    (==) { repeat_blocks_is_repeat_gen_blocks (w * nb_v + w) blocksize inp f l (normalize_v acc_v0) }
    repeat_blocks blocksize inp f l (normalize_v acc_v0);
  }



val normalize_v_map:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> i:nat{i <= n}
  -> map_blocks_a a (w * blocksize) n i ->
  map_blocks_a a blocksize (w * n) (w * i)

let normalize_v_map #a w blocksize n i b =
  Math.Lemmas.lemma_mult_le_right w i n;
  b


val lemma_map_blocks_multi_vec_equiv_pre:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> f:(i:nat{i < hi_f} -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> pre:squash (forall (i:nat{i < n}) (b_v:lseq a (w * blocksize)) (acc_v:map_blocks_a a (w * blocksize) n i).
      map_blocks_multi_vec_equiv_pre w blocksize n hi_f f f_v i b_v acc_v)
  -> i:nat{i < n}
  -> b_v:lseq a (w * blocksize)
  -> acc_v:map_blocks_a a (w * blocksize) n i ->
  Lemma
   (repeat_gen_blocks_multi_vec_equiv_pre #a w blocksize n hi_f
     (map_blocks_a a blocksize hi_f)
     (map_blocks_a a (w * blocksize) n)
     (repeat_gen_blocks_map_f blocksize hi_f f)
     (repeat_gen_blocks_map_f (w * blocksize) n f_v)
     (normalize_v_map #a w blocksize n) i b_v acc_v)

let lemma_map_blocks_multi_vec_equiv_pre #a w blocksize n hi_f f f_v pre i b_v acc_v =
  assert (map_blocks_multi_vec_equiv_pre w blocksize n hi_f f f_v i b_v acc_v);
  Math.Lemmas.cancel_mul_div w blocksize;
  Math.Lemmas.cancel_mul_mod w blocksize;
  Math.Lemmas.lemma_mult_le_right w (i + 1) n;
  map_blocks_multi_acc_is_repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v f acc_v


let lemma_map_blocks_multi_vec #a w blocksize n inp f f_v =
  let blocksize_v = w * blocksize in

  Math.Lemmas.cancel_mul_mod n (w * blocksize);
  Math.Lemmas.paren_mul_right blocksize w n;
  Math.Lemmas.cancel_mul_mod (w * n) blocksize;
  //Math.Lemmas.cancel_mul_div (w * n) blocksize;
  //Math.Lemmas.cancel_mul_div n (w * blocksize);

  calc (==) {
    map_blocks_multi blocksize_v n n inp f_v;
    (==) { map_blocks_multi_acc_is_map_blocks_multi0 blocksize_v n n inp f_v }
    map_blocks_multi_acc blocksize_v 0 n n inp f_v Seq.empty;
    (==) { map_blocks_multi_acc_is_repeat_gen_blocks_multi blocksize_v 0 n n inp f_v Seq.empty }
    repeat_gen_blocks_multi blocksize_v 0 n n inp
     (map_blocks_a a blocksize_v n)
     (repeat_gen_blocks_map_f blocksize_v n f_v) Seq.empty;
    (==) { Classical.forall_intro_3 (lemma_map_blocks_multi_vec_equiv_pre #a w blocksize n (w * n) f f_v ());
           lemma_repeat_gen_blocks_multi_vec w blocksize n (w * n) inp
             (map_blocks_a a blocksize (w * n)) (map_blocks_a a blocksize_v n)
             (repeat_gen_blocks_map_f blocksize (w * n) f)
             (repeat_gen_blocks_map_f blocksize_v n f_v)
             (normalize_v_map #a w blocksize n) Seq.empty }
    repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp
     (map_blocks_a a blocksize (w * n))
     (repeat_gen_blocks_map_f blocksize (w * n) f) Seq.empty;
    (==) { map_blocks_multi_acc_is_repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp f Seq.empty }
    map_blocks_multi_acc blocksize 0 (w * n) (w * n) inp f Seq.empty;
    (==) { map_blocks_multi_acc_is_map_blocks_multi0 blocksize (w * n) (w * n) inp f }
    map_blocks_multi blocksize (w * n) (w * n) inp f;
  }


val lemma_map_blocks_vec_equiv_pre:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre:squash (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (acc_v:map_blocks_a a (w * blocksize) n n).
      map_blocks_vec_equiv_pre w blocksize n f l l_v rem b_v acc_v)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq a rem
  -> acc_v:map_blocks_a a (w * blocksize) n n ->
  Lemma
    (repeat_gen_blocks_vec_equiv_pre w blocksize n
      (map_blocks_a a blocksize (w * n + w))
      (map_blocks_a a (w * blocksize) n)
      (repeat_gen_blocks_map_f blocksize (w * n + w) f)
      (repeat_gen_blocks_map_l blocksize (w * n + w) l)
      (repeat_gen_blocks_map_l (w * blocksize) n l_v)
      (normalize_v_map #a w blocksize n) rem b_v acc_v)

let lemma_map_blocks_vec_equiv_pre #a w blocksize n f l l_v pre rem b_v acc_v =
  assert (map_blocks_vec_equiv_pre w blocksize n f l l_v rem b_v acc_v);
  Math.Lemmas.small_mod rem (w * blocksize);
  Math.Lemmas.small_div rem (w * blocksize);
  map_blocks_acc_is_repeat_gen_blocks blocksize (w * n) (w * n + w) b_v f l acc_v


let lemma_map_blocks_vec #a w blocksize inp n f l f_v l_v =
  let len = length inp in
  let blocksize_v = w * blocksize in

  calc (==) {
    map_blocks_acc blocksize_v 0 n inp f_v l_v Seq.empty;
    (==) { map_blocks_acc_is_repeat_gen_blocks blocksize_v 0 n inp f_v l_v Seq.empty }
    repeat_gen_blocks blocksize_v 0 n inp
      (map_blocks_a a blocksize_v n)
      (repeat_gen_blocks_map_f blocksize_v n f_v)
      (repeat_gen_blocks_map_l blocksize_v n l_v)
      Seq.empty;

    (==) {
      Classical.forall_intro_3 (lemma_map_blocks_multi_vec_equiv_pre #a w blocksize n (w * n + w) f f_v ());
      Classical.forall_intro_3 (lemma_map_blocks_vec_equiv_pre #a w blocksize n f l l_v ());
      lemma_repeat_gen_blocks_vec w blocksize inp n
    	(map_blocks_a a blocksize (w * n + w))
    	(map_blocks_a a (w * blocksize) n)
    	(repeat_gen_blocks_map_f blocksize (w * n + w) f)
    	(repeat_gen_blocks_map_l blocksize (w * n + w) l)
    	(repeat_gen_blocks_map_f (w * blocksize) n f_v)
    	(repeat_gen_blocks_map_l (w * blocksize) n l_v)
    	(normalize_v_map #a w blocksize n) Seq.empty }

    repeat_gen_blocks blocksize 0 (w * n + w) inp
      (map_blocks_a a blocksize (w * n + w))
      (repeat_gen_blocks_map_f blocksize (w * n + w) f)
      (repeat_gen_blocks_map_l blocksize (w * n + w) l)
      Seq.empty;

    (==) { map_blocks_acc_is_repeat_gen_blocks blocksize 0 (w * n + w) inp f l Seq.empty }
    map_blocks_acc blocksize 0 (w * n + w) inp f l Seq.empty;
  };

  map_blocks_acc_is_map_blocks0 blocksize_v n inp f_v l_v;
  map_blocks_acc_is_map_blocks0 blocksize (w * n + w) inp f l
