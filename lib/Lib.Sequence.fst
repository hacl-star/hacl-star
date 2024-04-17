module Lib.Sequence

open FStar.Mul
open Lib.IntTypes
open Lib.LoopCombinators

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --using_facts_from '-* +Prims +FStar.Pervasives +FStar.Math.Lemmas +FStar.Seq +Lib.IntTypes +Lib.Sequence'"

let index #a #len s n = Seq.index s n

let create #a len init = Seq.create #a len init

let concat #a #len0 #len1 s0 s1 = Seq.append s0 s1

let to_list #a s = Seq.seq_to_list s

let of_list #a l = Seq.seq_of_list #a l

let of_list_index #a l i =
  Seq.lemma_seq_of_list_index #a l i

let equal #a #len s1 s2 =
  forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i

let eq_intro #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_intro #a (to_seq s1) (to_seq s2)

let eq_elim #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_elim #a s1 s2

let upd #a #len s n x = Seq.upd #a s n x

let member #a #len x l = Seq.count x l > 0

let sub #a #len s start n = Seq.slice #a s start (start + n)

let update_sub #a #len s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) (length s)) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

let lemma_update_sub #a #len dst start n src res =
  let res1 = update_sub dst start n src in
  Seq.lemma_split (sub res 0 (start + n)) start;
  Seq.lemma_split (sub res1 0 (start + n)) start;
  Seq.lemma_split res (start + n);
  Seq.lemma_split res1 (start + n);
  Seq.lemma_eq_intro res (update_sub dst start n src)

let lemma_concat2 #a len0 s0 len1 s1 s =
  Seq.Properties.lemma_split s len0;
  Seq.Properties.lemma_split (concat s0 s1) len0;
  Seq.lemma_eq_intro s (concat s0 s1)

let lemma_concat3 #a len0 s0 len1 s1 len2 s2 s =
  let s' = concat (concat s0 s1) s2 in
  Seq.Properties.lemma_split (sub s 0 (len0 + len1)) len0;
  Seq.Properties.lemma_split (sub s' 0 (len0 + len1)) len0;
  Seq.Properties.lemma_split s (len0 + len1);
  Seq.Properties.lemma_split s' (len0 + len1);
  Seq.lemma_eq_intro s (concat (concat s0 s1) s2)

let createi_a (a:Type) (len:size_nat) (init:(i:nat{i < len} -> a)) (k:nat{k <= len}) =
  lseq a k

let createi_pred (a:Type) (len:size_nat) (init:(i:nat{i < len} -> a)) (k:nat{k <= len})
  (s:createi_a a len init k) =
  forall (i:nat).{:pattern (index s i)} i < k ==> index s i == init i

let createi_step (a:Type) (len:size_nat) (init:(i:nat{i < len} -> a)) (i:nat{i < len})
                 (si:createi_a a len init i)
  : r:createi_a a len init (i + 1)
      {createi_pred a len init i si ==> createi_pred a len init (i + 1) r}
  =
  assert (createi_pred a len init i si ==> (forall (j:nat). j < i ==> index si j == init j));
  Seq.snoc si (init i)

#push-options "--max_fuel 1 --using_facts_from '+Lib.LoopCombinators +FStar.List'"

let createi #a len init_f =
  repeat_gen_inductive len
    (createi_a a len init_f)
    (createi_pred a len init_f)
    (createi_step a len init_f)
    (of_list [])

#pop-options

inline_for_extraction
let mapi_inner (#a:Type) (#b:Type) (#len:size_nat)
  (f:(i:nat{i < len} -> a -> b)) (s:lseq a len) (i:size_nat{i < len}) =
  f i s.[i]

let mapi #a #b #len f s =
  createi #b len (mapi_inner #a #b #len f s)

inline_for_extraction
let map_inner (#a:Type) (#b:Type) (#len:size_nat)
  (f:(a -> Tot b)) (s:lseq a len) (i:size_nat{i < len}) =
  f s.[i]

let map #a #b #len f s =
  createi #b len (map_inner #a #b #len f s)

let map2i #a #b #c #len f s1 s2 =
  createi #c len (fun i -> f i s1.[i] s2.[i])

inline_for_extraction
let map2_inner (#a:Type) (#b:Type) (#c:Type) (#len:size_nat)
  (f:(a -> b -> Tot c)) (s1:lseq a len) (s2:lseq b len) (i:size_nat{i < len}) =
  f s1.[i] s2.[i]

let map2 #a #b #c #len f s1 s2 =
  createi #c len (map2_inner #a #b #c #len f s1 s2)

let for_all #a #len f x = Seq.for_all f x

let for_all2 #a #b #len f x y =
  let r = map2 (fun xi yi -> f xi yi) x y in
  Seq.for_all (fun bi -> bi = true) r

(** Selecting a subset of an unbounded Sequence *)
val seq_sub:
    #a:Type
  -> s1:seq a
  -> start:nat
  -> n:nat{start + n <= length s1}
  -> s2:seq a{length s2 == n /\
             (forall (k:nat{k < n}). {:pattern (Seq.index s2 k)} Seq.index s2 k == Seq.index s1 (start + k))}
let seq_sub #a s start n =
  Seq.slice #a s start (start + n)

(** Updating a subset of an unbounded Sequence with another Sequence *)
val seq_update_sub:
    #a:Type
  -> i:seq a
  -> start:nat
  -> n:nat{start + n <= length i}
  -> x:seq a{length x == n}
  -> o:seq a{length o == length i /\ seq_sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < length i)}).
      {:pattern (Seq.index o k)} Seq.index o k == Seq.index i k)}
let seq_update_sub #a s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) (length s)) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

val repeati_blocks_f:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> b -> b)
  -> nb:nat{nb == length inp / blocksize}
  -> i:nat{i < nb}
  -> acc:b
  -> b
let repeati_blocks_f #a #b bs inp f nb i acc =
  assert ((i+1) * bs <= nb * bs);
  let block = seq_sub inp (i * bs) bs in
  f i block acc

let repeati_blocks #a #b bs inp f g init =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let acc = repeati nb (repeati_blocks_f bs inp f nb) init in
  let last = seq_sub inp (nb * bs) rem in
  g nb rem last acc

let repeat_blocks #a #b #c bs inp f l init =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let acc = repeati nb (repeat_blocks_f bs inp f nb) init in
  let last = seq_sub inp (nb * bs) rem in
  l rem last acc

let lemma_repeat_blocks #a #b #c bs inp f l init = ()

let repeat_blocks_multi #a #b bs inp f init =
  let len = length inp in
  let nb = len / bs in
  repeati nb (repeat_blocks_f bs inp f nb) init

let lemma_repeat_blocks_multi #a #b bs inp f init = ()

let generate_blocks_a (t:Type) (blocklen:size_nat) (max:nat) (a:(i:nat{i <= max} -> Type)) (i:nat{i <= max}) = a i & s:seq t{length s == i * blocklen}

let generate_blocks_inner (t:Type) (blocklen:size_nat) (max:nat) (a:(i:nat{i <= max} -> Type)) (f:(i:nat{i < max} -> a i -> a (i + 1) & s:seq t{length s == blocklen})) (i:nat{i < max}) (acc:generate_blocks_a t blocklen max a i) : generate_blocks_a t blocklen max a (i + 1) =
    let acc, o = acc in
    let acc', block = f i acc in
    let o' : s:seq t{length s == ((i + 1) * blocklen)} = Seq.append o block in
    acc', o'

let generate_blocks #t len max n a f acc0 =
  let a0  = (acc0, (Seq.empty <: s:seq t{length s == 0 * len}))  in
  repeat_gen n (generate_blocks_a t len max a) (generate_blocks_inner t len max a f) a0

let generate_blocks_simple_a (a:Type) (bs:size_nat) (max:nat) (i:nat{i <= max}) = s:seq a{length s == i * bs}

let generate_blocks_simple_f
 (#a:Type)
 (bs:size_nat{bs > 0})
 (max:nat)
 (f:(i:nat{i < max} -> lseq a bs))
 (i:nat{i < max})
 (acc:generate_blocks_simple_a a bs max i) : generate_blocks_simple_a a bs max (i + 1)
=
 Seq.append acc (f i)

let generate_blocks_simple #a bs max nb f =
 repeat_gen nb (generate_blocks_simple_a a bs max)
   (generate_blocks_simple_f #a bs max f) Seq.empty

#restart-solver
let div_interval b n i =
  Math.Lemmas.lemma_div_le (n * b) i b;
  Math.Lemmas.cancel_mul_div n b

let mod_interval_lt b n i j =
  div_interval b n i;
  div_interval b n j

let div_mul_lt b a n = ()

let mod_div_lt b i j =
  mod_interval_lt b (j / b) i j

let div_mul_l a b c d =
  calc (==) {
    a / (c * d);
    == { }
    a / (d * c);
    == { Math.Lemmas.division_multiplication_lemma a d c }
    (a / d) / c;
    == { }
    (b / d) / c;
    == { Math.Lemmas.division_multiplication_lemma b d c }
    b / (d * c);
    == { }
    b / (c * d);
  }


let map_blocks_multi #a bs max nb inp f =
  repeat_gen nb (map_blocks_a a bs max)
    (map_blocks_f #a bs max inp f) Seq.empty

let lemma_map_blocks_multi #a bs max nb inp f = ()

private
val mod_prop: n:pos -> a:nat -> b:nat{a * n <= b /\ b < (a + 1) * n} ->
  Lemma (b - a * n == b % n)
let mod_prop n a b =
  Math.Lemmas.modulo_lemma (b - a * n) n;
  Math.Lemmas.lemma_mod_sub b n a

#push-options "--z3rlimit 200"

let rec index_map_blocks_multi #a bs max n inp f i =
  let map_blocks_a = map_blocks_a a bs max in
  let map_blocks_f = map_blocks_f #a bs max inp f in
  let acc0 = Seq.empty #a in
  let s1 = repeat_gen n map_blocks_a map_blocks_f acc0 in
  unfold_repeat_gen n map_blocks_a map_blocks_f acc0 (n-1);
  let s = repeat_gen (n-1) map_blocks_a map_blocks_f acc0 in
  //assert (s1 == map_blocks_f (n-1) s);
  let s' = f (n-1) (Seq.slice inp ((n-1)*bs) (n*bs)) in
  //assert (s1 == Seq.append s s');
  if i < (n-1)*bs then begin
    Seq.lemma_index_app1 s s' i;
    index_map_blocks_multi #a bs max (n-1) inp f i end
  else begin
    Seq.lemma_index_app2 s s' i;
    mod_prop bs (n-1) i
  end

let map_blocks #a blocksize inp f g =
  let len = length inp in
  let nb = len / blocksize in
  let rem = len % blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let last = Seq.slice inp (nb * blocksize) len in
  let bs = map_blocks_multi #a blocksize nb nb blocks f in
  if (rem > 0) then
    Seq.append bs (g nb rem last)
  else bs

let lemma_map_blocks #a blocksize inp f g = ()

let index_map_blocks #a bs inp f g i =
  let len = length inp in
  let nb  = len / bs in
  let rem = len % bs in
  let blocks = Seq.slice inp 0 (nb * bs) in
  if rem > 0 then
    begin
    let s1 = map_blocks_multi #a bs nb nb blocks f in
    let last = Seq.slice inp (nb * bs) len in
    calc (==) {
      length last;
      == { Seq.lemma_len_slice inp (nb * bs) len }
      len - nb * bs;
      == {mod_prop bs nb len}
      len % bs;
      == { }
      rem;
    };
    let s2 = g nb rem last in
    assert (Seq.equal (map_blocks bs inp f g) (Seq.append s1 s2));
    if i < nb * bs then
      begin
      div_mul_lt bs i nb;
      Seq.lemma_index_app1 s1 s2 i;
      index_map_blocks_multi bs nb nb blocks f i
      end
    else
      begin
      Seq.lemma_index_app2 s1 s2 i;
      mod_prop bs nb i
      end
    end
  else index_map_blocks_multi #a bs nb nb blocks f i

let eq_generate_blocks0 #t len n a f acc0 =
  let a0  = (acc0, (Seq.empty <: s:seq t{length s == 0 * len}))  in
  assert (generate_blocks #t len n 0 a f acc0 ==
          repeat_gen 0 (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0);
  eq_repeat_gen0 0 (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0

let unfold_generate_blocks #t len n a f acc0 i =
  let a0  = (acc0, (Seq.empty <: s:seq t{length s == 0 * len}))  in
  assert (generate_blocks #t len n (i+1) a f acc0 ==
          repeat_gen (i+1) (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0);
  unfold_repeat_gen (i+1) (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0 i

let rec index_generate_blocks #t len max n f i =
  assert (0 < n);
  let a_spec (i:nat{i <= max}) = unit in
  let _,s = generate_blocks #t len max (n-1) a_spec f () in
  let _,s' = f (n-1) () in
  let _,s1 = generate_blocks #t len max n a_spec f () in
  unfold_generate_blocks #t len max a_spec f () (n-1);
  Seq.Properties.lemma_split s1 (n * len - len);
  Seq.Properties.lemma_split (Seq.append s s') (n * len - len);
  Seq.lemma_eq_intro s1 (Seq.append s s');
  if i < (n-1) * len then
    begin
    Seq.lemma_index_app1 s s' i;
    index_generate_blocks len max (n-1) f i
    end
  else
    begin
    Seq.lemma_index_app2 s s' i;
    mod_prop len (n-1) i
    end

#push-options "--using_facts_from '+FStar.UInt.pow2_values'"

let create2 #a x0 x1 =
  let l = [x0; x1] in
  assert_norm (List.Tot.length l = 2);
  createL l

let create2_lemma #a x0 x1 =
  Seq.elim_of_list [x0; x1]

let create4 #a x0 x1 x2 x3 =
  let l = [x0; x1; x2; x3] in
  assert_norm (List.Tot.length l = 4);
  createL l

let create4_lemma #a x0 x1 x2 x3 =
  Seq.elim_of_list [x0; x1; x2; x3]

let create8 #a x0 x1 x2 x3 x4 x5 x6 x7 =
  let l = [x0; x1; x2; x3; x4; x5; x6; x7] in
  assert_norm (List.Tot.length l = 8);
  createL l

let create8_lemma #a x0 x1 x2 x3 x4 x5 x6 x7 =
  Seq.elim_of_list [x0; x1; x2; x3; x4; x5; x6; x7]

let create16 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
  let l = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15] in
  assert_norm (List.Tot.length l = 16);
  createL l

let create16_lemma #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
  Seq.elim_of_list [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]

let create32 #a
  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
  let l = [
    x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15;
    x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31
  ] in
  assert_norm (List.Tot.length l = 32);
  createL l

let create32_lemma #a
x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
  Seq.elim_of_list [
    x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15;
    x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31
  ]
