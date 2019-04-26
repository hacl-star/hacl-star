module Lib.Sequence

open FStar.Mul
open Lib.IntTypes
open Lib.LoopCombinators

#set-options "--z3rlimit 15"

let index #a #len s n = Seq.index s n

let create #a len init = Seq.create #a len init

let concat #a #len0 #len1 s0 s1 = Seq.append s0 s1

let to_list #a s = Seq.seq_to_list s

let of_list #a l = Seq.seq_of_list #a l

let of_list_index #a l i =
  Seq.lemma_seq_of_list_index #a l i

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
  FStar.Seq.lemma_split (sub res 0 (start + n)) start;
  FStar.Seq.lemma_split (sub res1 0 (start + n)) start;
  FStar.Seq.lemma_split res (start + n);
  FStar.Seq.lemma_split res1 (start + n)

let lemma_concat2 #a len0 s0 len1 s1 s =
  FStar.Seq.Properties.lemma_split s len0;
  FStar.Seq.Properties.lemma_split (concat s0 s1) len0

let lemma_concat3 #a len0 s0 len1 s1 len2 s2 s =
  let s' = concat (concat s0 s1) s2 in
  FStar.Seq.Properties.lemma_split (sub s 0 (len0 + len1)) len0;
  FStar.Seq.Properties.lemma_split (sub s' 0 (len0 + len1)) len0;
  FStar.Seq.Properties.lemma_split s (len0 + len1);
  FStar.Seq.Properties.lemma_split s' (len0 + len1)

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

let createi #a len init_f =
  repeat_gen_inductive len
    (createi_a a len init_f)
    (createi_pred a len init_f)
    (createi_step a len init_f)
    (of_list [])

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

(*
let map_blocks #a bs inp f g =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let out = inp in
  let out =
    repeati #(s:seq a{length s == len}) nb
    (fun i out ->
      assert ((i+1) * bs <= nb * bs);
      seq_update_sub out (i * bs) bs (f i (seq_sub inp (i * bs) bs))
    ) out in
  if rem > 0 then
    seq_update_sub out (nb * bs) rem (g nb rem (seq_sub inp (nb * bs) rem))
  else out

*)

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

let repeat_blocks #a #b bs inp f l init =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let acc = repeati nb (repeat_blocks_f bs inp f nb) init in
  let last = seq_sub inp (nb * bs) rem in
  l rem last acc

let lemma_repeat_blocks #a #b bs inp f l init = ()

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

val fixed_a: t:Type0 -> i:nat -> Type0
let fixed_a t i = t

let map_blocks_inner #a (bs:size_nat{bs > 0}) (nb:nat) 
			(inp:seq a{length inp = nb * bs}) 
			(f:(i:nat{i < nb} -> lseq a bs -> lseq a bs)) 
			(i:nat{i < nb}) () =
  (), f i (Seq.slice inp (i*bs) ((i+1)*bs))

#set-options "--z3rlimit 200 --max_ifuel 2"

let map_blocks_multi #a blocksize nb inp f =
  assert (length inp == nb * blocksize);
  assert (length inp / blocksize == nb * blocksize / blocksize);
  Math.Lemmas.multiple_division_lemma nb blocksize;
  assert (length inp / blocksize == nb);
  snd (generate_blocks #a blocksize nb nb (fixed_a unit) (map_blocks_inner blocksize nb inp f) ())


let map_blocks #a blocksize inp f g =
  let len = length inp in 
  let nb = len / blocksize in
  let rem = len % blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let last = Seq.slice inp (nb * blocksize) len in
  let bs = map_blocks_multi #a blocksize nb blocks f in
  if (rem > 0) then
    Seq.append bs (g nb rem last)
  else bs

#set-options "--z3rlimit 50 --max_ifuel 2"
let eq_generate_blocks0 #t len n a f acc0 =
  let a0  = (acc0, (Seq.empty <: s:seq t{length s == 0 * len}))  in
  assert (generate_blocks #t len n 0 a f acc0 ==
	  repeat_gen 0 (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0);
  eq_repeat_gen0 0 (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0;
  ()

let unfold_generate_blocks #t len n a f acc0 i =
  let a0  = (acc0, (Seq.empty <: s:seq t{length s == 0 * len}))  in
  assert (generate_blocks #t len n (i+1) a f acc0 ==
	  repeat_gen (i+1) (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0);
  unfold_repeat_gen (i+1) (generate_blocks_a t len n a) (generate_blocks_inner t len n a f) a0 i;
  ()


(***** The following lemmas are work in progress: Do not rely on them ****)

let map_blocks_multi_lemma #a blocksize n inp f i = admit()
let map_blocks_lemma #a blocksize inp f g i = admit()

let map_blocks_n_fits_lemma len blocksize n i j =
  assert (i < len / (n * blocksize));
  assert (i+1 <= len / (n*blocksize));
  assert ((i + 1) * n * blocksize <= len);
  assert (((i + 1) * n) * blocksize <= len);
  Math.Lemmas.lemma_div_le (((i+1) * n)*blocksize) len blocksize;
  assert ((((i + 1) * n) * blocksize) / blocksize <= len / blocksize);
  Math.Lemmas.multiple_division_lemma ((i + 1) * n) blocksize;
  assert ((i + 1) * n <= len / blocksize);
  assert (i * n + n - 1 < len / blocksize);
  assert (n * i + j < len / blocksize)

let map_blocks_n_lemma #a blocksize n inp f g = admit()

let repeat_blocks_n_fits_lemma blocksize n len = admit()

let repeat_blocks_n_lemma #a #b blocksize n inp f l init = admit()

let generate_blocks1_lemma #t len a f acc0 =
  let a0 : generate_blocks_a t len 1 a 0 = (acc0, (Seq.empty <: s:seq t{length s == 0 * len}))  in
  unfold_repeat_gen 1 (generate_blocks_a t len 1 a) (generate_blocks_inner t len 1 a f) a0 0;
  eq_repeat_gen0 1 (generate_blocks_a t len 1 a) (generate_blocks_inner t len 1 a f) a0;
  let a',b = f 0 acc0 in
  assert (Seq.equal (Seq.append Seq.empty b) b)


let map_blocks_multi1_lemma #a blocksize inp f =  admit()



(*
let map_blocks #a bs inp f g =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let out = inp in
  let out =
    repeati #(s:seq a{length s == len}) nb
    (fun i out ->
      assert ((i+1) * bs <= nb * bs);
      seq_update_sub out (i * bs) bs (f i (seq_sub inp (i * bs) bs))
    ) out in
  if rem > 0 then
    seq_update_sub out (nb * bs) rem (g nb rem (seq_sub inp (nb * bs) rem))
  else out
*)
