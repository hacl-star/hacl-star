module Lib.Sequence

open Lib.IntTypes

/// Definition of sequences

val seq: a:Type0 -> t:Type0
let seq a = s:Seq.seq a{Seq.length s <= max_size_t}

//unfold
val length: #a:Type0 -> seq a -> size_nat
let length #a l = Seq.length l

let lseq (a:Type0) (len:size_nat) = s:seq a{Seq.length s == len}

type intseq (t:m_inttype) (len:size_nat) = lseq (uint_t t) len

val to_lseq: #a:Type0 -> s:seq a -> l:lseq a (Seq.length s){l == s}
let to_lseq #a s = s

val to_seq: #a:Type0 -> #len:size_nat -> s:lseq a len -> o:seq a {o == s /\ Seq.length o == len}
let to_seq #a #len s = s

//unfold
val index: #a:Type -> #len:size_nat -> s:lseq a len -> n:size_nat{n < len} -> a
let index #a #len s n = Seq.index s n

abstract
type equal (#a:Type) (#len:size_nat) (s1:lseq a len) (s2:lseq a len) =
 forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i

val eq_intro: #a:Type -> #len:size_nat -> s1:lseq a len -> s2:lseq a len -> Lemma
  (requires (forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i))
  (ensures  (equal s1 s2))
  [SMTPat (equal s1 s2)]
let eq_intro #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_intro #a s1 s2

val eq_elim: #a:Type -> #len:size_nat -> s1:lseq a len -> s2:lseq a len -> Lemma
  (requires (equal s1 s2))
  (ensures  (s1 == s2))
  [SMTPat (equal s1 s2)]
let eq_elim #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_elim #a s1 s2

//unfold
val upd: #a:Type -> #len:size_nat -> s:lseq a len -> n:size_nat{n < len /\ len > 0} -> x:a
  -> Pure (lseq a len)
    (requires True)
    (ensures (fun o -> index o n == x /\
      (forall (i:size_nat). {:pattern (index s i)} (i < len /\ i <> n) ==> index o i == index s i)))
let upd #a #len s n x = Seq.upd #a s n x


///
/// Allocation functions for sequences
///

val create: #a:Type -> len:size_nat -> init:a -> s:lseq a len{
    forall (i:size_nat). {:pattern (index s i)} i < len ==> index s i == init}
let create #a len init = Seq.create #a len init

/// TODO: rename this to of_list. Used in Lib.Buffer
val createL: #a:Type -> l:list a{List.Tot.length l <= maxint U32} -> lseq a (List.Tot.length l)
let createL #a l = Seq.createL #a l


val of_list:#a:Type -> l:list a{List.Tot.length l <= maxint U32} -> Tot (seq a)
let of_list #a l =
  let r = Seq.of_list #a l in
  //Seq.lemma_of_list_length #a r l;
  r

//unfold
val sub: #a:Type -> #len:size_nat -> s1:lseq a len -> start:size_nat -> n:size_nat{start + n <= len}
  -> s2:lseq a n{forall (k:size_nat{k < n}).{:pattern (index s2 k)} index s2 k == index s1 (start + k)}
let sub #a #len s start n = Seq.slice #a s start (start + n)

let slice (#a:Type) (#len:size_nat) (i:lseq a len) (start:size_nat)
	  (fin:size_nat{start <= fin /\ fin <= len}) =
	  sub #a #len i start (fin - start)

val update_sub:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> x:lseq a n
  -> o:lseq a len{sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < len)}).{:pattern (index o k)}
      index o k == index i k)}
let update_sub #a #len s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) len) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

let update_slice (#a:Type) (#len:size_nat) (i:lseq a len) (start:size_nat) (fin:size_nat{start <= fin /\ fin <= len}) (upd:lseq a (fin - start)) =
		 update_sub #a #len i start (fin-start) upd

unfold
let op_String_Access #a #len = index #a #len

unfold
let op_String_Assignment #a #len = upd #a #len

/// Iteration

// 2018.07.13 SZ: TODO
// Unsure why these functions are in Lib.Sequence; nothing to do with sequences

val repeat_range: #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> (s:size_nat{s >= min /\ s < max} -> a -> Tot a)
  -> a
  -> Tot a (decreases (max - min))
let rec repeat_range #a min max f x =
  if min = max then x
  else repeat_range #a (min + 1) max f (f min x)

val repeati: #a:Type -> n:size_nat -> (i:size_nat{i < n}  -> a -> Tot a) -> a -> a
let repeati #a n = repeat_range #a 0 n

val repeat: #a:Type -> n:size_nat -> (a -> Tot a) -> a -> a
let repeat #a n f x = repeat_range 0 n (fun i -> f) x

unfold
type repeatable (#a:Type) (#n:size_nat) (pred:(i:size_nat{i <= n} -> a -> Tot Type)) =
  i:size_nat{i < n} -> x:a -> Pure a (requires (pred i x)) (ensures (fun r -> pred (i+1) r))

val repeat_range_inductive: #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> pred:(i:size_nat{i <= max} -> a -> Type)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))
let rec repeat_range_inductive #a min max pred f x =
  if min = max then x
  else repeat_range_inductive #a (min + 1) max pred f (f min x)

val repeati_inductive:
   #a:Type
 -> n:size_nat
 -> pred:(i:size_nat{i <= n} -> a -> Type)
 -> f:repeatable #a #n pred
 -> x0:a{pred 0 x0}
 -> res:a{pred n res}
let repeati_inductive #a =
  repeat_range_inductive #a 0

val fold_land_:
    #n:size_nat
  -> f:(j:size_nat{j < n} -> GTot bool)
  -> i:size_nat{i <= n}
  -> GTot bool
let rec fold_land_ #n f i =
  if i = 0 then true
  else f (i - 1) && fold_land_ #n f (i - 1)

#set-options "--max_fuel 1"

val lbytes_eq_fc:
    #len:size_nat
  -> a:lseq uint8 len
  -> b:lseq uint8 len
  -> i:size_nat{i <= len}
  -> GTot bool
let lbytes_eq_fc #len a b i =
  let open Lib.RawIntTypes in
  let f i = uint_to_nat a.[i] = uint_to_nat b.[i] in
  fold_land_ #len f i

val lbytes_eq:
    #len:size_nat
  -> a:lseq uint8 len
  -> b:lseq uint8 len
  -> res:bool{res == lbytes_eq_fc #len a b len}
let lbytes_eq #len a b =
  let open Lib.RawIntTypes in
  repeati_inductive len
  (fun i res -> res == lbytes_eq_fc #len a b i)
  (fun i res ->
    res && (uint_to_nat a.[i] = uint_to_nat b.[i])
  ) true

val fold_left_range_: #a:Type -> #b:Type -> #len:size_nat
  -> min:size_nat
  -> max:size_nat{min <= max /\ len = max - min}
  -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b)
  -> lseq a len
  -> b
  -> Tot b (decreases (max - min))
let rec fold_left_range_ #a #b #len min max f l x =
  admit()
(*
  match l with
  | [] -> x
  | h::t -> fold_left_range_ #a #b #(len - 1) (min + 1) max f t (f min h x)
*)

val fold_left_range: #a:Type -> #b:Type -> #len:size_nat -> min:size_nat -> max:size_nat{min <= max /\ max <= len} -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b) -> lseq a len -> b -> b
let fold_left_range #a #b #len min max f l x =
  fold_left_range_ #a #b #(max - min) min max f (slice #a #len l min max) x

val fold_lefti: #a:Type -> #b:Type -> #len:size_nat -> (i:size_nat{i < len} -> a -> b -> Tot b) -> lseq a len -> b -> b
let fold_lefti #a #b #len = fold_left_range #a #b #len 0 len

val fold_left: #a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot b) -> lseq a len -> b -> b
let fold_left #a #b #len f = fold_left_range #a #b #len 0 len (fun i -> f)

val map: #a:Type -> #b:Type -> #len:size_nat -> (a -> Tot b) -> lseq a len -> lseq b len
let map #a #b #len f x =
  admit()

val for_all: #a:Type -> #len:size_nat -> (a -> Tot bool) -> lseq a len -> bool
let for_all #a #len f x = Seq.for_all f x

val map2: #a:Type -> #b:Type -> #c:Type -> #len:size_nat -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> lseq c len
let map2 #a #b #c #len f x y =
  admit()

val for_all2: #a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot bool) -> lseq a len -> lseq b len -> bool
let rec for_all2 #a #b #len f x y =
  if Seq.length x = 0 then true
  else
    f (Seq.head x) (Seq.head y) && for_all2 #a #b #(len - 1) f (Seq.tail x) (Seq.tail y)

val as_list: #a:Type -> #len:size_nat -> lseq a len -> l:list a{List.Tot.length l = len}
let as_list #a #len s = Seq.Properties.seq_to_list s

val concat:#a:Type -> #len1:size_nat -> #len2:size_nat{len1 + len2 <= maxint SIZE} -> lseq a len1 -> lseq a len2 -> lseq a (len1 + len2)
let concat #a #len1 #len2 s1 s2 = Seq.append s1 s2

let (@|) #a #len1 #len2 s1 s2 = concat #a #len1 #len2 s1 s2
