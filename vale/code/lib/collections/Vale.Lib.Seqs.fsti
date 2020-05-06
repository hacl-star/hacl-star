module Vale.Lib.Seqs

open FStar.Mul
open Vale.Lib.Seqs_s
open FStar.Seq

val lemma_slice_first_exactly_in_append (#a:Type) (x y:seq a) :
  Lemma (slice (append x y) 0 (length x) == x)

val lemma_all_but_last_append (#t:Type) (a:seq t) (b:seq t{length b > 0}) :
  Lemma (all_but_last (append a b) == append a (all_but_last b))

val reverse_seq_append (#a:eqtype) (s:seq a) (t:seq a) :
  Lemma(ensures reverse_seq (append s t) == append (reverse_seq t) (reverse_seq s))

val reverse_reverse_seq (#a:Type) (s:seq a) :
  Lemma(ensures reverse_seq (reverse_seq s) == s)
  [SMTPat (reverse_seq (reverse_seq s))]


val seq_map_i_indexed (#a:Type) (#b:Type) (f:int->a->b) (s:seq a) (i:int) :
  Tot (s':seq b { length s' == length s /\
                  (forall j . {:pattern index s' j} 0 <= j /\ j < length s ==> index s' j == f (i + j) (index s j))
                })
      (decreases %[(length s)])

val seq_map_i (#a:Type) (#b:Type) (f:int->a->b) (s:seq a) :
  Tot (s':seq b { length s' == length s /\
                  (forall j . {:pattern index s' j} 0 <= j /\ j < length s ==> index s' j == f j (index s j))
                })

val seq_map_internal_associative (#a:Type) (#b:eqtype) (f:int->a->b) (s:seq a) (pivot:int{0 <= pivot /\ pivot < length s}) :
  Lemma (let left,right = split s pivot in
         seq_map_i f s == seq_map_i_indexed f left 0 @| seq_map_i_indexed f right pivot )

val seq_map_inverses (#a #b:Type) (f:a -> b) (g:b -> a) (s:seq a) : Lemma
  (requires forall x . g (f x) == x)
  (ensures seq_map g (seq_map f s) == s)

val slice_append_adds (#a:Type) (s:seq a) (i:nat) (j:nat{ i <= j /\ j <= length s }) :
  Lemma (slice s 0 i @| slice s i j == slice s 0 j)

val slice_seq_map_commute (#a #b:Type) (f:a -> b) (s:seq a) (i:nat) (j:nat{ i <= j /\ j <= length s }) :
  Lemma (slice (seq_map f s) i j == seq_map f (slice s i j))

val append_distributes_seq_map (#a #b:Type) (f:a -> b) (s1 s2:seq a) :
  Lemma (seq_map f (s1 @| s2) == seq_map f s1 @| seq_map f s2)

val seq_map_injective (#a #b:Type) (f:a -> b) (s s':seq a) : Lemma
  (requires (forall (x x':a).{:pattern (f x); (f x')} f x == f x' ==> x == x') /\ seq_map f s == seq_map f s')
  (ensures s == s')

val list_to_seq (#a:Type) (l:list a) : Pure (seq a)
  (requires True)
  (ensures fun s -> Seq.length s == List.length l)

let rec list_to_seq_post (#a:Type) (l:list a) (s:seq a) (n:nat) : Pure prop
  (requires n + List.length l == Seq.length s)
  (ensures fun _ -> True)
  (decreases l)
  =
  match l with
  | [] -> n == Seq.length s
  | h::t -> Seq.index s n == h /\ list_to_seq_post t s (n + 1)

val lemma_list_to_seq (#a:Type) (l:list a) : Lemma
  (ensures norm [zeta; iota; delta_only [`%list_to_seq_post]] (list_to_seq_post l (list_to_seq l) 0))
