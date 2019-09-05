module Vale.Lib.Set
open FStar.Mul

friend FStar.Map

let rec remove_between' s (start:int) (finish:int{start <= finish}) : Tot (s':S.set int{ forall i.
  ((start <= i /\ i < finish) ==> not (S.mem i s')) /\
  ((i < start \/ finish <= i) ==> S.mem i s' = S.mem i s)})
  (decreases %[finish - start]) =
  if finish = start then s
  else remove_between' (S.intersect s (S.complement (S.singleton start))) (start + 1) finish

let remove_between s start finish =
  if finish <= start then s
  else remove_between' s start finish

let remove_between_reveal s start finish i = ()

let lemma_sel_restrict #a s m k = ()
