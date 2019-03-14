module Vale.Set

module S = FStar.Set

val remove_between (s:S.set int) (start:int) (finish:int): S.set int

val remove_between_reveal (s:S.set int) (start:int) (finish:int) (i:int) : Lemma (
  ((start <= i /\ i < finish) ==> not (S.mem i (remove_between s start finish))) /\
  ((i < start \/ finish <= i) ==> S.mem i (remove_between s start finish) = S.mem i s))
