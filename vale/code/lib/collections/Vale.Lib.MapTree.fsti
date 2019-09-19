module Vale.Lib.MapTree
open FStar.Mul

(** Balanced binary search tree *)

let is_cmp (#a:eqtype) (is_le:a -> a -> bool) =
  (forall (x y:a).{:pattern is_le x y} is_le x y \/ is_le y x) /\
  (forall (x y:a).{:pattern is_le x y} is_le x y /\ is_le y x ==> x == y) /\
  (forall (x y z:a).{:pattern is_le x y; is_le y z} is_le x y /\ is_le y z ==> is_le x z)

val map (a:eqtype) (b:Type u#a) : Type u#a

val const (a:eqtype) (b:Type) (is_le:(a -> a -> bool){is_cmp is_le}) (default_v:b) : map a b

val sel (#a:eqtype) (#b:Type) (m:map a b) (key:a) : b

val upd (#a:eqtype) (#b:Type) (m:map a b) (key:a) (value:b) : map a b

val lemma_const (a:eqtype) (b:Type) (is_le:(a -> a -> bool){is_cmp is_le}) (d:b) (key:a) : Lemma
  (ensures sel (const a b is_le d) key == d)
  [SMTPat (sel (const a b is_le d) key)]

val lemma_sel_upd_self (#a:eqtype) (#b:Type) (m:map a b) (key:a) (value:b) : Lemma
  (ensures sel (upd m key value) key == value)
  [SMTPat (sel (upd m key value) key)]

val lemma_sel_upd_other (#a:eqtype) (#b:Type) (m:map a b) (key kx:a) (value:b) : Lemma
  (requires key =!= kx)
  (ensures sel (upd m key value) kx == sel m kx)
  [SMTPat (sel (upd m key value) kx)]

