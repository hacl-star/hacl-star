module Vale.Lib.Map16
open FStar.Mul
open Vale.X64.Machine_s

type map2 (a:Type) = a & a
type map4 (a:Type) = map2 a & map2 a
type map8 (a:Type) = map4 a & map4 a
type map16 (a:Type) = map8 a & map8 a

[@va_qattr]
let sel2 (#a:Type) (m:map2 a) (n:int) : a =
  match m with (m0, m1) ->
  match n < 1 with true -> m0 | false -> m1

[@va_qattr]
let sel4 (#a:Type) (m:map4 a) (n:int) : a =
  match m with (m0, m1) ->
  match n < 2 with true -> sel2 m0 n | false -> sel2 m1 (n - 2)

[@va_qattr]
let sel8 (#a:Type) (m:map8 a) (n:int) : a =
  match m with (m0, m1) ->
  match n < 4 with true -> sel4 m0 n | false -> sel4 m1 (n - 4)

[@va_qattr]
let sel16 (#a:Type) (m:map16 a) (n:int) : a =
  match m with (m0, m1) ->
  match n < 8 with true -> sel8 m0 n | false -> sel8 m1 (n - 8)

[@va_qattr]
let upd2 (#a:Type) (m:map2 a) (n:int) (v:a) : map2 a =
  match m with (m0, m1) ->
  match n < 1 with true -> (v, m1) | false -> (m0, v)

[@va_qattr]
let upd4 (#a:Type) (m:map4 a) (n:int) (v:a) : map4 a =
  match m with (m0, m1) ->
  match n < 2 with true -> (upd2 m0 n v, m1) | false -> (m0, upd2 m1 (n - 2) v)

[@va_qattr]
let upd8 (#a:Type) (m:map8 a) (n:int) (v:a) : map8 a =
  match m with (m0, m1) ->
  match n < 4 with true -> (upd4 m0 n v, m1) | false -> (m0, upd4 m1 (n - 4) v)

[@va_qattr]
let upd16 (#a:Type) (m:map16 a) (n:int) (v:a) : map16 a =
  match m with (m0, m1) ->
  match n < 8 with true -> (upd8 m0 n v, m1) | false -> (m0, upd8 m1 (n - 8) v)

val lemma_self16 (#a:Type) (m:map16 a) (n:int) (v:a) : Lemma
  (requires 0 <= n /\ n < 16)
  (ensures sel16 (upd16 m n v) n == v)

val lemma_other16 (#a:Type) (m:map16 a) (n1 n2:int) (v:a) : Lemma
  (requires 0 <= n1 /\ n1 < 16 /\ 0 <= n2 /\ n2 < 16 /\ n1 =!= n2)
  (ensures sel16 (upd16 m n1 v) n2 == sel16 m n2)

val lemma_equal16 (#a:Type) (m1 m2:map16 a) : Lemma
  (requires (forall (i:int).{:pattern (sel16 m1 i) \/ (sel16 m2 i)} 0 <= i /\ i < 16 ==> sel16 m1 i == sel16 m2 i))
  (ensures m1 == m2)

//[@"uninterpreted_by_smt"]
//let map = map16

[@va_qattr "opaque_to_smt"]
let sel (#a:Type) (m:map16 a) (n:int) : a =
  sel16 m n

[@va_qattr "opaque_to_smt"]
let upd (#a:Type) (m:map16 a) (n:int) (v:a) : map16 a =
  upd16 m n v

let get (#a:Type) (m:map16 a) (n:int) : a =
  sel m n

[@va_qattr]
let eta16 (#a:Type) (m:map16 a) : map16 a =
  let m0_3 = ((get m 0, get m 1), (get m 2, get m 3)) in
  let m4_7 = ((get m 4, get m 5), (get m 6, get m 7)) in
  let m8_11 = ((get m 8, get m 9), (get m 10, get m 11)) in
  let m12_15 = ((get m 12, get m 13), (get m 14, get m 15)) in
  ((m0_3, m4_7), (m8_11, m12_15))

[@va_qattr "opaque_to_smt"]
let eta (#a:Type) (m:map16 a) : map16 a =
  eta16 m

val lemma_self (#a:Type) (m:map16 a) (n:int) (v:a) : Lemma
  (requires 0 <= n /\ n < 16)
  (ensures sel (upd m n v) n == v)
  [SMTPat (sel (upd m n v) n)]

val lemma_other (#a:Type) (m:map16 a) (n1 n2:int) (v:a) : Lemma
  (requires 0 <= n1 /\ n1 < 16 /\ 0 <= n2 /\ n2 < 16 /\ n1 =!= n2)
  (ensures sel (upd m n1 v) n2 == sel m n2)
  [SMTPat (sel (upd m n1 v) n2)]

val lemma_equal (#a:Type) (m1 m2:map16 a) : Lemma
  (requires (forall (i:int).{:pattern (sel m1 i) \/ (sel m2 i)} 0 <= i /\ i < 16 ==> sel m1 i == sel m2 i))
  (ensures m1 == m2)

val lemma_eta16 (#a:Type) (m:map16 a) : Lemma
  (ensures eta16 m == m)

val lemma_eta (#a:Type) (m:map16 a) : Lemma
  (ensures eta m == m)
  [SMTPat (eta m)]

val equal (#a:Type) (m1 m2:map16 a) : Type0

val lemma_equal_intro (#a:Type) (m1 m2:map16 a) : Lemma
  (requires (forall (i:int).{:pattern (sel m1 i) \/ (sel m2 i)} 0 <= i /\ i < 16 ==> sel m1 i == sel m2 i))
  (ensures equal m1 m2)
  [SMTPat (equal m1 m2)]

val lemma_equal_elim (#a:Type) (m1 m2:map16 a) : Lemma
  (requires equal m1 m2)
  (ensures m1 == m2)
  [SMTPat (equal m1 m2)]

val init (a:Type) (f:(i:nat{i < 16}) -> a) : Pure (map16 a)
  (requires True)
  (ensures fun m -> forall (i:int).{:pattern (sel m i)} 0 <= i /\ i < 16 ==> sel m i == f i)

val init_ghost (a:Type) (f:(i:nat{i < 16}) -> GTot a) : Ghost (map16 a)
  (requires True)
  (ensures fun m -> forall (i:int).{:pattern (sel m i)} 0 <= i /\ i < 16 ==> sel m i == f i)
