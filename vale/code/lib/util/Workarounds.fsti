module Workarounds

open FStar.Seq
open Types_s

val slice_work_around (#a:Type) (s:seq a) (i:int) : Pure (seq a)
  (requires True)
  (ensures fun s' -> 0 <= i && i <= length s ==> s' == slice s 0 i)

val slice_workaround (#a:Type) (s:seq a) (i:int) (j:int) : Pure (seq a)
  (requires True)
  (ensures fun s' -> 0 <= i && i <= j && j <= length s ==> s' == slice s i j)

val index_work_around_quad32 (s:seq quad32) (i:int) : Pure quad32
  (requires True)
  (ensures fun s' -> 0 <= i && i < length s ==> s' == index s i)
