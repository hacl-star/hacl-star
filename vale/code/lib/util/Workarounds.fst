module Workarounds

open Words_s

let slice_work_around (s:seq 'a) (i:int) =
  if 0 <= i && i <= length s then slice s 0 i
  else slice s 0 0

let slice_workaround (s:seq 'a) (i:int) (j:int) =
  if 0 <= i && i <= j && j <= length s then slice s i j
  else slice s 0 0

let index_work_around_quad32 (s:seq quad32) (i:int) =
  if 0 <= i && i < length s then index s i
  else Mkfour 0 0 0 0
