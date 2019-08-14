
module Vale.X64.ToyState
open FStar.Mul

module Map = FStar.Map

type ta = nat
type tv = nat
type toy_heap = Map.t (key: ta) (value: tv) //map of toy addrs to values
type toy_hmap = Map.t (key:nat) (value:toy_heap) //heaplet map

noeq type toy_state = {
  ts_heap: toy_heap;
  ts_hpls: toy_hmap;
}

//unfold let eval_mem (ptr:ta) (s:toy_state) : GTot tv = Map.sel s.ts_heap ptr
//unfold let eval_heap (hp:nat) (s:toy_state) : toy_heap = Map.sel s.ts_hpls hp

val valid_mem (ptr:ta) -> (h:toy_heap) -> GTot bool //does mem contain a value at ptr?
let valid_mem (ptr:ta) (h:toy_heap) = Map.contains h ptr

val load_mem (ptr:ta) -> (h:toy_heap) -> GTot (o:option tv)
let valid_mem (ptr:ta) (h:toy_heap) =
  if not (valid_mem ptr h) then 0
  else Map.sel h ptr

val store_mem (ptr:ta) -> (v:tv) -> (h:toy_heap) -> GTot toy_heap
let store_mem (ptr:ta) (h:toy_heap) = Map.upd h ptr v

val valid_hmem (ptr:ta) -> (hp:nat) -> (hm:toy_hmap) -> GTot bool //does heaplet hp have a key ptr?
let valid_hmem (ptr:ta) (hp:nat) (hm:toy_hmap) = Map.contains (Map.sel hm hp) ptr

val load_hmem (ptr:ta) -> (hp:nat) -> GTot (o: option tv) //the value in healet hp at key ptr (if valid_hmem and valid_mem hold)
let load_hmem (ptr:ta) (hp:nat) (hm:toy_hmap) = 
  if not (valid_hmem ptr hp hm) then 0
  else Map.sel (Map.sel hm hp) ptr 

val store_hmem (ptr:ta) -> (v:tv) -> (hp:nat) -> (hm:toy_hmap) -> GTot toy_hmap
let store_hmem (ptr:ta) (v:tv) (hp:nat) (hm:toy_hmap) = Map.upd (Map.sel hm hp) ptr v







