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
  ts_hpmap: Map.t (key:ta) (value:nat) //maps toy pointers to the heaplet they're in
}

val valid_mem : (ptr:ta) -> (h:toy_heap) -> GTot bool //does mem contain a value at ptr?
let valid_mem (ptr:ta) (h:toy_heap) = Map.contains h ptr

val load_mem : (ptr:ta) -> (h:toy_heap) -> GTot tv
let load_mem (ptr:ta) (h:toy_heap) =
  if not (valid_mem ptr h) then 0
  else Map.sel h ptr

val store_mem : (ptr:ta) -> (v:tv) -> (h:toy_heap) -> GTot toy_heap
let store_mem (ptr:ta) (h:toy_heap) = Map.upd h ptr v

val valid_hmem : (ptr:ta) -> (hp:nat) -> (hm:toy_hmap) -> GTot bool //does heaplet hp have a key ptr?
let valid_hmem (ptr:ta) (hp:nat) (hm:toy_hmap) = Map.contains (Map.sel hm hp) ptr

val load_hmem : (ptr:ta) -> (hp:nat) -> GTot tv
let load_hmem (ptr:ta) (hp:nat) (hm:toy_hmap) = 
  if not (valid_hmem ptr hp hm) then 0
  else Map.sel (Map.sel hm hp) ptr 

val store_hmem : (ptr:ta) -> (v:tv) -> (hp:nat) -> (hm:toy_hmap) -> GTot toy_hmap
let store_hmem (ptr:ta) (v:tv) (hp:nat) (hm:toy_hmap) = Map.upd (Map.sel hm hp) ptr v

val get_heaplet_loc : (ptr:ta) (m:Map.t nat toy_heap) -> GTot (o: option tv)
let get_heaplet_loc (ptr:ta) (m:Map.t nat toy_heap) = 
  if not (Map.contains m ta) then None
  else Some (Map.sel m ta)

let lemma_toy_store (ptr:ta) (v:tv) (hp:nat) (s:toy_state) : Lemma
  (requires
    s.ts_heap.domain == s.ts_hpmap.domain
  )
  (ensures
    s.ts_heap.domain == s.ts_hpmap.domain /\
    valid_mem ptr s.ts_heap;
    valid_hmem ptr ptr hp s.ts_hpls;
    get_heaplet_loc ptr s.ts_hpmap == hp
  )
  =  
  store_hmem ta v hp s.ts_hpls;
  store_mem ptr s.ts_heap;
  Map.upd s.ts_hpmap ptr hp
    







