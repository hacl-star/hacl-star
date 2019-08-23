module Vale.X64.ToyState
open FStar.Mul

module Map = FStar.Map

type ta = nat
type tv = nat
type toy_heap = Map.t (key: ta) (value: tv) //map of toy addrs to values
type toy_hpls = Map.t (key:nat) (value:toy_heap) //heaplet map

noeq type toy_state = {
  ts_heap: toy_heap;
  ts_hpls: toy_hpls;
  ts_hmap: Map.t (key:ta) (value:nat) //maps toy pointers to the heaplet they're in
}

val valid_mem : (ptr:ta) -> (h:toy_heap) -> GTot bool //does mem contain a value at ptr?
let valid_mem (ptr:ta) (h:toy_heap) = Map.contains h ptr

val load_mem : (ptr:ta) -> (h:toy_heap) -> GTot tv
let load_mem (ptr:ta) (h:toy_heap) =
  if not (valid_mem ptr h) then 0
  else Map.sel h ptr

val store_mem : (ptr:ta) -> (v:tv) -> (h:toy_heap) -> GTot toy_heap
let store_mem (ptr:ta) (v:tv) (h:toy_heap) = Map.upd h ptr v

val valid_hmem : (ptr:ta) -> (hp:nat) -> (hm:toy_hpls) -> GTot bool //does heaplet hp have a key ptr?
let valid_hmem (ptr:ta) (hp:nat) (hm:toy_hpls) = Map.contains (Map.sel hm hp) ptr

val load_hmem : (ptr:ta) -> (hp:nat) -> (hm:toy_hpls) -> GTot tv
let load_hmem (ptr:ta) (hp:nat) (hm:toy_hpls) = 
  if not (valid_hmem ptr hp hm) then 0
  else Map.sel (Map.sel hm hp) ptr 

val store_hmem : (ptr:ta) -> (v:tv) -> (hp:nat) -> (hm:toy_hpls) -> GTot toy_hpls
let store_hmem (ptr:ta) (v:tv) (hp:nat) (hm:toy_hpls) = 
  let h = Map.upd (Map.sel hm hp) ptr v in
  Map.upd hm hp h
  
let mem_ok (s:toy_state) =
   Map.domain s.ts_heap == Map.domain s.ts_hmap /\
   (forall (ptr:ta{Map.contains s.ts_heap ptr}). {:pattern (Map.contains s.ts_heap ptr)}
   (Map.contains s.ts_hmap ptr /\ //ptr has a heaplet number
   (let hp = (Map.sel s.ts_hmap ptr) in
   Map.contains s.ts_hpls hp /\ //heaplet exists
   (let heaplet = Map.sel s.ts_hpls hp in
   Map.sel heaplet ptr == Map.sel s.ts_heap ptr))))  //value in heaplet same as value in heap

let toy_load (ptr:ta) (hp:nat) (s:toy_state) : Ghost tv
  (requires (
    valid_mem ptr s.ts_heap /\
    valid_hmem ptr hp s.ts_hpls /\
    Map.sel s.ts_hmap ptr == hp /\
    mem_ok s))
  (ensures
    fun _ -> let hp = Map.sel s.ts_hmap ptr in
    load_mem ptr s.ts_heap == load_hmem ptr hp s.ts_hpls
  )
  =
  load_mem ptr s.ts_heap

let toy_store (ptr:ta) (v:tv) (hp:nat) (s:toy_state) : Ghost toy_state
  (requires
    Map.sel s.ts_hmap ptr == hp /\
    mem_ok s)
  (ensures
  fun s' ->
    Map.domain s'.ts_heap == Map.domain s'.ts_hmap /\
    valid_mem ptr s'.ts_heap /\
    valid_hmem ptr hp s'.ts_hpls /\
    Map.sel s'.ts_hmap ptr == hp /\
    mem_ok s'
  )
  =  
  let hmap': Map.t (key:ta) (value:nat) = Map.upd s.ts_hmap ptr hp in 
  let hmem' = store_hmem ptr v hp s.ts_hpls in
  let mem' : toy_heap = store_mem ptr v s.ts_heap in
  {
  s with
      ts_heap = mem';
      ts_hpls = hmem';
      ts_hmap = hmap';
   }
