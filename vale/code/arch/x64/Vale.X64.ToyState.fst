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

let load_hmem (ptr:ta) (hp:nat) (hm:toy_hpls) = 
  if not (valid_hmem ptr hp hm) then 0
  else Map.sel (Map.sel hm hp) ptr 

let store_hmem (ptr:ta) (v:tv) (hp:nat) (hm:toy_hpls) = Map.upd (Map.sel hm hp) ptr v

//get which heap a pointer belongs to
let get_heaplet_loc (ptr:ta) (m:Map.t ta nat) = 
  if not (Map.contains m ptr) then None
  else Some (Map.sel m ptr)

let mem_invariant (s:toy_state) =
   Map.domain s.ts_heap == Map.domain s.ts_hmap /\
   (forall (ptr:ta{Map.contains s.ts_heap ptr}). {:pattern (Map.contains s.ts_heap ptr)} //for every pointer in the heap...
   (Map.contains s.ts_hmap ptr /\ //ptr has a heaplet number
   (let hp = (Map.sel s.ts_hmap ptr) in //heaplet number
   Map.contains s.ts_hpls hp /\ //heaplet exists
   (let heaplet = Map.sel s.ts_hpls hp in //heaplet map
   Map.sel heaplet ptr == Map.sel s.ts_heap ptr))))  //value in heaplet same as value in heap

#reset-options "--query_stats"
let toy_load (ptr:ta) (hp:nat) (s:toy_state) : Ghost tv
  (requires (
    valid_mem ptr s.ts_heap /\
    valid_hmem ptr hp s.ts_hpls /\
    Map.sel s.ts_hmap ptr == hp /\
    mem_invariant s))
  (ensures
    fun _ -> let hp = Map.sel s.ts_hmap ptr in
    load_mem ptr s.ts_heap == load_hmem ptr hp s.ts_hpls
  )
  =
  load_mem ptr s.ts_heap

let toy_store (ptr:ta) (v:tv) (hp:nat) (s:toy_state) : Ghost toy_state
  (requires
    // heaplet and heap ptrs aligned
    Map.domain s.ts_heap == Map.domain s.ts_hmap /\
    // ptr in the heap (and so also in a heaplet)
    Map.contains s.ts_heap ptr)
  (ensures
  fun s' ->
    Map.domain s'.ts_heap == Map.domain s'.ts_hmap /\
    valid_mem ptr s'.ts_heap /\
    valid_hmem ptr hp s'.ts_hpls /\
    get_heaplet_loc ptr s'.ts_hmap == Some hp
  )
  =  
  Map.upd s.ts_hmap ptr hp;
  store_hmem ptr v hp s.ts_hpls;
  store_mem ptr s.ts_heap

  
    







