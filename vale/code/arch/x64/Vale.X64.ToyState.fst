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
   (forall (hp:nat{hp < 16}). //for ever heaplet
     Map.contains s.ts_hpls hp /\ //heaplet exists and
     (forall (ptr:ta{Map.contains (Map.sel s.ts_hpls hp) ptr}). //for every pointer ptr in that heaplet
       Map.contains s.ts_hmap ptr /\ //ptr has a heaplet number and
       Map.sel s.ts_hmap ptr == hp /\ //ptr had the RIGHT heaplet number
       Map.sel (Map.sel s.ts_hpls hp) ptr == Map.sel s.ts_heap ptr))  //value in heaplet same as value in heap

let toy_load (ptr:ta) (hp:nat{hp < 16}) (s:toy_state) : Ghost tv
  (requires (
    valid_mem ptr s.ts_heap /\
    valid_hmem ptr hp s.ts_hpls /\
    Map.sel s.ts_hmap ptr == hp /\
    mem_ok s))
  (ensures
    fun v -> //let (hp:nat) = Map.sel s.ts_hmap ptr in
    v == load_hmem ptr hp s.ts_hpls
  )
  =
  load_mem ptr s.ts_heap

let toy_store (ptr:ta) (v:tv) (hp:nat{hp < 16}) (s:toy_state) : Ghost toy_state
  (requires
    Map.sel s.ts_hmap ptr == hp /\
    mem_ok s)
  (ensures
  fun s' ->
    valid_mem ptr s'.ts_heap /\
    valid_hmem ptr hp s'.ts_hpls /\
    Map.sel s'.ts_hmap ptr == hp /\
    mem_ok s'
  )
  =  
  let hmap': Map.t (key:ta) (value:nat) = Map.upd s.ts_hmap ptr hp in 
  let hmem' : toy_hpls = store_hmem ptr v hp s.ts_hpls in
  let mem' : toy_heap = store_mem ptr v s.ts_heap in
  {
  s with
      ts_heap = mem';
      ts_hpls = hmem';
      ts_hmap = hmap';
   }

let switch_hp (ptr:ta) (ohp:nat{ohp<16}) (nhp:nat{nhp<16}) (s:toy_state) : Ghost toy_state
  (requires
    ohp <> nhp /\
    Map.sel s.ts_hmap ptr == ohp /\
    valid_mem ptr s.ts_heap /\
    valid_hmem ptr ohp s.ts_hpls /\
    mem_ok s
  )
  (ensures
    fun s' ->
    Map.sel s'.ts_hmap ptr == nhp /\
    valid_mem ptr s'.ts_heap /\
    valid_hmem ptr nhp s'.ts_hpls /\
    //mem_ok s' /\
    //Map.domain s'.ts_heap == Map.domain s'.ts_hmap /\
    (Map.sel (Map.sel s.ts_hpls ohp)) ptr == (Map.sel (Map.sel s'.ts_hpls nhp) ptr) /\
    Map.sel s'.ts_heap ptr == (Map.sel (Map.sel s'.ts_hpls nhp) ptr)
  ) =
  assert((Map.sel s.ts_hmap ptr =!= nhp));
  
  let nh = Map.sel s.ts_hpls nhp in
  assert(not (Map.contains nh ptr));
  
  //update the heaplet that ptr belongs to
  let hmap' = Map.upd s.ts_hmap ptr nhp in //update expectd heaplet
  
  assert(Map.domain s.ts_heap == Map.domain s.ts_hmap);
  
  // remote ptr from heaplet #ohp
  let oh = Map.sel s.ts_hpls ohp in //old heaplet
  assert(Map.contains oh ptr);
  let no_ptr = Set.complement(Set.singleton ptr) in
  let ohd' = Set.intersect (Map.domain oh) no_ptr in
  let oh' = Map.restrict ohd' oh in //oh without ptr
  assert(not (Map.contains oh' ptr));
  
  // update heaplets map so that ohp contains heaplet without ptr
  let ts_hpls' = Map.upd s.ts_hpls ohp oh' in

  // move (ptr, value) pair to new heaplet
  let v = load_mem ptr s.ts_heap in
  let hmem' = store_hmem ptr v nhp ts_hpls' in
  
  {
  s with
      ts_hpls = hmem';
      ts_hmap = hmap';
   } 
  
//Map.domain s.ts_heap == Map.domain s.ts_hmap /\
//   (forall (hp:nat{hp < 16}). //for ever heaplet
//     Map.contains s.ts_hpls hp /\ //heaplet exists and
//     (forall (ptr:ta{Map.contains (Map.sel s.ts_hpls hp) ptr}). //for every pointer ptr in that heaplet
//       Map.contains s.ts_hmap ptr /\ //ptr has a heaplet number and
//       Map.sel s.ts_hmap ptr == hp /\ //ptr had the RIGHT heaplet number
//       Map.sel (Map.sel s.ts_hpls hp) ptr == Map.sel s.ts_heap ptr))  //value in heaplet same as value in heap
