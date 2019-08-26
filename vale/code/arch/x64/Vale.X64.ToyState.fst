module Vale.X64.ToyState
open FStar.Mul

module Map = FStar.Map

type ta = nat
type tv = nat
type toy_heap = Map.t (key: ta) (value: tv) // main heap
type toy_hpls = Map.t (key:nat) (value:toy_heap) //heaplet map

noeq type toy_state = {
  ts_heap: toy_heap;
  ts_hpls: toy_hpls;
  ts_hmap: Map.t (key:ta) (value:nat) // ptr -> hp map
}

val valid_mem : (ptr:ta) -> (h:toy_heap) -> GTot bool
let valid_mem (ptr:ta) (h:toy_heap) = Map.contains h ptr

val load_mem : (ptr:ta) -> (h:toy_heap) -> GTot tv
let load_mem (ptr:ta) (h:toy_heap) =
  if not (valid_mem ptr h) then 0
  else Map.sel h ptr

val store_mem : (ptr:ta) -> (v:tv) -> (h:toy_heap) -> GTot toy_heap
let store_mem (ptr:ta) (v:tv) (h:toy_heap) = Map.upd h ptr v

val valid_hmem : (ptr:ta) -> (hp:nat) -> (hm:toy_hpls) -> GTot bool
let valid_hmem (ptr:ta) (hp:nat) (hm:toy_hpls) = Map.contains (Map.sel hm hp) ptr

val load_hmem : (ptr:ta) -> (hp:nat) -> (hm:toy_hpls) -> GTot tv
let load_hmem (ptr:ta) (hp:nat) (hm:toy_hpls) = 
  if not (valid_hmem ptr hp hm) then 0
  else Map.sel (Map.sel hm hp) ptr 

val store_hmem : (ptr:ta) -> (v:tv) -> (hp:nat) -> (hm:toy_hpls) -> GTot toy_hpls
let store_hmem (ptr:ta) (v:tv) (hp:nat) (hm:toy_hpls) = 
  let h = Map.upd (Map.sel hm hp) ptr v in
  Map.upd hm hp h

// for every heaplet hp:
//     for every pointer ptr in heaplet hp:
//         hmap contains (ptr, hp)
//         (hpls, hp) contains (ptr, v)
//         value at ptr in hp == value at ptr in heap
let mem_ok (s:toy_state) =
   Map.domain s.ts_heap == Map.domain s.ts_hmap /\
   (forall (hp:nat{hp < 16}). //for ever heaplet
     Map.contains s.ts_hpls hp /\
     (forall (ptr:ta{Map.contains (Map.sel s.ts_hpls hp) ptr}).
       Map.contains s.ts_hmap ptr /\
       Map.sel s.ts_hmap ptr == hp /\
       Map.sel (Map.sel s.ts_hpls hp) ptr == Map.sel s.ts_heap ptr))

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

#set-options "--z3rlimit 100"
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
    valid_hmem ptr nhp s'.ts_hpls /\
    mem_ok s' /\
    (Map.sel (Map.sel s.ts_hpls ohp)) ptr == (Map.sel (Map.sel s'.ts_hpls nhp) ptr) /\
    Map.sel s'.ts_heap ptr == (Map.sel (Map.sel s'.ts_hpls nhp) ptr)
  ) =

  // s' is:
  // s with ts_hmap = hmap'                         <-- updated hmap
  //   with ts_hpls with (ohp, oh') and (nhp, nh')  <-- updated heaplets
  //   where
  //       nh' contains (ptr, v)
  //       oh' does not contain ptr
  //  and ts_heap is unchanged

  // updated hmap
  let hmap' = Map.upd s.ts_hmap ptr nhp in //update expectd heaplet
  assert(Set.equal (Map.domain s.ts_heap) (Map.domain hmap'));

  // get value to move from oh to nh
  let v = load_mem ptr s.ts_heap in

  // remote ptr from heaplet ohp
  let oh = Map.sel s.ts_hpls ohp in //old heaplet
  let no_ptr = Set.complement(Set.singleton ptr) in
  let ohd' = Set.intersect (Map.domain oh) no_ptr in //new domain
  let oh' = Map.restrict ohd' oh in //oh without ptr

  // add ptr and value to new heaplet
  let nh = Map.sel s.ts_hpls nhp in
  let nh' = Map.upd nh ptr v in

  // update heaplets map
  let ts_hpls' = Map.upd s.ts_hpls ohp oh' in
  let ts_hpls' = Map.upd ts_hpls' nhp nh' in

  {
  s with
      ts_hpls = ts_hpls';
      ts_hmap = hmap';
   }
