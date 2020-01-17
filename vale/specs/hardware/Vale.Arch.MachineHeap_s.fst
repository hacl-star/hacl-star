module Vale.Arch.MachineHeap_s

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s

unfold let (.[]) = Map.sel
unfold let (.[]<-) = Map.upd

let machine_heap = Map.t int nat8

let is_machine_heap_update (mh mh':machine_heap) =
  Set.equal (Map.domain mh) (Map.domain mh') /\
  (forall (i:int).{:pattern Map.sel mh i \/ Map.sel mh' i}
    not (Map.contains mh i) ==> Map.sel mh i == Map.sel mh' i)

let get_heap_val32_def (ptr:int) (mem:machine_heap) : nat32 =
  four_to_nat 8
  (Mkfour
    mem.[ptr]
    mem.[ptr + 1]
    mem.[ptr + 2]
    mem.[ptr + 3])
[@"opaque_to_smt"] let get_heap_val32 = opaque_make get_heap_val32_def
irreducible let get_heap_val32_reveal = opaque_revealer (`%get_heap_val32) get_heap_val32 get_heap_val32_def

let get_heap_val64_def (ptr:int) (mem:machine_heap) : nat64 =
  two_to_nat 32
  (Mktwo
    (four_to_nat 8 (Mkfour mem.[ptr] mem.[ptr + 1] mem.[ptr + 2] mem.[ptr + 3]))
    (four_to_nat 8 (Mkfour mem.[ptr + 4] mem.[ptr + 5] mem.[ptr + 6] mem.[ptr + 7]))
  )
[@"opaque_to_smt"] let get_heap_val64 = opaque_make get_heap_val64_def
irreducible let get_heap_val64_reveal = opaque_revealer (`%get_heap_val64) get_heap_val64 get_heap_val64_def

let get_heap_val128_def (ptr:int) (mem:machine_heap) : quad32 = Mkfour
  (get_heap_val32 ptr mem)
  (get_heap_val32 (ptr + 4) mem)
  (get_heap_val32 (ptr + 8) mem)
  (get_heap_val32 (ptr + 12) mem)
[@"opaque_to_smt"] let get_heap_val128 = opaque_make get_heap_val128_def
irreducible let get_heap_val128_reveal = opaque_revealer (`%get_heap_val128) get_heap_val128 get_heap_val128_def

let update_heap32_def (ptr:int) (v:nat32) (mem:machine_heap) : machine_heap =
  let v = nat_to_four 8 v in
  let mem = mem.[ptr] <- v.lo0 in
  let mem = mem.[ptr + 1] <- v.lo1 in
  let mem = mem.[ptr + 2] <- v.hi2 in
  let mem = mem.[ptr + 3] <- v.hi3 in
  mem
[@"opaque_to_smt"] let update_heap32 = opaque_make update_heap32_def
irreducible let update_heap32_reveal = opaque_revealer (`%update_heap32) update_heap32 update_heap32_def

let update_heap64_def (ptr:int) (v:nat64) (mem:machine_heap) : machine_heap =
  let v = nat_to_two 32 v in
  let lo = nat_to_four 8 v.lo in
  let hi = nat_to_four 8 v.hi in
  let mem = mem.[ptr] <- lo.lo0 in
  let mem = mem.[ptr + 1] <- lo.lo1 in
  let mem = mem.[ptr + 2] <- lo.hi2 in
  let mem = mem.[ptr + 3] <- lo.hi3 in
  let mem = mem.[ptr + 4] <- hi.lo0 in
  let mem = mem.[ptr + 5] <- hi.lo1 in
  let mem = mem.[ptr + 6] <- hi.hi2 in
  let mem = mem.[ptr + 7] <- hi.hi3 in
  mem
[@"opaque_to_smt"] let update_heap64 = opaque_make update_heap64_def
irreducible let update_heap64_reveal = opaque_revealer (`%update_heap64) update_heap64 update_heap64_def

let update_heap128_def (ptr:int) (v:quad32) (mem:machine_heap) =
  let mem = update_heap32 ptr v.lo0 mem in
  let mem = update_heap32 (ptr + 4) v.lo1 mem in
  let mem = update_heap32 (ptr + 8) v.hi2 mem in
  let mem = update_heap32 (ptr + 12) v.hi3 mem in
  mem
[@"opaque_to_smt"] let update_heap128 = opaque_make update_heap128_def
irreducible let update_heap128_reveal = opaque_revealer (`%update_heap128) update_heap128 update_heap128_def

let valid_addr (ptr:int) (mem:machine_heap) : bool =
  Map.contains mem ptr

[@"opaque_to_smt"]
let valid_addr64 (ptr:int) (mem:machine_heap) =
  valid_addr ptr mem &&
  valid_addr (ptr + 1) mem &&
  valid_addr (ptr + 2) mem &&
  valid_addr (ptr + 3) mem &&
  valid_addr (ptr + 4) mem &&
  valid_addr (ptr + 5) mem &&
  valid_addr (ptr + 6) mem &&
  valid_addr (ptr + 7) mem

[@"opaque_to_smt"]
let valid_addr128 (ptr:int) (mem:machine_heap) =
  valid_addr ptr mem &&
  valid_addr (ptr + 1) mem &&
  valid_addr (ptr + 2) mem &&
  valid_addr (ptr + 3) mem &&
  valid_addr (ptr + 4) mem &&
  valid_addr (ptr + 5) mem &&
  valid_addr (ptr + 6) mem &&
  valid_addr (ptr + 7) mem &&
  valid_addr (ptr + 8) mem &&
  valid_addr (ptr + 9) mem &&
  valid_addr (ptr + 10) mem &&
  valid_addr (ptr + 11) mem &&
  valid_addr (ptr + 12) mem &&
  valid_addr (ptr + 13) mem &&
  valid_addr (ptr + 14) mem &&
  valid_addr (ptr + 15) mem

