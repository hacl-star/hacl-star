module Vale.Arch.MachineHeap
open FStar.Mul
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Two
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Seq
open Vale.Def.Types_s
open Vale.Arch.Types

let same_mem_get_heap_val64 ptr mem1 mem2 =
  get_heap_val64_reveal ();
  four_to_nat_8_injective ();
  two_to_nat_32_injective ()

let frame_update_heap64 ptr v mem =
  get_heap_val64_reveal ();
  update_heap64_reveal ()

let correct_update_get64 ptr v mem =
  get_heap_val64_reveal ();
  update_heap64_reveal ()

let same_domain_update64 ptr v mem =
  reveal_opaque (`%valid_addr64) valid_addr64;
  update_heap64_reveal ();
  let mem2 = update_heap64 ptr v mem in
  assert (Set.equal (Map.domain mem) (Map.domain mem2))

let same_mem_get_heap_val32 ptr mem1 mem2 =
  get_heap_val32_reveal ();
  four_to_nat_8_injective ()

let frame_update_heap32 ptr v mem =
  get_heap_val32_reveal ();
  update_heap32_reveal ()

let same_domain_update32 ptr v mem =
  get_heap_val32_reveal ();
  update_heap32_reveal ();
  assert (Set.equal (Map.domain mem) (Map.domain (update_heap32 ptr v mem)))

let update_heap32_get_heap32 ptr mem =
  get_heap_val32_reveal ();
  update_heap32_reveal ();
  assert (Map.equal mem (update_heap32 ptr (get_heap_val32 ptr mem) mem))

let frame_update_heap128 ptr v mem =
  update_heap128_reveal ();
  let mem1 = update_heap32 ptr v.lo0 mem in
  frame_update_heap32 ptr v.lo0 mem;
  let mem2 = update_heap32 (ptr+4) v.lo1 mem1 in
  frame_update_heap32 (ptr+4) v.lo1 mem1;
  let mem3 = update_heap32 (ptr+8) v.hi2 mem2 in
  frame_update_heap32 (ptr+8) v.hi2 mem2;
  let mem4 = update_heap32 (ptr+12) v.hi3 mem3 in
  frame_update_heap32 (ptr+12) v.hi3 mem3

let correct_update_get32 (ptr:int) (v:nat32) (mem:machine_heap) : Lemma
  (get_heap_val32 ptr (update_heap32 ptr v mem) == v) =
  get_heap_val32_reveal ();
  update_heap32_reveal ()

#reset-options "--z3rlimit 30 --using_facts_from 'Prims Vale.Def.Opaque_s Vale.Arch.MachineHeap_s Vale.Def.Words_s Vale.Def.Types_s'"

let correct_update_get128 ptr v mem =
  update_heap128_reveal ();
  get_heap_val32_reveal ();
  update_heap32_reveal ();
  get_heap_val128_reveal ();
  let mem1 = update_heap32 ptr v.lo0 mem in
  frame_update_heap32 ptr v.lo0 mem;
  correct_update_get32 ptr v.lo0 mem;
  let mem2 = update_heap32 (ptr+4) v.lo1 mem1 in
  frame_update_heap32 (ptr+4) v.lo1 mem1;
  correct_update_get32 (ptr+4) v.lo1 mem1;
  let mem3 = update_heap32 (ptr+8) v.hi2 mem2 in
  frame_update_heap32 (ptr+8) v.hi2 mem2;
  correct_update_get32 (ptr+8) v.hi2 mem2;
  let mem4 = update_heap32 (ptr+12) v.hi3 mem3 in
  frame_update_heap32 (ptr+12) v.hi3 mem3;
  correct_update_get32 (ptr+12) v.hi3 mem3

#reset-options "--z3rlimit 10 --max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

let same_domain_update128 ptr v mem =
  reveal_opaque (`%valid_addr128) valid_addr128;
  update_heap128_reveal ();
  let memf = update_heap128 ptr v mem in
  update_heap32_reveal ();
  // These two lines are apparently needed
  let mem1 = update_heap32 ptr v.lo0 mem in
  assert (Set.equal (Map.domain mem) (Map.domain mem1));
  assert (Set.equal (Map.domain mem) (Map.domain memf))

let same_mem_get_heap_val128 ptr mem1 mem2 =
  get_heap_val128_reveal ();
  same_mem_get_heap_val32 ptr mem1 mem2;
  same_mem_get_heap_val32 (ptr+4) mem1 mem2;
  same_mem_get_heap_val32 (ptr+8) mem1 mem2;
  same_mem_get_heap_val32 (ptr+12) mem1 mem2

