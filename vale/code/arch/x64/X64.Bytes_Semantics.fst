module X64.Bytes_Semantics
open Opaque_s
open Views

#reset-options "--z3rlimit 100 --max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

let nat32_to_nat8s (n:nat32) : nat8*nat8*nat8*nat8 =
  let v1 = n % 0x100 in
  let n = n / 0x100 in
  let v2 = n % 0x100 in
  let n = n / 0x100 in
  let v3 = n % 0x100 in
  let n = n / 0x100 in
  let v4 = n % 0x100 in
  (v1, v2, v3, v4)

#reset-options "--z3rlimit 70"
let nat32_to_nat8s_to_nat32 (v1 v2 v3 v4:nat8) :
  Lemma (nat32_to_nat8s (nat8s_to_nat32 v1 v2 v3 v4) = (v1, v2, v3, v4))
  =
  ()

let nat8s_to_nat32_injective (v1 v2 v3 v4 v1' v2' v3' v4':nat8) :
  Lemma (nat8s_to_nat32 v1 v2 v3 v4 == nat8s_to_nat32 v1' v2' v3' v4' ==>
         v1 == v1' /\
         v2 == v2' /\
         v3 == v3' /\
         v4 == v4')
  =
  nat32_to_nat8s_to_nat32 v1 v2 v3 v4;
  nat32_to_nat8s_to_nat32 v1' v2' v3' v4'

let nat8s_to_nat64_alt (v1 v2 v3 v4 v5 v6 v7 v8:nat8) : nat64 =
  nat8s_to_nat32 v1 v2 v3 v4
  +
  pow2_32 `op_Multiply` nat8s_to_nat32 v5 v6 v7 v8

let nat8s_to_nat64_alt_equiv (v1 v2 v3 v4 v5 v6 v7 v8:nat8) :
  Lemma (nat8s_to_nat64_alt v1 v2 v3 v4 v5 v6 v7 v8 == nat8s_to_nat64 v1 v2 v3 v4 v5 v6 v7 v8)
  =
  ()

let nat64_to_nat8s (n:nat64) : nat8*nat8*nat8*nat8*nat8*nat8*nat8*nat8 =
  let lower = n % 0x100000000 in
  let upper = (n / 0x100000000) % 0x100000000 in
  let (v1, v2, v3, v4) = nat32_to_nat8s lower in
  let (v5, v6, v7, v8) = nat32_to_nat8s upper in
  (v1, v2, v3, v4, v5, v6, v7, v8)

#push-options "--z3rlimit 60 --z3refresh"
let nat64_to_nat8s_to_nat64_alt (v1 v2 v3 v4 v5 v6 v7 v8:nat8) :
  Lemma (nat64_to_nat8s (nat8s_to_nat64_alt v1 v2 v3 v4 v5 v6 v7 v8) == (v1, v2, v3, v4, v5, v6, v7, v8))
  =
  nat32_to_nat8s_to_nat32 v1 v2 v3 v4;
  nat32_to_nat8s_to_nat32 v5 v6 v7 v8;
  ()
#pop-options

let nat64_to_nat8s_to_nat64 (v1 v2 v3 v4 v5 v6 v7 v8:nat8) :
  Lemma (nat64_to_nat8s (nat8s_to_nat64 v1 v2 v3 v4 v5 v6 v7 v8) == (v1, v2, v3, v4, v5, v6, v7, v8))
  =
  nat8s_to_nat64_alt_equiv v1 v2 v3 v4 v5 v6 v7 v8;
  nat64_to_nat8s_to_nat64_alt v1 v2 v3 v4 v5 v6 v7 v8;
  ()

#reset-options "--z3rlimit 20"
let nat8s_to_nat64_injective (v1 v2 v3 v4 v5 v6 v7 v8 v1' v2' v3' v4' v5' v6' v7' v8':nat8) :
  Lemma (nat8s_to_nat64 v1 v2 v3 v4 v5 v6 v7 v8 ==
         nat8s_to_nat64 v1' v2' v3' v4' v5' v6' v7' v8' ==>
         v1 == v1' /\
         v2 == v2' /\
         v3 == v3' /\
         v4 == v4' /\
         v5 == v5' /\
         v6 == v6' /\
         v7 == v7' /\
         v8 == v8')
  =
  nat64_to_nat8s_to_nat64 v1 v2 v3 v4 v5 v6 v7 v8;
  nat64_to_nat8s_to_nat64 v1' v2' v3' v4' v5' v6' v7' v8'

let same_mem_get_heap_val (ptr:int) (mem1 mem2:heap) =
  reveal_opaque get_heap_val64_def;
  nat8s_to_nat64_injective
      mem1.[ptr]
      mem1.[ptr+1]
      mem1.[ptr+2]
      mem1.[ptr+3]
      mem1.[ptr+4]
      mem1.[ptr+5]
      mem1.[ptr+6]
      mem1.[ptr+7]
      mem2.[ptr]
      mem2.[ptr+1]
      mem2.[ptr+2]
      mem2.[ptr+3]
      mem2.[ptr+4]
      mem2.[ptr+5]
      mem2.[ptr+6]
      mem2.[ptr+7]

let frame_update_heap ptr v mem =
  reveal_opaque get_heap_val64_def;
  reveal_opaque update_heap64_def

let correct_update_get ptr v mem =
  reveal_opaque get_heap_val64_def;
  reveal_opaque update_heap64_def

let same_domain_update ptr v mem =
  reveal_opaque update_heap64_def;
  let mem2 = update_heap64 ptr v mem in
  assert (Set.equal (Map.domain mem) (Map.domain mem2))

(*
// Verifies, but it's not as useful as hoped
#reset-options "--max_fuel 5 --initial_fuel 5"
let nat8s_to_nat32_is_get32 (v1 v2 v3 v4:nat8) :
  Lemma (let s = [U8.uint_to_t v1;
                  U8.uint_to_t v2;
                  U8.uint_to_t v3;
                  U8.uint_to_t v4] in
         let s = Seq.of_list s in
         Seq.length s == 4 /\
         nat8s_to_nat32 v1 v2 v3 v4 == UInt32.v (get32 s))
  =
  let s = [U8.uint_to_t v1;
           U8.uint_to_t v2;
           U8.uint_to_t v3;
           U8.uint_to_t v4] in
  let s' = Seq.of_list s in
  assert (List.length s == 4);  // OBSERVE
  assert (Seq.length s' == 4);
  assert (U8.v (List.index s 0) == v1);  // OBSERVE
  assert (U8.v (Seq.index s' 0) == v1);
  assert (U8.v (List.index s 1) == v2);  // OBSERVE
  assert (U8.v (Seq.index s' 1) == v2);
  assert (U8.v (List.index s 2) == v3);  // OBSERVE
  assert (U8.v (Seq.index s' 2) == v3);
  assert (U8.v (List.index s 3) == v4);  // OBSERVE
  assert (U8.v (Seq.index s' 3) == v4);
  reveal_opaque get32_def;
  ()


let get32_injective (s1 s2:Seq.lseq U8.t 4) :
  Lemma (get32 s1 == get32 s2 ==> s1 == s2)
  =
  let specific (s:Seq.lseq U8.t 4) :
    Lemma (put32 (get32 s) == s)
    =
    inverses32()
  in
  Meta.generic_injective_proof #(Seq.lseq U8.t 4) #UInt32.t get32 put32 specific

*)

let same_mem_get_heap_val32 ptr mem1 mem2 =
  reveal_opaque get_heap_val32_def;
  nat8s_to_nat32_injective
    mem1.[ptr]
    mem1.[ptr+1]
    mem1.[ptr+2]
    mem1.[ptr+3]
    mem2.[ptr]
    mem2.[ptr+1]
    mem2.[ptr+2]
    mem2.[ptr+3]

let frame_update_heap32 (ptr:int) (v:nat32) (mem:heap) : Lemma
  (let mem' = update_heap32 ptr v mem in
  forall i. i < ptr \/ i >= ptr + 4 ==> mem.[i] == mem'.[i]) =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

let frame_update_heap128 ptr v s =
  let mem1 = update_heap32 ptr v.lo0 s.mem in
  frame_update_heap32 ptr v.lo0 s.mem;
  let mem2 = update_heap32 (ptr+4) v.lo1 mem1 in
  frame_update_heap32 (ptr+4) v.lo1 mem1;
  let mem3 = update_heap32 (ptr+8) v.hi2 mem2 in
  frame_update_heap32 (ptr+8) v.hi2 mem2;
  let mem4 = update_heap32 (ptr+12) v.hi3 mem3 in
  frame_update_heap32 (ptr+12) v.hi3 mem3

let correct_update_get32 (ptr:int) (v:nat32) (mem:heap) : Lemma
  (get_heap_val32 ptr (update_heap32 ptr v mem) == v) =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

#reset-options "--z3rlimit 30 --using_facts_from 'Prims Opaque_s X64.Bytes_Semantics_s Words_s Types_s'"

let correct_update_get128 ptr v s =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def;
  let mem1 = update_heap32 ptr v.lo0 s.mem in
  frame_update_heap32 ptr v.lo0 s.mem;
  correct_update_get32 ptr v.lo0 s.mem;
  let mem2 = update_heap32 (ptr+4) v.lo1 mem1 in
  frame_update_heap32 (ptr+4) v.lo1 mem1;
  correct_update_get32 (ptr+4) v.lo1 mem1;
  let mem3 = update_heap32 (ptr+8) v.hi2 mem2 in
  frame_update_heap32 (ptr+8) v.hi2 mem2;
  correct_update_get32 (ptr+8) v.hi2 mem2;
  let mem4 = update_heap32 (ptr+12) v.hi3 mem3 in
  frame_update_heap32 (ptr+12) v.hi3 mem3;
  correct_update_get32 (ptr+12) v.hi3 mem3

#reset-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

let same_domain_update128 ptr v mem =
  let memf = update_heap128 ptr v mem in
  reveal_opaque update_heap32_def;
  // These two lines are apparently needed
  let mem1 = update_heap32 ptr v.lo0 mem in
  assert (Set.equal (Map.domain mem) (Map.domain mem1));
  assert (Set.equal (Map.domain mem) (Map.domain memf))
