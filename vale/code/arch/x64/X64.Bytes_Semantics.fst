module X64.Bytes_Semantics
open Opaque_s
open Words_s
open Words.Two_s
open Words.Two
open Words.Four_s
open Words.Seq_s
open Words.Seq
open Types_s
open Arch.Types

let same_mem_get_heap_val (ptr:int) (mem1 mem2:heap) =
  reveal_opaque get_heap_val64_def;
  four_to_nat_8_injective ();
  two_to_nat_32_injective ()

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

let same_mem_get_heap_val32 ptr mem1 mem2 =
  reveal_opaque get_heap_val32_def;
  four_to_nat_8_injective ()
  
let frame_update_heap32 ptr v mem =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

let same_domain_update32 ptr v mem =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def;
  assert (Set.equal (Map.domain mem) (Map.domain (update_heap32 ptr v mem)))

let update_heap32_get_heap32 ptr mem =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def;
  assert (Map.equal mem (update_heap32 ptr (get_heap_val32 ptr mem) mem))

let frame_update_heap128 ptr v mem =
  let mem1 = update_heap32 ptr v.lo0 mem in
  frame_update_heap32 ptr v.lo0 mem;
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

let correct_update_get128 ptr v mem =
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def;
  reveal_opaque get_heap_val128_def;
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
  let memf = update_heap128 ptr v mem in
  reveal_opaque update_heap32_def;
  // These two lines are apparently needed
  let mem1 = update_heap32 ptr v.lo0 mem in
  assert (Set.equal (Map.domain mem) (Map.domain mem1));
  assert (Set.equal (Map.domain mem) (Map.domain memf))

let same_mem_get_heap_val128 ptr mem1 mem2 =
  Opaque_s.reveal_opaque get_heap_val128_def;
  same_mem_get_heap_val32 ptr mem1 mem2;
  same_mem_get_heap_val32 (ptr+4) mem1 mem2;
  same_mem_get_heap_val32 (ptr+8) mem1 mem2;
  same_mem_get_heap_val32 (ptr+12) mem1 mem2  

(* All the following lemmas prove that the domain of the bytes memory map remains invariant
through execution *)

val update_operand_flags_same_domains (dst:operand) (v:nat64) (s:state) : Lemma
  (let s1 = update_operand_preserve_flags' dst v s in
  Set.equal (Map.domain s.mem) (Map.domain s1.mem))
  [SMTPat (update_operand_preserve_flags' dst v s)]

let update_operand_flags_same_domains dst v s = match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()

val update_operand_same_domains (dst:operand) (ins:ins) (v:nat64) (s:state) : Lemma
  (let s1 = update_operand' dst ins v s in
  Set.equal (Map.domain s.mem) (Map.domain s1.mem))
  [SMTPat (update_operand' dst ins v s)]

let update_operand_same_domains dst ins v s = update_operand_flags_same_domains dst v s

val update_operand128_flags_same_domains (o:mov128_op) (v:quad32) (s:state) : Lemma
  (let s1 = update_mov128_op_preserve_flags' o v s in
  Set.equal (Map.domain s.mem) (Map.domain s1.mem))
  [SMTPat (update_mov128_op_preserve_flags' o v s)]

#set-options "--z3rlimit 20"
let update_operand128_flags_same_domains o v s = match o with
  | Mov128Mem m ->
      let ptr = eval_maddr m s in
      if not (valid_addr128 ptr s.mem) then ()
      else
        // This line is unusued, but needed
        let s1 = update_mem128 ptr v s in
        reveal_opaque update_heap32_def;
        let mem = update_heap32 ptr v.lo0 s.mem in
        assert (Set.equal (Map.domain s.mem) (Map.domain mem));
        let mem = update_heap32 (ptr+4) v.lo1 mem in
        assert (Set.equal (Map.domain s.mem) (Map.domain mem));
        let mem = update_heap32 (ptr+8) v.hi2 mem in
        assert (Set.equal (Map.domain s.mem) (Map.domain mem));
        let mem = update_heap32 (ptr+12) v.hi3 mem in
        assert (Set.equal (Map.domain s.mem) (Map.domain mem))
  | _ -> ()

val eval_ins_bs_domains (ins:ins) (s0:state) : Lemma
  (let s1 = run (eval_ins ins) s0 in
  Set.equal (Map.domain s0.mem) (Map.domain s1.mem))

#set-options "--z3rlimit 30"

let eval_ins_bs_domains ins s0 = ()

let eval_ins_domains ins s0 =
  let t = ins.TS.t in
  let i = ins.TS.i in
  let dsts, srcs = TS.extract_operands i in
  let s = 
    if MOVDQU? i then 
      let MOVDQU dst src = ins.TS.i in
      run (check (TS.taint_match128 src t s0.TS.memTaint)) s0.TS.state
    else run (check (TS.taint_match_list srcs t s0.TS.memTaint)) s0.TS.state
  in
  eval_ins_bs_domains i s

(* The following lemmas prove that the unspecified heap remains invariant through execution *)

val update_operand_flags_same_unspecified (dst:operand) (v:nat64) (s:state) : Lemma
  (let s1 = update_operand_preserve_flags' dst v s in
  forall x. not (Map.contains s1.mem x && Map.contains s.mem x) ==> s1.mem.[x] == s.mem.[x])
  [SMTPat (update_operand_preserve_flags' dst v s)]

#push-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
let update_operand_flags_same_unspecified dst v s = match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()
#pop-options

val update_operand_same_unspecified (dst:operand) (ins:ins) (v:nat64) (s:state) : Lemma
  (let s1 = update_operand' dst ins v s in
  forall x. not (Map.contains s1.mem x && Map.contains s.mem x) ==> s1.mem.[x] == s.mem.[x])
  [SMTPat (update_operand' dst ins v s)]
  
let update_operand_same_unspecified dst ins v s = update_operand_flags_same_unspecified dst v s

val update_operand128_flags_same_unspecified (o:mov128_op) (v:quad32) (s:state) : Lemma
  (let s1 = update_mov128_op_preserve_flags' o v s in
  forall x. not (Map.contains s1.mem x && Map.contains s.mem x) ==> s1.mem.[x] == s.mem.[x])
  [SMTPat (update_mov128_op_preserve_flags' o v s)]

val update_heap32_same_unspecified (ptr:int) (v:nat32) (h:heap) : Lemma
  (requires 
    valid_addr ptr h /\ valid_addr (ptr+1) h /\
    valid_addr (ptr+2) h /\ valid_addr (ptr+3) h)
  (ensures (
    let h1 = update_heap32 ptr v h in
    (forall x. valid_addr x h <==> valid_addr x h1) /\
    (forall x. not (Map.contains h1 x && Map.contains h x) ==> h1.[x] == h.[x]))
  )
  
let update_heap32_same_unspecified ptr v h = reveal_opaque update_heap32_def

let update_operand128_flags_same_unspecified o v s = match o with
  | Mov128Mem m ->
      let ptr = eval_maddr m s in
      if not (valid_addr128 ptr s.mem) then ()
      else
        // This line is unusued, but needed
        let s1 = update_mem128 ptr v s in
        update_heap32_same_unspecified ptr v.lo0 s.mem;
        let mem = update_heap32 ptr v.lo0 s.mem in
        update_heap32_same_unspecified (ptr+4) v.lo1 mem;
        let mem = update_heap32 (ptr+4) v.lo1 mem in
        update_heap32_same_unspecified (ptr+8) v.hi2 mem;  
        let mem = update_heap32 (ptr+8) v.hi2 mem in
        update_heap32_same_unspecified (ptr+12) v.hi3 mem;  
        let mem = update_heap32 (ptr+12) v.hi3 mem in
        ()
  | _ -> ()

val eval_ins_bs_same_unspecified (ins:ins) (s0:state) : Lemma
  (let s1 = run (eval_ins ins) s0 in
   forall x. not (Map.contains s1.mem x) ==> s1.mem.[x] == s0.mem.[x])

let eval_ins_bs_same_unspecified ins s0 = ()

let eval_ins_same_unspecified ins s0 =
  let t = ins.TS.t in
  let i = ins.TS.i in
  let dsts, srcs = TS.extract_operands i in
  let s = 
    if MOVDQU? i then 
      let MOVDQU dst src = i in
      run (check (TS.taint_match128 src t s0.TS.memTaint)) s0.TS.state
    else run (check (TS.taint_match_list srcs t s0.TS.memTaint)) s0.TS.state
  in
  eval_ins_bs_same_unspecified i s
