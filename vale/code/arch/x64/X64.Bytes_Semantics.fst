module X64.Bytes_Semantics
open Opaque_s
open Views_s

#reset-options "--z3rlimit 100 --max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

let nat32_to_nat8s_def (n:nat32) : nat8*nat8*nat8*nat8 =
  let v1 = n % 0x100 in
  let n = n / 0x100 in
  let v2 = n % 0x100 in
  let n = n / 0x100 in
  let v3 = n % 0x100 in
  let n = n / 0x100 in
  let v4 = n % 0x100 in
  (v1, v2, v3, v4)
let nat32_to_nat8s = make_opaque nat32_to_nat8s_def

#reset-options "--z3rlimit 70"
let nat32_to_nat8s_to_nat32 (v1 v2 v3 v4:nat8) :
  Lemma (nat32_to_nat8s (nat8s_to_nat32 v1 v2 v3 v4) = (v1, v2, v3, v4))
  =
  reveal_opaque nat32_to_nat8s_def

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

#reset-options "--z3rlimit 100 --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"
let nat64_to_nat8s_to_nat64_alt (v1 v2 v3 v4 v5 v6 v7 v8:nat8) :
  Lemma (nat64_to_nat8s (nat8s_to_nat64_alt v1 v2 v3 v4 v5 v6 v7 v8) == (v1, v2, v3, v4, v5, v6, v7, v8))
  =
  nat32_to_nat8s_to_nat32 v1 v2 v3 v4;
  nat32_to_nat8s_to_nat32 v5 v6 v7 v8;
  ()

#reset-options "--z3rlimit 100 --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"
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
  Util.Meta.generic_injective_proof #(Seq.lseq U8.t 4) #UInt32.t get32 put32 specific

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

let update_operand_flags_same_unspecified dst v s = match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()

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
