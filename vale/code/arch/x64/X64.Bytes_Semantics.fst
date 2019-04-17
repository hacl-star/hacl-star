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
open X64.Instruction_s

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

let update_operand_flags_same_domains (dst:operand) (v:nat64) (s_orig s:state) : Lemma
  (let s1 = update_operand_preserve_flags'' dst v s_orig s in
  Set.equal (Map.domain s.mem) (Map.domain s_orig.mem) ==>
  Set.equal (Map.domain s.mem) (Map.domain s1.mem))
  [SMTPat (update_operand_preserve_flags'' dst v s_orig s)]
  =
  match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()

let update_operand_same_domains (dst:operand) (ins:ins) (v:nat64) (s:state) : Lemma
  (let s1 = update_operand' dst ins v s in
  Set.equal (Map.domain s.mem) (Map.domain s1.mem))
  [SMTPat (update_operand' dst ins v s)]
  =
  update_operand_flags_same_domains dst v s s

#set-options "--z3rlimit 20"
let update_operand128_flags_same_domains (o:mov128_op) (v:quad32) (s_orig s:state) : Lemma
  (let s1 = update_mov128_op_preserve_flags'' o v s_orig s in
  Set.equal (Map.domain s.mem) (Map.domain s_orig.mem) ==>
  Set.equal (Map.domain s.mem) (Map.domain s1.mem))
  [SMTPat (update_mov128_op_preserve_flags'' o v s_orig s)]
  =
  match o with
  | Mov128Mem m ->
      let ptr = eval_maddr m s_orig in
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

(* The following lemmas prove that the unspecified heap remains invariant through execution *)

#push-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
let update_operand_flags_same_unspecified (dst:operand) (v:nat64) (s_orig s:state) : Lemma
  (let s1 = update_operand_preserve_flags'' dst v s_orig s in
  Set.equal (Map.domain s.mem) (Map.domain s_orig.mem) ==>
  (forall x.{:pattern (s.mem.[x])} not (Map.contains s1.mem x && Map.contains s.mem x) ==> s1.mem.[x] == s.mem.[x]))
  [SMTPat (update_operand_preserve_flags'' dst v s_orig s)]
  =
  match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()
#pop-options

let update_operand_same_unspecified (dst:operand) (ins:ins) (v:nat64) (s:state) : Lemma
  (let s1 = update_operand' dst ins v s in
  forall x.{:pattern (s.mem.[x])} not (Map.contains s1.mem x && Map.contains s.mem x) ==> s1.mem.[x] == s.mem.[x])
  [SMTPat (update_operand' dst ins v s)]
  =
  update_operand_flags_same_unspecified dst v s s

let update_heap32_same_unspecified (ptr:int) (v:nat32) (h:heap) : Lemma
  (requires 
    valid_addr ptr h /\ valid_addr (ptr+1) h /\
    valid_addr (ptr+2) h /\ valid_addr (ptr+3) h)
  (ensures (
    let h1 = update_heap32 ptr v h in
    (forall x. valid_addr x h <==> valid_addr x h1) /\
    (forall x. not (Map.contains h1 x && Map.contains h x) ==> h1.[x] == h.[x]))
  )
  =
  reveal_opaque update_heap32_def

let update_operand128_flags_same_unspecified (o:mov128_op) (v:quad32) (s_orig s:state) : Lemma
  (let s1 = update_mov128_op_preserve_flags'' o v s_orig s in
  Set.equal (Map.domain s.mem) (Map.domain s_orig.mem) ==>
  (forall x.{:pattern (s.mem.[x])} not (Map.contains s1.mem x && Map.contains s.mem x) ==> s1.mem.[x] == s.mem.[x]))
  [SMTPat (update_mov128_op_preserve_flags'' o v s_orig s)]
  =
  match o with
  | Mov128Mem m ->
      let ptr = eval_maddr m s_orig in
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

let rec instr_write_outputs_bs_domains
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:state)
  : Lemma
    (requires Set.equal (Map.domain s_orig.mem) (Map.domain s.mem))
    (ensures (
      let s1 = instr_write_outputs outs args vs oprs s_orig s in
      Set.equal (Map.domain s.mem) (Map.domain s1.mem) /\
      (forall (x:int).{:pattern (s.mem.[x])} not (Map.contains s1.mem x) ==> s1.mem.[x] == s.mem.[x])
    ))
    [SMTPat (instr_write_outputs outs args vs oprs s_orig s)]
  =
  match outs with
  | [] -> ()
  | (b, i)::outs ->
    (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> coerce #(instr_val_t i & instr_ret_t outs) #(instr_ret_t ((b, i)::outs)) vs
        in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        let s = instr_write_output_explicit i v (fst oprs) s_orig s in
        instr_write_outputs_bs_domains outs args vs (snd oprs) s_orig s
      | IOpIm i ->
        let s' = instr_write_output_implicit i v s_orig s in
        instr_write_outputs_bs_domains outs args vs (coerce oprs) s_orig s'
    )

#set-options "--z3rlimit 30 --max_ifuel 2"

// TODO: get rid of this when we've removed most cases from the ins datatype
let eval_ins_bs_domains_Ins (ins) (s0:state) : Lemma
  (requires
    Ins_64_64_preserve? ins \/
    Ins_io64_64? ins \/
    Ins_io64_64_cf? ins \/
    Ins_ioXmm? ins \/
    Ins_Xmm_Xmm? ins \/
    Ins_ioXmm_Xmm? ins
  )
  (ensures (
    let s1 = run (eval_ins ins) s0 in
    Set.equal (Map.domain s0.mem) (Map.domain s1.mem)
  ))
  =
  ()

#set-options "--z3rlimit 30 --max_ifuel 1"

let eval_ins_bs_domains (ins:ins) (s0:state) : Lemma
  (let s1 = run (eval_ins ins) s0 in
  Set.equal (Map.domain s0.mem) (Map.domain s1.mem))
  =
  let s1 = run (eval_ins ins) s0 in
  match ins with
  | Ins_64_64_preserve _ _ _  -> eval_ins_bs_domains_Ins ins s0
  | Ins_io64_64 _ _ _ -> eval_ins_bs_domains_Ins ins s0
  | Ins_io64_64_cf _ _ _ -> eval_ins_bs_domains_Ins ins s0
  | Ins_ioXmm _ _ -> eval_ins_bs_domains_Ins ins s0
  | Ins_Xmm_Xmm _ _ _ -> eval_ins_bs_domains_Ins ins s0
  | Ins_ioXmm_Xmm _ _ _ -> eval_ins_bs_domains_Ins ins s0
  | _ -> assert (Set.equal (Map.domain s0.mem) (Map.domain s1.mem))

#set-options "--z3rlimit 30"

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

#set-options "--z3rlimit 30 --max_ifuel 2"
let eval_ins_bs_same_unspecified (ins:ins) (s0:state) : Lemma
  (let s1 = run (eval_ins ins) s0 in
   forall x. not (Map.contains s1.mem x) ==> s1.mem.[x] == s0.mem.[x])
  =
  ()
#set-options "--z3rlimit 30 --max_ifuel 1"

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
