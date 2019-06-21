module Vale.X64.Bytes_Semantics
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Two
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Seq
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.X64.Instruction_s

let same_mem_get_heap_val ptr mem1 mem2 =
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
  FStar.Pervasives.reveal_opaque (`%valid_addr64) valid_addr64;
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
  Vale.Def.Opaque_s.reveal_opaque update_heap128_def;
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
  reveal_opaque get_heap_val32_def;
  reveal_opaque update_heap32_def

#reset-options "--z3rlimit 30 --using_facts_from 'Prims Vale.Def.Opaque_s Vale.X64.Machine_Semantics_s Vale.Def.Words_s Vale.Def.Types_s'"

let correct_update_get128 ptr v mem =
  Vale.Def.Opaque_s.reveal_opaque update_heap128_def;
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
  FStar.Pervasives.reveal_opaque (`%valid_addr128) valid_addr128;
  Vale.Def.Opaque_s.reveal_opaque update_heap128_def;
  let memf = update_heap128 ptr v mem in
  reveal_opaque update_heap32_def;
  // These two lines are apparently needed
  let mem1 = update_heap32 ptr v.lo0 mem in
  assert (Set.equal (Map.domain mem) (Map.domain mem1));
  assert (Set.equal (Map.domain mem) (Map.domain memf))

let same_mem_get_heap_val128 ptr mem1 mem2 =
  Vale.Def.Opaque_s.reveal_opaque get_heap_val128_def;
  same_mem_get_heap_val32 ptr mem1 mem2;
  same_mem_get_heap_val32 (ptr+4) mem1 mem2;
  same_mem_get_heap_val32 (ptr+8) mem1 mem2;
  same_mem_get_heap_val32 (ptr+12) mem1 mem2

(* All the following lemmas prove that the domain of the bytes memory map remains invariant
through execution *)

let update_operand_flags_same_domains (dst:operand64) (v:nat64) (s_orig s:machine_state) : Lemma
  (let s1 = update_operand64_preserve_flags'' dst v s_orig s in
  Set.equal (Map.domain s.ms_heap) (Map.domain s_orig.ms_heap) ==>
  Set.equal (Map.domain s.ms_heap) (Map.domain s1.ms_heap))
  [SMTPat (update_operand64_preserve_flags'' dst v s_orig s)]
  =
  FStar.Pervasives.reveal_opaque (`%valid_addr64) valid_addr64;
  match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()

let update_operand_same_domains (dst:operand64) (ins:ins) (v:nat64) (s:machine_state) : Lemma
  (let s1 = update_operand64' dst ins v s in
  Set.equal (Map.domain s.ms_heap) (Map.domain s1.ms_heap))
  [SMTPat (update_operand64' dst ins v s)]
  =
  update_operand_flags_same_domains dst v s s

#set-options "--z3rlimit 20"
let update_operand128_flags_same_domains (o:operand128) (v:quad32) (s_orig s:machine_state) : Lemma
  ( let s1 = update_operand128_preserve_flags'' o v s_orig s in
    Set.equal (Map.domain s.ms_heap) (Map.domain s_orig.ms_heap) ==>
    Set.equal (Map.domain s.ms_heap) (Map.domain s1.ms_heap))
  [SMTPat (update_operand128_preserve_flags'' o v s_orig s)]
  =
  FStar.Pervasives.reveal_opaque (`%valid_addr128) valid_addr128;
  Vale.Def.Opaque_s.reveal_opaque update_heap128_def;
  match o with
  | OMem (m, t) ->
      let ptr = eval_maddr m s_orig in
      if not (valid_addr128 ptr s.ms_heap) then ()
      else
        // This line is unusued, but needed
        let s1 = update_mem128_and_taint ptr v s t in
        reveal_opaque update_heap32_def;
        let mem = update_heap32 ptr v.lo0 s.ms_heap in
        assert (Set.equal (Map.domain s.ms_heap) (Map.domain mem));
        let mem = update_heap32 (ptr+4) v.lo1 mem in
        assert (Set.equal (Map.domain s.ms_heap) (Map.domain mem));
        let mem = update_heap32 (ptr+8) v.hi2 mem in
        assert (Set.equal (Map.domain s.ms_heap) (Map.domain mem));
        let mem = update_heap32 (ptr+12) v.hi3 mem in
        assert (Set.equal (Map.domain s.ms_heap) (Map.domain mem))
  | _ -> ()

(* The following lemmas prove that the unspecified heap remains invariant through execution *)

#push-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
let update_operand_flags_same_unspecified (dst:operand64) (v:nat64) (s_orig s:machine_state) : Lemma
  (let s1 = update_operand64_preserve_flags'' dst v s_orig s in
  Set.equal (Map.domain s.ms_heap) (Map.domain s_orig.ms_heap) ==>
  (forall x.{:pattern (s.ms_heap.[x])} not (Map.contains s1.ms_heap x && Map.contains s.ms_heap x) ==> s1.ms_heap.[x] == s.ms_heap.[x]))
  [SMTPat (update_operand64_preserve_flags'' dst v s_orig s)]
  =
  match dst with
  | OMem _ -> reveal_opaque update_heap64_def
  | _ -> ()
#pop-options

let update_operand_same_unspecified (dst:operand64) (ins:ins) (v:nat64) (s:machine_state) : Lemma
  (let s1 = update_operand64' dst ins v s in
  forall x.{:pattern (s.ms_heap.[x])} not (Map.contains s1.ms_heap x && Map.contains s.ms_heap x) ==> s1.ms_heap.[x] == s.ms_heap.[x])
  [SMTPat (update_operand64' dst ins v s)]
  =
  update_operand_flags_same_unspecified dst v s s

let update_heap32_same_unspecified (ptr:int) (v:nat32) (h:machine_heap) : Lemma
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

let update_operand128_flags_same_unspecified (o:operand128) (v:quad32) (s_orig s:machine_state) : Lemma
  (let s1 = update_operand128_preserve_flags'' o v s_orig s in
  Set.equal (Map.domain s.ms_heap) (Map.domain s_orig.ms_heap) ==>
  (forall x.{:pattern (s.ms_heap.[x])} not (Map.contains s1.ms_heap x && Map.contains s.ms_heap x) ==> s1.ms_heap.[x] == s.ms_heap.[x]))
  [SMTPat (update_operand128_preserve_flags'' o v s_orig s)]
  =
  FStar.Pervasives.reveal_opaque (`%valid_addr128) valid_addr128;
  Vale.Def.Opaque_s.reveal_opaque update_heap128_def;
  match o with
  | OMem (m, t) ->
      let ptr = eval_maddr m s_orig in
      if not (valid_addr128 ptr s.ms_heap) then ()
      else
        // This line is unusued, but needed
        let s1 = update_mem128_and_taint ptr v s t in
        update_heap32_same_unspecified ptr v.lo0 s.ms_heap;
        let mem = update_heap32 ptr v.lo0 s.ms_heap in
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
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:machine_state)
  : Lemma
    (requires Set.equal (Map.domain s_orig.ms_heap) (Map.domain s.ms_heap))
    (ensures (
      let s1 = instr_write_outputs outs args vs oprs s_orig s in
      Set.equal (Map.domain s.ms_heap) (Map.domain s1.ms_heap) /\
      (forall (x:int).{:pattern (s.ms_heap.[x])} not (Map.contains s1.ms_heap x) ==> s1.ms_heap.[x] == s.ms_heap.[x])
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

let eval_ins_bs_domains (ins:ins) (s0:machine_state) : Lemma
  (let s1 = run (machine_eval_ins_st ins) s0 in
  Set.equal (Map.domain s0.ms_heap) (Map.domain s1.ms_heap))
  =
  let s1 = run (machine_eval_ins_st ins) s0 in
  match ins with
  | _ -> assert (Set.equal (Map.domain s0.ms_heap) (Map.domain s1.ms_heap))

#set-options "--z3rlimit 30"

let eval_ins_domains i s0 =
  eval_ins_bs_domains i s0

#set-options "--z3rlimit 30 --max_ifuel 2"
let eval_ins_bs_same_unspecified (ins:ins) (s0:machine_state) : Lemma
  (let s1 = run (machine_eval_ins_st ins) s0 in
   forall x. not (Map.contains s1.ms_heap x) ==> s1.ms_heap.[x] == s0.ms_heap.[x])
  =
  ()
#set-options "--z3rlimit 30 --max_ifuel 1"

let eval_ins_same_unspecified i s0 =
  let s = {s0 with ms_trace = []} in
  eval_ins_bs_same_unspecified i s
