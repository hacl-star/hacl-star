module Vale.X64.Bytes_Semantics
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
open Vale.X64.Instruction_s

//(* All the following lemmas prove that the domain of the bytes memory map remains invariant
//through execution *)
//
//let update_operand_flags_same_domains (dst:operand64) (v:nat64) (s_orig s:machine_state) : Lemma
//  (let s1 = update_operand64_preserve_flags'' dst v s_orig s in
//  Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s_orig.ms_heap)) ==>
//  Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s1.ms_heap)))
//  [SMTPat (update_operand64_preserve_flags'' dst v s_orig s)]
//  =
//  reveal_opaque (`%valid_addr64) valid_addr64;
//  match dst with
//  | OMem _ -> update_heap64_reveal ()
//  | _ -> ()
//
//let update_operand_same_domains (dst:operand64) (ins:ins) (v:nat64) (s:machine_state) : Lemma
//  (let s1 = update_operand64' dst ins v s in
//  Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s1.ms_heap)))
//  [SMTPat (update_operand64' dst ins v s)]
//  =
//  update_operand_flags_same_domains dst v s s
//
//#set-options "--z3rlimit 20"
//let update_operand128_flags_same_domains (o:operand128) (v:quad32) (s_orig s:machine_state) : Lemma
//  ( let s1 = update_operand128_preserve_flags'' o v s_orig s in
//    Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s_orig.ms_heap)) ==>
//    Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s1.ms_heap)))
//  [SMTPat (update_operand128_preserve_flags'' o v s_orig s)]
//  =
//  reveal_opaque (`%valid_addr128) valid_addr128;
//  update_heap128_reveal ();
//  match o with
//  | OMem (m, t) ->
//      let ptr = eval_maddr m s_orig in
//      if not (valid_addr128 ptr (heap_get s.ms_heap)) then ()
//      else
//        // This line is unusued, but needed
//        let s1 = update_mem128_and_taint ptr v s t in
//        update_heap32_reveal ();
//        let mem = update_heap32 ptr v.lo0 (heap_get s.ms_heap) in
//        assert (Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain mem));
//        let mem = update_heap32 (ptr+4) v.lo1 mem in
//        assert (Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain mem));
//        let mem = update_heap32 (ptr+8) v.hi2 mem in
//        assert (Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain mem));
//        let mem = update_heap32 (ptr+12) v.hi3 mem in
//        assert (Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain mem))
//  | _ -> ()
//
//(* The following lemmas prove that the unspecified heap remains invariant through execution *)
//
//#push-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
//let update_operand_flags_same_unspecified (dst:operand64) (v:nat64) (s_orig s:machine_state) : Lemma
//  (ensures (
//    let s1 = update_operand64_preserve_flags'' dst v s_orig s in
//    Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s_orig.ms_heap)) ==>
//      (forall x.{:pattern ((heap_get s.ms_heap).[x])}
//        not (Map.contains (heap_get s1.ms_heap) x && Map.contains (heap_get s.ms_heap) x) ==>
//          (heap_get s1.ms_heap).[x] == (heap_get s.ms_heap).[x])
//  ))
//  [SMTPat (update_operand64_preserve_flags'' dst v s_orig s)]
//  =
//  match dst with
//  | OMem _ -> update_heap64_reveal ()
//  | _ -> ()
//#pop-options
//
//let update_operand_same_unspecified (dst:operand64) (ins:ins) (v:nat64) (s:machine_state) : Lemma
//  (let s1 = update_operand64' dst ins v s in
//  forall x.{:pattern ((heap_get s.ms_heap).[x])} not (Map.contains (heap_get s1.ms_heap) x && Map.contains (heap_get s.ms_heap) x) ==> (heap_get s1.ms_heap).[x] == (heap_get s.ms_heap).[x])
//  [SMTPat (update_operand64' dst ins v s)]
//  =
//  update_operand_flags_same_unspecified dst v s s
//
//let update_heap32_same_unspecified (ptr:int) (v:nat32) (h:machine_heap) : Lemma
//  (requires
//    valid_addr ptr h /\ valid_addr (ptr+1) h /\
//    valid_addr (ptr+2) h /\ valid_addr (ptr+3) h)
//  (ensures (
//    let h1 = update_heap32 ptr v h in
//    (forall x. valid_addr x h <==> valid_addr x h1) /\
//    (forall x. not (Map.contains h1 x && Map.contains h x) ==> h1.[x] == h.[x]))
//  )
//  =
//  update_heap32_reveal ()
//
//let update_operand128_flags_same_unspecified (o:operand128) (v:quad32) (s_orig s:machine_state) : Lemma
//  (let s1 = update_operand128_preserve_flags'' o v s_orig s in
//  Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s_orig.ms_heap)) ==>
//  (forall x.{:pattern ((heap_get s.ms_heap).[x])} not (Map.contains (heap_get s1.ms_heap) x && Map.contains (heap_get s.ms_heap) x) ==> (heap_get s1.ms_heap).[x] == (heap_get s.ms_heap).[x]))
//  [SMTPat (update_operand128_preserve_flags'' o v s_orig s)]
//  =
//  reveal_opaque (`%valid_addr128) valid_addr128;
//  update_heap128_reveal ();
//  match o with
//  | OMem (m, t) ->
//      let ptr = eval_maddr m s_orig in
//      if not (valid_addr128 ptr (heap_get s.ms_heap)) then ()
//      else
//        // This line is unusued, but needed
//        let s1 = update_mem128_and_taint ptr v s t in
//        update_heap32_same_unspecified ptr v.lo0 (heap_get s.ms_heap);
//        let mem = update_heap32 ptr v.lo0 (heap_get s.ms_heap) in
//        update_heap32_same_unspecified (ptr+4) v.lo1 mem;
//        let mem = update_heap32 (ptr+4) v.lo1 mem in
//        update_heap32_same_unspecified (ptr+8) v.hi2 mem;
//        let mem = update_heap32 (ptr+8) v.hi2 mem in
//        update_heap32_same_unspecified (ptr+12) v.hi3 mem;
//        let mem = update_heap32 (ptr+12) v.hi3 mem in
//        ()
//  | _ -> ()
//
//let rec instr_write_outputs_bs_domains
//    (outs:list instr_out) (args:list instr_operand)
//    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:machine_state)
//  : Lemma
//    (requires Set.equal (Map.domain (heap_get s_orig.ms_heap)) (Map.domain (heap_get s.ms_heap)))
//    (ensures (
//      let s1 = instr_write_outputs outs args vs oprs s_orig s in
//      Set.equal (Map.domain (heap_get s.ms_heap)) (Map.domain (heap_get s1.ms_heap)) /\
//      (forall (x:int).{:pattern ((heap_get s.ms_heap).[x])} not (Map.contains (heap_get s1.ms_heap) x) ==> (heap_get s1.ms_heap).[x] == (heap_get s.ms_heap).[x])
//    ))
//    [SMTPat (instr_write_outputs outs args vs oprs s_orig s)]
//  =
//  match outs with
//  | [] -> ()
//  | (b, i)::outs ->
//    (
//      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
//        match outs with
//        | [] -> (vs, ())
//        | _::_ -> coerce #(instr_val_t i & instr_ret_t outs) #(instr_ret_t ((b, i)::outs)) vs
//        in
//      match i with
//      | IOpEx i ->
//        let oprs = coerce oprs in
//        let s = instr_write_output_explicit i v (fst oprs) s_orig s in
//        instr_write_outputs_bs_domains outs args vs (snd oprs) s_orig s
//      | IOpIm i ->
//        let s' = instr_write_output_implicit i v s_orig s in
//        instr_write_outputs_bs_domains outs args vs (coerce oprs) s_orig s'
//    )
//
//#set-options "--z3rlimit 30 --max_ifuel 2"
//
//let eval_ins_bs_domains (ins:ins) (s0:machine_state) : Lemma
//  (let s1 = run (machine_eval_ins_st ins) s0 in
//  Set.equal (Map.domain (heap_get s0.ms_heap)) (Map.domain (heap_get s1.ms_heap)))
//  =
//  let s1 = run (machine_eval_ins_st ins) s0 in
//  match ins with
//  | _ -> assert (Set.equal (Map.domain (heap_get s0.ms_heap)) (Map.domain (heap_get s1.ms_heap)))
//
//#set-options "--z3rlimit 30"
//
//let eval_ins_domains i s0 =
//  eval_ins_bs_domains i s0
//
//#set-options "--z3rlimit 30 --max_ifuel 2"
//let eval_ins_bs_same_unspecified (ins:ins) (s0:machine_state) : Lemma
//  (let s1 = run (machine_eval_ins_st ins) s0 in
//   forall x. not (Map.contains (heap_get s1.ms_heap) x) ==> (heap_get s1.ms_heap).[x] == (heap_get s0.ms_heap).[x])
//  =
//  ()
//#set-options "--z3rlimit 30 --max_ifuel 1"
//
//let eval_ins_same_unspecified i s0 =
//  let s = {s0 with ms_trace = []} in
//  eval_ins_bs_same_unspecified i s

