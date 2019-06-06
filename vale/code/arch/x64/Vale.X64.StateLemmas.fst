module Vale.X64.StateLemmas
open Vale.X64.Machine_s
open Vale.X64.State
module BS = Vale.X64.Machine_Semantics_s
module MS = Vale.X64.Memory_Sems
module ME = Vale.X64.Memory
module VST = Vale.X64.Stack_i
module VSS = Vale.X64.Stack_Sems
module F = FStar.FunctionalExtensionality

#reset-options "--initial_fuel 2 --max_fuel 2"

let same_domain sv s = MS.same_domain sv.vs_mem s.BS.ms_mem

let same_domain_eval_ins c f s0 sv =
  match c with
  | Ins ins ->
    let obs = BS.ins_obs ins s0 in
    let s1 = {BS.machine_eval_ins ins ({s0 with BS.ms_trace = []}) with BS.ms_trace = obs @ s0.BS.ms_trace} in
    Vale.X64.Bytes_Semantics.eval_ins_domains ins ({s0 with BS.ms_trace = []});
    MS.lemma_same_domains sv.vs_mem s0.BS.ms_mem s1.BS.ms_mem

let state_to_S (s:vale_state) : GTot BS.machine_state =
  {
    BS.ms_ok = s.vs_ok;
    BS.ms_regs = F.on_dom reg (fun r -> Regs.sel r s.vs_regs);
    BS.ms_xmms = F.on_dom xmm (fun x -> Xmms.sel x s.vs_xmms);
    BS.ms_flags = F.on_dom flag (fun f -> Flags.sel f s.vs_flags);
    BS.ms_mem = MS.get_heap s.vs_mem;
    BS.ms_memTaint = s.vs_memTaint;
    BS.ms_stack = VSS.stack_to_s s.vs_stack;
    BS.ms_stackTaint = s.vs_stackTaint;
    BS.ms_trace = [];
  }

let state_of_S (sv:vale_state) (s:BS.machine_state{same_domain sv s}) : GTot vale_state =
  let { BS.ms_ok = ok; BS.ms_regs = regs; BS.ms_xmms = xmms; BS.ms_flags = flags; BS.ms_mem = mem; BS.ms_stack = stack} = s in
  {
    vs_ok = ok;
    vs_regs = Regs.of_fun regs;
    vs_xmms = Xmms.of_fun xmms;
    vs_flags = Flags.of_fun flags;
    vs_mem = MS.get_hs sv.vs_mem mem;
    vs_memTaint = s.BS.ms_memTaint;
    vs_stack = VSS.stack_from_s stack;
    vs_stackTaint = s.BS.ms_stackTaint;
  }

let lemma_to_ok s = ()
let lemma_to_flags s f = ()

let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_mem s = ()
let lemma_to_stack s = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()
let lemma_to_stackTaint s = ()

#set-options "--max_ifuel 2 --initial_ifuel 2"
let lemma_to_eval_operand s o =
  match o with
  | OConst _ | OReg _ -> ()
  | OMem (m, _) ->
    let addr = eval_maddr m s in
    MS.equiv_load_mem addr s.vs_mem
  | OStack (m, _) -> ()

#reset-options "--initial_fuel 2 --max_fuel 2"

let lemma_to_eval_xmm s x = ()

#set-options "--max_ifuel 2 --initial_ifuel 2"
let lemma_to_eval_operand128 s o =
  match o with
  | OConst _ | OReg _ -> ()
  | OMem (m, _) ->
    let addr = eval_maddr m s in
    MS.equiv_load_mem128 addr s.vs_mem
  | OStack (m, _) -> ()

#reset-options "--initial_fuel 2 --max_fuel 2"

let lemma_to_valid_operand s o =
  match o with
  | OConst _ | OReg _ -> ()
  | OMem (m, _) -> let addr = eval_maddr m s in
    let aux () : Lemma
      (requires valid_src_operand o s)
      (ensures BS.valid_src_operand o (state_to_S s)) =
      MS.bytes_valid addr s.vs_mem
      in
    Classical.move_requires aux ()
  | OStack (m, _) -> ()

let lemma_to_valid_taint s o t = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S s (state_to_S s)));
  ()

let lemma_to_of_eval_ins c s0 =
  let s0' = state_to_S s0 in
  let Ins ins = c in
  let Some sM = BS.machine_eval_code c 0 s0' in
  same_domain_eval_ins c 0 s0' s0;
  let s' = state_of_S s0 sM in
  let s'' = state_to_S s' in
  let { BS.ms_ok = ok; BS.ms_regs = regs; BS.ms_xmms = xmms; BS.ms_flags = flags; BS.ms_mem = heap; BS.ms_stack = stack} = sM in
  let { BS.ms_ok = ok''; BS.ms_regs = regs''; BS.ms_xmms = xmms''; BS.ms_flags = flags''; BS.ms_mem = heap''; BS.ms_stack = stack''} = s'' in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  assert (feq flags flags'');
  Vale.X64.Bytes_Semantics.eval_ins_same_unspecified ins s0';
  Vale.X64.Bytes_Semantics.eval_ins_domains ins s0';
  VSS.lemma_stack_to_from stack;
  MS.get_heap_hs heap s0.vs_mem

val lemma_valid_taint64: (b:ME.buffer64) ->
                         (memTaint:ME.memtaint) ->
                         (mem:ME.mem) ->
                         (i:nat{i < ME.buffer_length b}) ->
                         (t:taint) -> Lemma
  (requires ME.valid_taint_buf64 b mem memTaint t /\ ME.buffer_readable mem b)
  (ensures memTaint.[ME.buffer_addr b mem + 8 `op_Multiply` i] == t)

val lemma_valid_taint128: (b:ME.buffer128) ->
                         (memTaint:ME.memtaint) ->
                         (mem:ME.mem) ->
                         (i:nat{i < ME.buffer_length b}) ->
                         (t:taint) -> Lemma
  (requires ME.valid_taint_buf128 b mem memTaint t /\ ME.buffer_readable mem b)
  (ensures memTaint.[ME.buffer_addr b mem + 16 `op_Multiply` i] == t /\
           memTaint.[ME.buffer_addr b mem + 16 `op_Multiply` i + 8] == t)


val same_memTaint64: (b:ME.buffer64) ->
                   (mem0:ME.mem) ->
                   (mem1:ME.mem) ->
                   (memtaint0:ME.memtaint) ->
                   (memtaint1:ME.memtaint) -> Lemma
  (requires (ME.modifies (ME.loc_buffer b) mem0 mem1 /\
    (forall p. Map.sel memtaint0 p == Map.sel memtaint1 p)))
  (ensures memtaint0 == memtaint1)

val same_memTaint128: (b:ME.buffer128) ->
                   (mem0:ME.mem) ->
                   (mem1:ME.mem) ->
                   (memtaint0:ME.memtaint) ->
                   (memtaint1:ME.memtaint) -> Lemma
  (requires (ME.modifies (ME.loc_buffer b) mem0 mem1 /\
    (forall p. Map.sel memtaint0 p == Map.sel memtaint1 p)))
  (ensures memtaint0 == memtaint1)

let lemma_valid_taint64 = ME.lemma_valid_taint64
let lemma_valid_taint128  = ME.lemma_valid_taint128

let same_memTaint64 = ME.same_memTaint64
let same_memTaint128 = ME.same_memTaint128
