module X64.Vale.StateLemmas
open X64.Machine_s
open X64.Vale.State
module BS = X64.Bytes_Semantics_s
module MS = X64.Memory_Sems
module ME = X64.Memory
module VST = X64.Stack_i
module VSS = X64.Stack_Sems
module TS = X64.Taint_Semantics_s

module F = FStar.FunctionalExtensionality

#reset-options "--initial_fuel 2 --max_fuel 2"

let same_domain sv s = MS.same_domain sv.mem s.TS.state.BS.mem

let same_domain_eval_ins c f s0 sv = match c with
  | Ins ins -> 
      let obs = TS.ins_obs ins s0 in 
      let s1 = {TS.taint_eval_ins ins s0 with TS.trace = obs @ s0.TS.trace} in
      X64.Bytes_Semantics.eval_ins_domains ins s0;
      MS.lemma_same_domains sv.mem s0.TS.state.BS.mem s1.TS.state.BS.mem

let state_to_S (s:state) : GTot TS.traceState =
  {
  TS.state = {
    BS.ok = s.ok;
    BS.regs = F.on_dom reg (fun r -> Regs.sel r s.regs);
    BS.xmms = F.on_dom xmm (fun x -> Xmms.sel x s.xmms);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = MS.get_heap s.mem;
    BS.stack = VSS.stack_to_s s.stack;
  };
  TS.trace = [];
  TS.memTaint = s.memTaint;
  }

let state_of_S (sv:state) (s:TS.traceState{same_domain sv s}) : GTot state =
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = mem; BS.stack = stack} = s.TS.state in
  {
    ok = ok;
    regs = Regs.of_fun regs;
    xmms = Xmms.of_fun xmms;
    flags = flags;
    mem = MS.get_hs sv.mem mem;
    stack = VSS.stack_from_s stack;
    memTaint = s.TS.memTaint;
  }

let lemma_to_ok s = ()
let lemma_to_flags s = ()

let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_mem s = ()
let lemma_to_stack s = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()

#set-options "--max_ifuel 2 --initial_ifuel 2"
let lemma_to_eval_operand s o = match o with
  | OConst _ | OReg _ -> ()
  | OMem m ->
    let addr = eval_maddr m s in
    MS.equiv_load_mem addr s.mem
  | OStack m -> ()

#reset-options "--initial_fuel 2 --max_fuel 2"

let lemma_to_eval_xmm s x = ()

#set-options "--max_ifuel 2 --initial_ifuel 2"
let lemma_to_eval_operand128 s o = match o with
  | Mov128Xmm _ -> ()
  | Mov128Mem m ->
    let addr = eval_maddr m s in
    MS.equiv_load_mem128 addr s.mem
  | Mov128Stack m -> () 

#reset-options "--initial_fuel 2 --max_fuel 2"

let lemma_to_valid_operand s o = match o with
  | OConst _ | OReg _ -> ()
  | OMem m -> let addr = eval_maddr m s in
    let aux () : Lemma
    (requires valid_src_operand o s)
    (ensures BS.valid_src_operand o (state_to_S s).TS.state) =
    MS.bytes_valid addr s.mem in
    Classical.move_requires aux ()
  | OStack m -> ()

let lemma_to_valid_taint s o t = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S s (state_to_S s)));
  ()

let lemma_to_of_eval_ins c s0 =
  let s0' = state_to_S s0 in
  let Ins ins = c in
  let Some sM = TS.taint_eval_code c 0 s0' in
  same_domain_eval_ins c 0 s0' s0;
  let s' = state_of_S s0 sM in
  let s'' = state_to_S s' in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = heap; BS.stack = stack} = sM.TS.state in
  let { BS.ok = ok''; BS.regs = regs''; BS.xmms = xmms''; BS.flags = flags''; BS.mem = heap''; BS.stack = stack''} = s''.TS.state in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  X64.Bytes_Semantics.eval_ins_same_unspecified ins s0';
  X64.Bytes_Semantics.eval_ins_domains ins s0';
  VSS.lemma_stack_to_from stack;
  MS.get_heap_hs heap s0.mem

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
