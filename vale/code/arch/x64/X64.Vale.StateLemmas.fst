module X64.Vale.StateLemmas
open X64.Machine_s
open X64.Vale.State
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_s
module TS = X64.Taint_Semantics_s
open X64.Semantics_Equiv

friend X64.Memory

#reset-options "--initial_fuel 2 --max_fuel 2"

let same_domain sv s = ME.same_domain sv.mem s.TS.state.BS.mem

let same_domain_eval_ins c f s0 sv = match c with
  | Ins ins -> 
      let obs = TS.ins_obs ins s0 in 
      let s1 = {TS.taint_eval_ins ins s0 with TS.trace = obs @ s0.TS.trace} in
      X64.Bytes_Semantics.eval_ins_domains ins s0;
      ME.lemma_same_domains sv.mem s0.TS.state.BS.mem s1.TS.state.BS.mem

let state_to_S (s:state) : GTot TS.traceState =
  {
  TS.state = {
    BS.ok = s.ok;
    BS.regs = (fun r -> s.regs r);
    BS.xmms = (fun x -> s.xmms x);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  };
  TS.trace = [];
  TS.memTaint = s.memTaint;
  }

let state_of_S (sv:state) (s:TS.traceState{same_domain sv s}) : GTot state =
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = mem} = s.TS.state in
  {
    ok = ok;
    regs = (fun r -> regs r);
    xmms = (fun x -> xmms x);
    flags = flags;
    mem = ME.get_hs sv.mem mem;
    memTaint = s.TS.memTaint;
  }

let lemma_to_ok s = ()
let lemma_to_flags s = ()
let lemma_to_mem s = ()

let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()

(*
let lemma_of_ok s = ()
let lemma_of_flags s = ()
let lemma_of_mem s = ()
let lemma_of_regs s = assert (feq (regs' s.TS.state) (state_of_S s).regs)
let lemma_of_xmms s = assert (feq (xmms' s.TS.state) (state_of_S s).xmms)
let lemma_of_memTaint s = ()
*)

let state_to_HS (s:state) : GTot ME.state =
  {
  ME.state = {
    BS.ok = s.ok;
    BS.regs = (fun r -> s.regs r);
    BS.xmms = (fun x -> s.xmms x);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  };
  ME.mem = s.mem;
  }

let lemma_to_eval_operand s o = equiv_eval_operand o (state_to_HS s)

let lemma_to_eval_xmm s x = ()

let lemma_to_valid_operand s o = match o with
  | OConst _ | OReg _ -> ()
  | OMem m -> let addr = eval_maddr m s in
    let aux () : Lemma
    (requires valid_operand o s)
    (ensures BS.valid_operand o (state_to_S s).TS.state) =
    ME.bytes_valid addr (state_to_HS s) in
    Classical.move_requires aux ()

let lemma_to_valid_taint s o t = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S s (state_to_S s)));
  ()

let lemma_to_of_eval_code c s0 =
  let s0' = state_to_S s0 in
  let Ins ins = c in
  let Some sM = TS.taint_eval_code c 0 s0' in
  same_domain_eval_ins c 0 s0' s0;
  let s' = state_of_S s0 sM in
  let s'' = state_to_S s' in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = heap} = sM.TS.state in
  let { BS.ok = ok''; BS.regs = regs''; BS.xmms = xmms''; BS.flags = flags''; BS.mem = heap''} = s''.TS.state in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  X64.Bytes_Semantics.eval_ins_same_unspecified ins s0';
  X64.Bytes_Semantics.eval_ins_domains ins s0';
  ME.get_heap_hs heap s0.mem;
  ()

val lemma_valid_taint64: (b:X64.Memory.buffer64) ->
                         (memTaint:X64.Memory.memtaint) ->
                         (mem:X64.Memory.mem) ->
                         (i:nat{i < X64.Memory.buffer_length b}) ->
                         (t:taint) -> Lemma
  (requires X64.Memory.valid_taint_buf64 b mem memTaint t /\ X64.Memory.buffer_readable mem b)
  (ensures memTaint.[X64.Memory.buffer_addr b mem + 8 `op_Multiply` i] == t)

val lemma_valid_taint128: (b:X64.Memory.buffer128) ->
                         (memTaint:X64.Memory.memtaint) ->
                         (mem:X64.Memory.mem) ->
                         (i:nat{i < X64.Memory.buffer_length b}) ->
                         (t:taint) -> Lemma
  (requires X64.Memory.valid_taint_buf128 b mem memTaint t /\ X64.Memory.buffer_readable mem b)
  (ensures memTaint.[X64.Memory.buffer_addr b mem + 16 `op_Multiply` i] == t /\
           memTaint.[X64.Memory.buffer_addr b mem + 16 `op_Multiply` i + 8] == t)


val same_memTaint64: (b:X64.Memory.buffer64) ->
                   (mem0:X64.Memory.mem) ->
                   (mem1:X64.Memory.mem) ->
                   (memtaint0:X64.Memory.memtaint) ->
                   (memtaint1:X64.Memory.memtaint) -> Lemma
  (requires (X64.Memory.modifies (X64.Memory.loc_buffer b) mem0 mem1 /\
    (forall p. Map.sel memtaint0 p == Map.sel memtaint1 p)))
  (ensures memtaint0 == memtaint1)

val same_memTaint128: (b:X64.Memory.buffer128) ->
                   (mem0:X64.Memory.mem) ->
                   (mem1:X64.Memory.mem) ->
                   (memtaint0:X64.Memory.memtaint) ->
                   (memtaint1:X64.Memory.memtaint) -> Lemma
  (requires (X64.Memory.modifies (X64.Memory.loc_buffer b) mem0 mem1 /\
    (forall p. Map.sel memtaint0 p == Map.sel memtaint1 p)))
  (ensures memtaint0 == memtaint1)

let lemma_valid_taint64 = ME.lemma_valid_taint64
let lemma_valid_taint128  = ME.lemma_valid_taint128

let same_memTaint64 = ME.same_memTaint64
let same_memTaint128 = ME.same_memTaint128
