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

let eq_modulo_heap h1 h2 =
  Set.equal (Map.domain h1) (Map.domain h2) /\
  (forall (x:int). Map.contains h1 x /\ Map.contains h2 x ==> (Map.sel h1 x == Map.sel h2 x) )

let eq_modulo_heap_idem h = ()

let eq_modulo_heap_sym h1 h2 = ()

let eq_modulo_heap_trans h1 h2 h3 = ()

let eq_modulo_heap_valid ptr h1 h2 = ()

let eq_modulo_heap_load ptr h1 h2 = Opaque_s.reveal_opaque BS.get_heap_val64_def
  
let eq_modulo_heap_store ptr v h1 h2 = Opaque_s.reveal_opaque BS.update_heap64_def

let eq_modulo_heap_valid128 ptr h1 h2 = ()

let eq_modulo_heap_load128 ptr h1 h2 =
  Opaque_s.reveal_opaque BS.get_heap_val128_def;
  Opaque_s.reveal_opaque BS.get_heap_val32_def

open Words_s

let eq_modulo_heap_store32 (ptr:int) (v:nat32) (h1 h2:BS.heap) : Lemma
  (requires eq_modulo_heap h1 h2 /\ 
    BS.valid_addr ptr h1 /\ BS.valid_addr (ptr+1) h1 /\ 
    BS.valid_addr (ptr+2) h1 /\ BS.valid_addr (ptr+3) h1)
  (ensures (
    let h1' = BS.update_heap32 ptr v h1 in 
    let h2' = BS.update_heap32 ptr v h2 in
    eq_modulo_heap h1' h2' /\
    Set.equal (Map.domain h1) (Map.domain h1') /\
    Set.equal (Map.domain h2) (Map.domain h2'))) =
  Opaque_s.reveal_opaque BS.update_heap32_def
  
let eq_modulo_heap_store128 ptr v h1 h2 =
  eq_modulo_heap_store32 ptr v.lo0 h1 h2;
  let h1' = BS.update_heap32 ptr v.lo0 h1 in
  let h2' = BS.update_heap32 ptr v.lo0 h2 in
  eq_modulo_heap_store32 (ptr+4) v.lo1 h1' h2';
  let h1' = BS.update_heap32 (ptr+4) v.lo1 h1' in
  let h2' = BS.update_heap32 (ptr+4) v.lo1 h2' in
  eq_modulo_heap_store32 (ptr+8) v.hi2 h1' h2';  
  let h1' = BS.update_heap32 (ptr+8) v.hi2 h1' in
  let h2' = BS.update_heap32 (ptr+8) v.hi2 h2' in
  eq_modulo_heap_store32 (ptr+12) v.hi3 h1' h2'

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

let lemma_to_of sv s =
  let s' = state_of_S sv s in
  let s'' = state_to_S s' in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = heap} = s.TS.state in
  let { BS.ok = ok''; BS.regs = regs''; BS.xmms = xmms''; BS.flags = flags''; BS.mem = heap''} = s''.TS.state in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
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
