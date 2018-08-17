module X64.Vale.StateLemmas
open X64.Machine_s
open X64.Vale.State
module S = X64.Semantics_s
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_s
module TS = X64.Taint_Semantics_s

friend X64.Memory

#reset-options "--initial_fuel 2 --max_fuel 2"

let state_to_S (s:state) : GTot TS.traceState =
  {
  TS.state = (let s' = {
    BS.ok = s.ok;
    BS.regs = (fun r -> s.regs r);
    BS.xmms = (fun x -> s.xmms x);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  } in
  { ME.state = s'; ME.mem = s.mem});
  TS.trace = [];
  TS.memTaint = s.memTaint;
  }

let state_of_S (s:TS.traceState) : GTot state =
  let { ME.state = st; ME.mem = mem } = s.TS.state in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = _} = st in
  {
    ok = ok;
    regs = (fun r -> regs r);
    xmms = (fun x -> xmms x);
    flags = flags;
    mem = mem;
    memTaint = s.TS.memTaint;
  }

let lemma_to_ok s = ()
let lemma_to_flags s = ()
let lemma_to_mem s = ()

let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()
let lemma_of_ok s = ()
let lemma_of_flags s = ()
let lemma_of_mem s = ()
let lemma_of_regs s = assert (feq (regs' s.TS.state) (state_of_S s).regs)
let lemma_of_xmms s = assert (feq (xmms' s.TS.state) (state_of_S s).xmms)
let lemma_of_memTaint s = ()
let lemma_to_eval_operand s o = ()
let lemma_to_eval_xmm s x = ()
let lemma_to_valid_operand s o = ()
let lemma_to_valid_taint s o t = ()

let lemma_of_to s =
  assert (state_eq s (state_of_S (state_to_S s)));
  ()

let lemma_to_of s =
  let s' = state_of_S s in
  let s'' = state_to_S s' in
  let { ME.state = st; ME.mem = mem } = s.TS.state in
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = heap} = st in
  let { ME.state = st''; ME.mem = mem'' } = s''.TS.state in
  let { BS.ok = ok''; BS.regs = regs''; BS.xmms = xmms''; BS.flags = flags''; BS.mem = heap''} = st'' in
  assert (feq regs regs'');
  assert (feq xmms xmms'');
  ME.same_heap s.TS.state s''.TS.state;
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
