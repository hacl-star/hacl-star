module X64.Vale.StateLemmas
open X64.Machine_s
open X64.Vale.State
open FStar.FunctionalExtensionality
module S = X64.Semantics_s
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_s
module TS = X64.Taint_Semantics_s

unfold let ok' s = s.ME.state.BS.ok
unfold let regs' s = s.ME.state.BS.regs
unfold let xmms' s = s.ME.state.BS.xmms
unfold let flags' s = s.ME.state.BS.flags
unfold let mem' = ME.Mkstate'?.mem
unfold let trace' = TS.MktraceState?.trace
unfold let memTaint' = TS.MktraceState?.memTaint

val state_to_S : s:state -> GTot TS.traceState
val state_of_S : s:TS.traceState -> GTot state

val lemma_to_ok : s:state -> Lemma
  (ensures s.ok == ok' (state_to_S s).TS.state)
  [SMTPat s.ok]

val lemma_to_flags : s:state -> Lemma
  (ensures s.flags == flags' (state_to_S s).TS.state)
  [SMTPat s.flags]

val lemma_to_mem : s:state -> Lemma
  (ensures s.mem === mem' (state_to_S s).TS.state)
  [SMTPat s.mem]

val lemma_to_reg : s:state -> r:reg -> Lemma
  (ensures s.regs r == regs' (state_to_S s).TS.state r)
  [SMTPat (s.regs r)]

val lemma_to_xmm : s:state -> x:xmm -> Lemma
  (ensures s.xmms x == xmms' (state_to_S s).TS.state x)
  [SMTPat (s.xmms x)]

val lemma_to_trace : s:state -> Lemma
  (ensures [] == trace' (state_to_S s))
  [SMTPat (state_to_S s)]

val lemma_to_memTaint : s:state -> Lemma
  (ensures s.memTaint === memTaint' (state_to_S s))
  [SMTPat s.memTaint]

// No SMTPats for lemmas_of to avoid pattern loops
val lemma_of_ok : s:TS.traceState -> Lemma
  (ensures (state_of_S s).ok == ok' s.TS.state)

val lemma_of_flags : s:TS.traceState -> Lemma
  (ensures (state_of_S s).flags == flags' s.TS.state)

val lemma_of_mem : s:TS.traceState -> Lemma
  (ensures (state_of_S s).mem === mem' s.TS.state)
  
val lemma_of_regs : s:TS.traceState -> Lemma
  (ensures (state_of_S s).regs == regs' s.TS.state)

val lemma_of_xmms : s:TS.traceState -> Lemma
  (ensures (state_of_S s).xmms == xmms' s.TS.state)

val lemma_of_memTaint : s:TS.traceState -> Lemma
  (ensures (state_of_S s).memTaint === memTaint' s)

val lemma_to_eval_operand : s:state -> o:operand -> Lemma
  (ensures eval_operand o s == S.eval_operand o (state_to_S s).TS.state)
  [SMTPat (eval_operand o s)]

val lemma_to_eval_xmm : s:state -> x:xmm -> Lemma
  (ensures eval_xmm x s == S.eval_xmm x (state_to_S s).TS.state)
  [SMTPat (eval_xmm x s)]

val lemma_to_valid_operand : s:state -> o:operand -> Lemma
  (ensures valid_operand o s ==> S.valid_operand o (state_to_S s).TS.state)
  [SMTPat (valid_operand o s)]

val lemma_of_to : s:state -> Lemma
  (ensures s == state_of_S (state_to_S s))
  [SMTPat (state_of_S (state_to_S s))]

val lemma_to_of : s:TS.traceState -> Lemma
  (ensures state_to_S (state_of_S s) == {s with TS.trace = []})
  [SMTPat (state_to_S (state_of_S s))]

unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
