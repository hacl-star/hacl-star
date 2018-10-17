module X64.Vale.StateLemmas
open X64.Machine_s
open X64.Vale.State
open FStar.FunctionalExtensionality
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_s
module TS = X64.Taint_Semantics_s
open Prop_s

unfold let ok' s = s.BS.ok
unfold let regs' s = s.BS.regs
unfold let xmms' s = s.BS.xmms
unfold let flags' s = s.BS.flags
unfold let mem' s = s.BS.mem
unfold let trace' = TS.MktraceState?.trace
unfold let memTaint' = TS.MktraceState?.memTaint

val same_domain: sv:state -> s:TS.traceState -> prop0

val same_domain_eval_ins (c:TS.tainted_code{Ins? c}) (f:nat) (s0:TS.traceState) (sv:state) : Lemma
  (requires same_domain sv s0)
  (ensures (let s1 = TS.taint_eval_code c f s0 in
     same_domain sv (Some?.v s1))
  )

val state_to_S : s:state -> GTot (s':TS.traceState{same_domain s s'})
val state_of_S : sv:state -> (s:TS.traceState{same_domain sv s}) -> GTot state

val lemma_to_ok : s:state -> Lemma
  (ensures s.ok == ok' (state_to_S s).TS.state)
  [SMTPat s.ok]

val lemma_to_flags : s:state -> Lemma
  (ensures s.flags == flags' (state_to_S s).TS.state)
  [SMTPat s.flags]

val lemma_to_reg : s:state -> r:reg -> Lemma
  (ensures Regs.sel r s.regs == regs' (state_to_S s).TS.state r)
  [SMTPat (Regs.sel r s.regs)]

val lemma_to_xmm : s:state -> x:xmm -> Lemma
  (ensures Xmms.sel x s.xmms == xmms' (state_to_S s).TS.state x)
  [SMTPat (Xmms.sel x s.xmms)]

val lemma_to_trace : s:state -> Lemma
  (ensures [] == trace' (state_to_S s))
  [SMTPat (state_to_S s)]

val lemma_to_memTaint : s:state -> Lemma
  (ensures s.memTaint === memTaint' (state_to_S s))
  [SMTPat s.memTaint]

val lemma_to_eval_operand : s:state -> o:operand -> Lemma
  (requires valid_operand o s)
  (ensures eval_operand o s == BS.eval_operand o (state_to_S s).TS.state)
  [SMTPat (eval_operand o s)]

val lemma_to_eval_xmm : s:state -> x:xmm -> Lemma
  (ensures eval_xmm x s == BS.eval_xmm x (state_to_S s).TS.state)
  [SMTPat (eval_xmm x s)]

val lemma_to_valid_operand : s:state -> o:operand -> Lemma
  (ensures valid_operand o s ==> BS.valid_operand o (state_to_S s).TS.state)
  [SMTPat (valid_operand o s)]

val lemma_of_to : s:state -> Lemma
  (ensures s == state_of_S s (state_to_S s))
  [SMTPat (state_of_S s (state_to_S s))]

val lemma_to_of_eval_code: (c:TS.tainted_code) -> (s0:state) -> Lemma
  (requires Ins? c)
  (ensures (
    let Some sM = TS.taint_eval_code c 0 (state_to_S s0) in
    same_domain_eval_ins c 0 (state_to_S s0) s0;
    (state_to_S (state_of_S s0 sM) == {sM with TS.trace = []})
  ))
    
unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
