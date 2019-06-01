module Vale.X64.StateLemmas
open Vale.X64.Machine_s
open Vale.X64.State
open FStar.FunctionalExtensionality
module BS = Vale.X64.Machine_Semantics_s
module ME = Vale.X64.Memory
module MS = Vale.X64.Memory_Sems
module VSS = Vale.X64.Stack_Sems
open Vale.Def.Prop_s

unfold let ok' s = s.BS.ms_ok
unfold let regs' s = s.BS.ms_regs
unfold let xmms' s = s.BS.ms_xmms
unfold let flags' s = s.BS.ms_flags
unfold let mem' s = s.BS.ms_mem
unfold let memTaint' s = s.BS.ms_memTaint
unfold let stack' s = s.BS.ms_stack
unfold let stackTaint' s = s.BS.ms_stackTaint
unfold let trace' s = s.BS.ms_trace

val same_domain: sv:state -> s:BS.machine_state -> prop0

val same_domain_eval_ins (c:BS.code{Ins? c}) (f:nat) (s0:BS.machine_state) (sv:state) : Lemma
  (requires same_domain sv s0)
  (ensures (let s1 = BS.machine_eval_code c f s0 in
     same_domain sv (Some?.v s1))
  )

val state_to_S : s:state -> GTot (s':BS.machine_state{same_domain s s'})
val state_of_S : sv:state -> (s:BS.machine_state{same_domain sv s}) -> GTot state

val lemma_to_ok : s:state -> Lemma
  (ensures s.ok == ok' (state_to_S s))
  [SMTPat s.ok]

val lemma_to_flags : s:state -> Lemma
  (ensures s.flags == flags' (state_to_S s))
  [SMTPat s.flags]

val lemma_to_reg : s:state -> r:reg -> Lemma
  (ensures Regs.sel r s.regs == regs' (state_to_S s) r)
  [SMTPat (Regs.sel r s.regs)]

val lemma_to_xmm : s:state -> x:xmm -> Lemma
  (ensures Xmms.sel x s.xmms == xmms' (state_to_S s) x)
  [SMTPat (Xmms.sel x s.xmms)]

val lemma_to_mem : s:state -> Lemma
  (ensures MS.get_heap s.mem == mem' (state_to_S s))

val lemma_to_stack : s:state -> Lemma
  (ensures VSS.stack_to_s s.stack == stack' (state_to_S s))

val lemma_to_trace : s:state -> Lemma
  (ensures [] == trace' (state_to_S s))
  [SMTPat (state_to_S s)]

val lemma_to_memTaint : s:state -> Lemma
  (ensures s.memTaint === memTaint' (state_to_S s))
  [SMTPat s.memTaint]

val lemma_to_stackTaint : s:state -> Lemma
  (ensures s.stackTaint === stackTaint' (state_to_S s))
  [SMTPat s.stackTaint]

val lemma_to_eval_operand : s:state -> o:operand64 -> Lemma
  (requires valid_src_operand o s)
  (ensures eval_operand o s == BS.eval_operand o (state_to_S s))
  [SMTPat (eval_operand o s)]

val lemma_to_eval_xmm : s:state -> x:xmm -> Lemma
  (ensures eval_xmm x s == BS.eval_xmm x (state_to_S s))
  [SMTPat (eval_xmm x s)]

val lemma_to_eval_operand128 : s:state -> o:operand128 -> Lemma
  (requires valid_src_operand128 o s)
  (ensures eval_operand128 o s == BS.eval_mov128_op o (state_to_S s))
  [SMTPat (eval_operand128 o s)]

val lemma_to_valid_operand : s:state -> o:operand64 -> Lemma
  (ensures valid_src_operand o s ==> BS.valid_src_operand o (state_to_S s))
  [SMTPat (valid_src_operand o s)]

val lemma_of_to : s:state -> Lemma
  (ensures s == state_of_S s (state_to_S s))
  [SMTPat (state_of_S s (state_to_S s))]

val lemma_to_of_eval_ins: (c:BS.code) -> (s0:state) -> Lemma
  (requires Ins? c)
  (ensures (
    let Some sM = BS.machine_eval_code c 0 (state_to_S s0) in
    same_domain_eval_ins c 0 (state_to_S s0) s0;
    (state_to_S (state_of_S s0 sM) == {sM with BS.ms_trace = []})
  ))

unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
