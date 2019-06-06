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

val same_domain: sv:vale_state -> s:BS.machine_state -> prop0

val same_domain_eval_ins (c:BS.code{Ins? c}) (f:nat) (s0:BS.machine_state) (sv:vale_state) : Lemma
  (requires same_domain sv s0)
  (ensures (let s1 = BS.machine_eval_code c f s0 in
     same_domain sv (Some?.v s1))
  )

val state_to_S : s:vale_state -> GTot (s':BS.machine_state{same_domain s s'})
val state_of_S : sv:vale_state -> (s:BS.machine_state{same_domain sv s}) -> GTot vale_state

val lemma_to_ok : s:vale_state -> Lemma
  (ensures s.vs_ok == ok' (state_to_S s))
  [SMTPat s.vs_ok]

val lemma_to_flags : s:vale_state -> f:flag -> Lemma
  (ensures Flags.sel f s.vs_flags == flags' (state_to_S s) f)
  [SMTPat (Flags.sel f s.vs_flags)]

val lemma_to_reg : s:vale_state -> r:reg -> Lemma
  (ensures Regs.sel r s.vs_regs == regs' (state_to_S s) r)
  [SMTPat (Regs.sel r s.vs_regs)]

val lemma_to_xmm : s:vale_state -> x:xmm -> Lemma
  (ensures Xmms.sel x s.vs_xmms == xmms' (state_to_S s) x)
  [SMTPat (Xmms.sel x s.vs_xmms)]

val lemma_to_mem : s:vale_state -> Lemma
  (ensures MS.get_heap s.vs_mem == mem' (state_to_S s))

val lemma_to_stack : s:vale_state -> Lemma
  (ensures VSS.stack_to_s s.vs_stack == stack' (state_to_S s))

val lemma_to_trace : s:vale_state -> Lemma
  (ensures [] == trace' (state_to_S s))
  [SMTPat (state_to_S s)]

val lemma_to_memTaint : s:vale_state -> Lemma
  (ensures s.vs_memTaint === memTaint' (state_to_S s))
  [SMTPat s.vs_memTaint]

val lemma_to_stackTaint : s:vale_state -> Lemma
  (ensures s.vs_stackTaint === stackTaint' (state_to_S s))
  [SMTPat s.vs_stackTaint]

val lemma_to_eval_operand : s:vale_state -> o:operand64 -> Lemma
  (requires valid_src_operand o s)
  (ensures eval_operand o s == BS.eval_operand o (state_to_S s))
  [SMTPat (eval_operand o s)]

val lemma_to_eval_xmm : s:vale_state -> x:xmm -> Lemma
  (ensures eval_xmm x s == BS.eval_xmm x (state_to_S s))
  [SMTPat (eval_xmm x s)]

val lemma_to_eval_operand128 : s:vale_state -> o:operand128 -> Lemma
  (requires valid_src_operand128 o s)
  (ensures eval_operand128 o s == BS.eval_mov128_op o (state_to_S s))
  [SMTPat (eval_operand128 o s)]

val lemma_to_valid_operand : s:vale_state -> o:operand64 -> Lemma
  (ensures valid_src_operand o s ==> BS.valid_src_operand o (state_to_S s))
  [SMTPat (valid_src_operand o s)]

val lemma_of_to : s:vale_state -> Lemma
  (ensures s == state_of_S s (state_to_S s))
  [SMTPat (state_of_S s (state_to_S s))]

val lemma_to_of_eval_ins: (c:BS.code) -> (s0:vale_state) -> Lemma
  (requires Ins? c)
  (ensures (
    let Some sM = BS.machine_eval_code c 0 (state_to_S s0) in
    same_domain_eval_ins c 0 (state_to_S s0) s0;
    (state_to_S (state_of_S s0 sM) == {sM with BS.ms_trace = []})
  ))

unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
