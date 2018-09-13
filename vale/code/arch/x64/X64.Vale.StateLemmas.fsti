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

val eq_modulo_heap: h1:BS.heap -> h2:BS.heap -> prop0

val eq_modulo_heap_idem: h:BS.heap -> 
  Lemma (eq_modulo_heap h h)
  [SMTPat (eq_modulo_heap h h)]

val eq_modulo_heap_sym: h1:BS.heap -> h2:BS.heap -> Lemma
  (eq_modulo_heap h1 h2 <==> eq_modulo_heap h2 h1)
  [SMTPat (eq_modulo_heap h1 h2)]

val eq_modulo_heap_trans: h1:BS.heap -> h2:BS.heap -> h3:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2 /\ eq_modulo_heap h2 h3)
  (ensures eq_modulo_heap h1 h3)
  [SMTPat (eq_modulo_heap h1 h2); SMTPat (eq_modulo_heap h2 h3)]

val eq_modulo_heap_valid: ptr:int -> h1:BS.heap -> h2:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2)
  (ensures BS.valid_addr64 ptr h1 <==> BS.valid_addr64 ptr h2)
  [SMTPat (BS.valid_addr64 ptr h1); SMTPat (eq_modulo_heap h1 h2)]

val eq_modulo_heap_load: ptr:int -> h1:BS.heap -> h2:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2 /\ BS.valid_addr64 ptr h1)
  (ensures BS.get_heap_val64 ptr h1 == BS.get_heap_val64 ptr h2)
  [SMTPat (BS.get_heap_val64 ptr h1); SMTPat (eq_modulo_heap h1 h2)]

val eq_modulo_heap_store: ptr:int -> v:nat64 -> h1:BS.heap -> h2:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2 /\ BS.valid_addr64 ptr h1)
  (ensures eq_modulo_heap (BS.update_heap64 ptr v h1) (BS.update_heap64 ptr v h2))
  [SMTPat (BS.update_heap64 ptr v h1); SMTPat (eq_modulo_heap h1 h2)]

val eq_modulo_heap_valid128: ptr:int -> h1:BS.heap -> h2:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2)
  (ensures BS.valid_addr128 ptr h1 <==> BS.valid_addr128 ptr h2)
  [SMTPat (BS.valid_addr128 ptr h1); SMTPat (eq_modulo_heap h1 h2)]

val eq_modulo_heap_load128: ptr:int -> h1:BS.heap -> h2:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2 /\ BS.valid_addr128 ptr h1)
  (ensures BS.get_heap_val128 ptr h1 == BS.get_heap_val128 ptr h2)
  [SMTPat (BS.get_heap_val128 ptr h1); SMTPat (eq_modulo_heap h1 h2)]

val eq_modulo_heap_store128: ptr:int -> v:quad32 -> h1:BS.heap -> h2:BS.heap -> Lemma
  (requires eq_modulo_heap h1 h2 /\ BS.valid_addr128 ptr h1)
  (ensures eq_modulo_heap (BS.update_heap128 ptr v h1) (BS.update_heap128 ptr v h2))
  [SMTPat (BS.update_heap128 ptr v h1); SMTPat (eq_modulo_heap h1 h2)]

let state_eq_BS (s1 s2:BS.state) =
  s1.BS.ok == s2.BS.ok /\
  s1.BS.flags == s2.BS.flags /\
  s1.BS.regs == s2.BS.regs /\
  s1.BS.xmms == s2.BS.xmms /\
  eq_modulo_heap s1.BS.mem s2.BS.mem

let state_eq_S (s1 s2:TS.traceState) =
  s1.TS.memTaint == s2.TS.memTaint /\
  state_eq_BS s1.TS.state s2.TS.state

val state_to_S : s:state -> GTot (s':TS.traceState{same_domain s s'})
val state_of_S : sv:state -> (s:TS.traceState{same_domain sv s}) -> GTot state

val lemma_to_ok : s:state -> Lemma
  (ensures s.ok == ok' (state_to_S s).TS.state)
  [SMTPat s.ok]

val lemma_to_flags : s:state -> Lemma
  (ensures s.flags == flags' (state_to_S s).TS.state)
  [SMTPat s.flags]

(*
val lemma_to_mem : s:state -> Lemma
  (ensures s.mem === mem' (state_to_S s).TS.state)
  [SMTPat s.mem]
*)

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

(*
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
*)

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

val lemma_to_of : sv:state -> (s:TS.traceState{same_domain sv s}) -> Lemma
  (ensures state_eq_S (state_to_S (state_of_S sv s)) s)
  [SMTPat (state_to_S (state_of_S sv s))]

unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
