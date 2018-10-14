module X64.Vale.StateLemmas
open X64.Machine_s
open X64.Vale.State
module BS = X64.Bytes_Semantics_s
module ME = X64.Memory_s
module TS = X64.Taint_Semantics_s
open X64.Semantics_Equiv

friend X64.Memory
module F = FStar.FunctionalExtensionality

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
    BS.regs = F.on_dom reg (fun r -> Regs.sel r s.regs);
    BS.xmms = F.on_dom xmm (fun x -> Xmms.sel x s.xmms);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  };
  TS.trace = [];
  TS.memTaint = s.memTaint;
  }

[@"opaque_to_smt"]
let regs_of_fun (m:reg -> nat64) : Pure Regs.t
  (requires True)
  (ensures fun m' ->
    (forall (r:reg).{:pattern (m r) \/ (Regs.sel r m')} m r == Regs.sel r m')
  )
  =
  let m0_3 = ((m Rax, m Rbx), (m Rcx, m Rdx)) in
  let m4_7 = ((m Rsi, m Rdi), (m Rbp, m Rsp)) in
  let m8_11 = ((m R8, m R9), (m R10, m R11)) in
  let m12_15 = ((m R12, m R13), (m R14, m R15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m Rax == Regs.sel Rax m');
  assert_norm (m Rbx == Regs.sel Rbx m');
  assert_norm (m Rcx == Regs.sel Rcx m');
  assert_norm (m Rdx == Regs.sel Rdx m');
  assert_norm (m Rsi == Regs.sel Rsi m');
  assert_norm (m Rdi == Regs.sel Rdi m');
  assert_norm (m Rbp == Regs.sel Rbp m');
  assert_norm (m Rsp == Regs.sel Rsp m');
  assert_norm (m R8  == Regs.sel R8  m');
  assert_norm (m R9  == Regs.sel R9  m');
  assert_norm (m R10 == Regs.sel R10 m');
  assert_norm (m R11 == Regs.sel R11 m');
  assert_norm (m R12 == Regs.sel R12 m');
  assert_norm (m R13 == Regs.sel R13 m');
  assert_norm (m R14 == Regs.sel R14 m');
  assert_norm (m R15 == Regs.sel R15 m');
  m'

[@"opaque_to_smt"]
let xmms_of_fun (m:xmm -> quad32) : Pure Xmms.t
  (requires True)
  (ensures fun m' ->
    (forall (r:xmm).{:pattern (m r) \/ (Xmms.sel r m')} m r == Xmms.sel r m')
  )
  =
  let m0_3 = ((m 0, m 1), (m 2, m 3)) in
  let m4_7 = ((m 4, m 5), (m 6, m 7)) in
  let m8_11 = ((m 8, m 9), (m 10, m 11)) in
  let m12_15 = ((m 12, m 13), (m 14, m 15)) in
  let m' = ((m0_3, m4_7), (m8_11, m12_15)) in
  assert_norm (m  0 == Xmms.sel  0 m');
  assert_norm (m  1 == Xmms.sel  1 m');
  assert_norm (m  2 == Xmms.sel  2 m');
  assert_norm (m  3 == Xmms.sel  3 m');
  assert_norm (m  4 == Xmms.sel  4 m');
  assert_norm (m  5 == Xmms.sel  5 m');
  assert_norm (m  6 == Xmms.sel  6 m');
  assert_norm (m  7 == Xmms.sel  7 m');
  assert_norm (m  8 == Xmms.sel  8 m');
  assert_norm (m  9 == Xmms.sel  9 m');
  assert_norm (m 10 == Xmms.sel 10 m');
  assert_norm (m 11 == Xmms.sel 11 m');
  assert_norm (m 12 == Xmms.sel 12 m');
  assert_norm (m 13 == Xmms.sel 13 m');
  assert_norm (m 14 == Xmms.sel 14 m');
  assert_norm (m 15 == Xmms.sel 15 m');
  m'

let state_of_S (sv:state) (s:TS.traceState{same_domain sv s}) : GTot state =
  let { BS.ok = ok; BS.regs = regs; BS.xmms = xmms; BS.flags = flags; BS.mem = mem} = s.TS.state in
  {
    ok = ok;
    regs = regs_of_fun regs;
    xmms = xmms_of_fun xmms;
    flags = flags;
    mem = ME.get_hs sv.mem mem;
    memTaint = s.TS.memTaint;
  }

let lemma_to_ok s = ()
let lemma_to_flags s = ()

let lemma_to_reg s r = ()
let lemma_to_xmm s x = ()
let lemma_to_trace s = ()
let lemma_to_memTaint s = ()

let state_to_HS (s:state) : GTot ME.state =
  {
  ME.state = {
    BS.ok = s.ok;
    BS.regs = F.on_dom reg (fun r -> Regs.sel r s.regs);
    BS.xmms = F.on_dom xmm (fun x -> Xmms.sel x s.xmms);
    BS.flags = int_to_nat64 s.flags;
    BS.mem = ME.get_heap s.mem
  };
  ME.mem = s.mem;
  }

#set-options "--max_ifuel 2 --initial_ifuel 2"
let lemma_to_eval_operand s o = equiv_eval_operand o (state_to_HS s)
#reset-options "--initial_fuel 2 --max_fuel 2"

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
