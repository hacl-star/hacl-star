module ModularInterop

friend X64.Memory

open X64.Machine_s

let make_h_equals_refine (a:Type) (x:a) (p:a -> Type0) (q:squash (p x)) : h_equals_refine a x (y:a{p y}) x =
  HReflRefine p q

let prove_squash (a:Type) (x:a) : Lemma (squash a) = ()

let to_b8 m =
  let p (b:b8) : Type0 = LB.length b % M.view_n (M.TBase M.TUInt64) == 0 in
  let h : h_equals_refine b8 m (y:b8{p y}) m = make_h_equals_refine b8 m p () in //HReflRefine p () in
  prove_squash (h_equals_refine b8 m (M.buffer (M.TBase M.TUInt64)) m) h;
  m

let regs_with_stack (regs:registers) (stack_b:b8) (rsp:nat64) : registers =
  fun r -> if r = Rsp then rsp else regs r

let create_memory (acc:list b8) (h0:HS.mem{mem_roots_p h0 acc}) : M.mem =
  { M.addrs = IA.addrs;
    M.ptrs = acc;
    M.hs = h0; }

let create_initial_trusted_state_core
       (acc:list b8)
       (rsp:nat64)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : GTot (TS.traceState & M.mem)
  = let acc = stack::acc in
    let (mem:M.mem) = create_memory acc h0 in
    let regs = FunctionalExtensionality.on reg (regs_with_stack regs stack rsp) in
    let xmms = FunctionalExtensionality.on xmm xmms in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = 0;
      BS.mem = I.down_mem h0 IA.addrs acc
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = M.create_valid_memtaint mem acc taint
    },
    mem

let create_initial_vale_state_core
       (acc:list b8)
       (rsp:nat64)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : GTot V.va_state
  = let t_state, mem = create_initial_trusted_state_core acc rsp regs xmms taint h0 stack in
    { VS.ok = TS.(BS.(t_state.state.ok));
      VS.regs = X64.Vale.Regs.of_fun TS.(BS.(t_state.state.regs));
      VS.xmms =  X64.Vale.Xmms.of_fun TS.(BS.(t_state.state.xmms));
      VS.flags = TS.(BS.(t_state.state.flags));
      VS.mem = mem;
      VS.memTaint = TS.(t_state.memTaint) }

let arg_of_register (is_win:bool) (r:reg)
  : option (i:nat{i < max_arity is_win /\ register_of_arg_i is_win i = r})
  = if is_win then
       match r with
       | Rcx -> Some 0
       | Rdx -> Some 1
       | R8 -> Some 2
       | R9 -> Some 3
       | _ -> None
    else
       match r with
       | Rdi -> Some 0
       | Rsi -> Some 1
       | Rdx -> Some 2
       | Rcx -> Some 3
       | R8 -> Some 4
       | R9 -> Some 5
       | _ -> None

let upd_reg (is_win:bool) (regs:registers) (i:nat) (v:_) : registers =
    fun (r:reg) ->
      match arg_of_register is_win r with
      | Some j ->
        if i = j then v
        else regs r
      | _ -> regs r

let lemma_low_assumptions_length (b:M.buffer64) :
  Lemma
    (requires True)
    (ensures LB.length (to_b8 b) == 8 * M.buffer_length b)
    [SMTPat (LB.length (to_b8 b))]
  =
  let vb = LBV.mk_buffer_view b Views.view64 in
  LBV.length_eq vb;
  LBV.as_buffer_mk_buffer_view b Views.view64;
  assert (LBV.get_view vb == Views.view64);
  assert (LBV.View?.n (LBV.get_view vb) == 8);
  assert (LB.length (to_b8 b) == 8 * M.buffer_length b)

let lemma_low_assumptions_seq (acc:list b8) (hs_mem:HS.mem) (b:M.buffer64) :
  Lemma
    (requires mem_roots_p hs_mem acc)
    (ensures (
      let va_mem = create_memory acc hs_mem in
      seq_nat64_to_seq_U64 (M.buffer_as_seq va_mem b) ==
      LBV.as_seq hs_mem (LBV.mk_buffer_view (to_b8 b) Views.view64)))
    [SMTPat (LBV.mk_buffer_view (to_b8 b) Views.view64); SMTPat (create_memory acc hs_mem)]
  =
  let va_mem = create_memory acc hs_mem in
//  let s = LBV.as_seq hs_mem (LBV.mk_buffer_view b Views.view64) in
//  let len = Seq.length s in
//  let contents (i:nat{i < len}) : nat64 = UInt64.v (Seq.index s i) in
//  let s' = Seq.init len contents in
//
//  assert (M.buffer_as_seq va_mem b == M.buffer_as_seq #(M.TBase M.TUInt64) va_mem b);
//  assert (Seq.equal (M.buffer_as_seq #(M.TBase M.TUInt64) va_mem b) s');
//
//  assert (Seq.equal
//    (seq_nat64_to_seq_U64 s')
//    (LBV.as_seq hs_mem (LBV.mk_buffer_view (to_b8 b) Views.view64)));

  assert (Seq.equal
    (seq_nat64_to_seq_U64 (M.buffer_as_seq va_mem b))
    (LBV.as_seq hs_mem (LBV.mk_buffer_view (to_b8 b) Views.view64)));

  ()

#reset-options "--z3rlimit 40"

let wrap code pre post v = fun (x0:M.buffer64) (x1:M.buffer64) ->
  let acc = [x0; x1] in
  let h0 = HST.get () in
  HST.push_frame();
  let h1 = HST.get () in
  let (stack_b:b8) = LB.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
  lemma_low_assumptions_length stack_b;
  let h2 = HST.get () in

assume (
  (Seq.equal
    (LBV.as_seq h0 (LBV.mk_buffer_view (to_b8 x0) Views.view64))
    (LBV.as_seq h1 (LBV.mk_buffer_view (to_b8 x0) Views.view64))
  )
);
assume (
  (Seq.equal
    (LBV.as_seq h1 (LBV.mk_buffer_view (to_b8 x0) Views.view64))
    (LBV.as_seq h2 (LBV.mk_buffer_view (to_b8 x0) Views.view64))
  )
);
assume (
  (Seq.equal
    (LBV.as_seq h0 (LBV.mk_buffer_view (to_b8 x1) Views.view64))
    (LBV.as_seq h1 (LBV.mk_buffer_view (to_b8 x1) Views.view64))
  )
);
assume (
  (Seq.equal
    (LBV.as_seq h1 (LBV.mk_buffer_view (to_b8 x1) Views.view64))
    (LBV.as_seq h2 (LBV.mk_buffer_view (to_b8 x1) Views.view64))
  )
);

  assert (HS.fresh_frame h0 h1);
  assert (disjoint_or_eq_l_aux x0 []);
  assert (disjoint_or_eq_l_aux x0 [x1]);
  assert (disjoint_or_eq_l_aux stack_b []);
  assert (disjoint_or_eq_l_aux stack_b [x1]);
  assert (disjoint_or_eq_l_aux stack_b [x0; x1]);
  assert (mem_roots_p h2 []);
  assert (mem_roots_p h2 [x1]);
  assert (mem_roots_p h2 [x0; x1]);
  assert (mem_roots_p h2 [stack_b; x0; x1]);
  let (va_s0, va_s1, fuel) = IA.st_put
    #(x:(V.va_state & V.va_state & V.va_fuel){
      let (va_s0, va_s1, fuel) = x in
      low_assumptions h0 va_s0.VS.mem x0 x1 /\
      LB.modifies (LB.loc_union (LB.loc_buffer (to_b8 stack_b)) (LB.loc_union (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1)))) h2 va_s1.VS.mem.M.hs /\
      post IA.win x0 x1 va_s0 stack_b va_s1 fuel
    })
    (fun h0' -> h0' == h2) (fun h0' ->
    let regs = IA.init_regs in
    let xmms = IA.init_xmms in
    let taints (b:b8) : GTot taint =
      if StrongExcludedMiddle.strong_excluded_middle (b == x0) then Secret else
      if StrongExcludedMiddle.strong_excluded_middle (b == x1) then Secret else
      Public
      in
    let regs = upd_reg IA.win regs 0 (IA.addrs x0) in
    let regs = upd_reg IA.win regs 1 (IA.addrs x1) in
    let rsp = IA.addrs stack_b + 24 in
    let va_s0 = create_initial_vale_state_core acc rsp regs xmms taints h0' stack_b in
    assert (LB.frameOf stack_b = HS.get_tip h0');
    assert (LB.live h0' stack_b);
    let va_mem = va_s0.VS.mem in
    let num_stack_slots = 3 in
    assert (low_assumptions h0 va_mem x0 x1);
    assert_norm (List.memP x0 [stack_b; x0; x1]);
    assert_norm (List.memP x1 [stack_b; x0; x1]);
    assert (M.buffer_readable va_mem x0);
    assert (M.buffer_readable va_mem x1);
    assert (V.valid_stack_slots va_mem (VS.eval_reg Rsp va_s0) stack_b num_stack_slots va_s0.VS.memTaint);
    assert (M.buffer_length #(M.TBase M.TUInt64) stack_b >= num_stack_slots);
    assert (M.locs_disjoint ([M.loc_buffer #(M.TBase M.TUInt64) stack_b; M.loc_buffer #(M.TBase M.TUInt64) x0; M.loc_buffer #(M.TBase M.TUInt64) x1]));
    assert (M.valid_taint_buf64 x0 va_s0.VS.mem va_s0.VS.memTaint Secret);
    assert (M.valid_taint_buf64 x1 va_s0.VS.mem va_s0.VS.memTaint Secret);
    assert (pre IA.win x0 x1 va_s0 stack_b);
    let va_s1, fuel = v IA.win x0 x1 va_s0 stack_b in
    assert (post IA.win x0 x1 va_s0 stack_b va_s1 fuel);
    assert (V.modifies_mem (M.loc_union (M.loc_buffer x0) (M.loc_buffer x1)) va_s0.VS.mem va_s1.VS.mem);
    assert (LB.modifies (LB.loc_union (LB.loc_buffer (to_b8 stack_b)) (LB.loc_union (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1)))) h2 va_s1.VS.mem.M.hs);
    ((va_s0, va_s1, fuel), va_s1.VS.mem.M.hs)
  ) in //conveniently, st_put assumes that the shape of the stack did not change
  let h3 = HST.get () in
  assert (LB.modifies (LB.loc_union (LB.loc_buffer (to_b8 stack_b)) (LB.loc_union (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1)))) h2 h3);
  HST.pop_frame ();
  let h4 = HST.get () in
assume (
  (Seq.equal
    (LBV.as_seq h3 (LBV.mk_buffer_view (to_b8 x0) Views.view64))
    (LBV.as_seq h4 (LBV.mk_buffer_view (to_b8 x0) Views.view64))
  )
);
assume (
  (Seq.equal
    (LBV.as_seq h3 (LBV.mk_buffer_view (to_b8 x1) Views.view64))
    (LBV.as_seq h4 (LBV.mk_buffer_view (to_b8 x1) Views.view64))
  )
);
  assert (LB.modifies (LB.loc_union (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1))) h0 h4);
  assert (low_assumptions h0 va_s0.VS.mem x0 x1);
  assert (low_assumptions h4 va_s1.VS.mem x0 x1);
  assert (post IA.win x0 x1 va_s0 stack_b va_s1 fuel);
  assert (to_low_post post x0 x1 h0 () h4);
  ()

