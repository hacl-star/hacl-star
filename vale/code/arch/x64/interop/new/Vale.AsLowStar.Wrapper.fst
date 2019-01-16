module Vale.AsLowStar.Wrapper
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module IM = Interop.Mem
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = X64.Vale.StateLemmas
module VL = X64.Vale.Lemmas
module ST = FStar.HyperStack.ST

[@__reduce__]
let create_initial_vale_state
       (#n:IX64.max_slots)
       (args:IX64.arity_ok arg)
  : IX64.state_builder_t n args V.va_state =
  fun h0 stack ->
    let t_state, mem = IX64.create_initial_trusted_state n args h0 stack in
    let open VS in
    { ok = true;
      regs = X64.Vale.Regs.of_fun t_state.TS.state.BS.regs;
      xmms = X64.Vale.Xmms.of_fun t_state.TS.state.BS.xmms;
      flags = 0; // TODO: REVIEW
      mem = mem;
      memTaint = TS.(t_state.memTaint) }

let lemma_create_initial_vale_state_core
    (#n:IX64.max_slots)
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (
        let s = create_initial_vale_state args h0 stack in
        Interop.Adapters.hs_of_mem VS.(s.mem) == h0
      ))
  = Interop.Adapters.mk_mem_injective (arg_of_sb stack::args) h0

let as_vale_buffer_disjoint (#t1 #t2:ME.typ) (x:lowstar_buffer t1) (y:lowstar_buffer t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_buffer x)) (ME.loc_buffer (as_vale_buffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_buffer x)) (ME.loc_buffer (as_vale_buffer y)))]
   = admit()

#reset-options "--initial_ifuel 2 --max_ifuel 2"
let rec core_create_lemma_disjointness
    (args:list arg{disjoint_or_eq args})
  : Lemma
    (ensures vale_disjoint_or_eq args)
  = match args with
    | [] -> ()
    | hd::tl ->
      disjoint_or_eq_cons hd tl;
      BigOps.pairwise_and'_cons vale_disjoint_or_eq_1 hd tl;
      core_create_lemma_disjointness tl;
      assert (vale_disjoint_or_eq tl);
      let rec aux (n:list arg)
        : Lemma (requires (BigOps.big_and' (disjoint_or_eq_1 hd) n))
                (ensures (BigOps.big_and' (vale_disjoint_or_eq_1 hd) n)) =
        match n with
        | [] -> ()
        | n::ns ->
          BigOps.big_and'_cons (disjoint_or_eq_1 hd) n ns;
          BigOps.big_and'_cons (vale_disjoint_or_eq_1 hd) n ns;
          aux ns
      in
      aux tl
#reset-options

let rec args_b8_lemma (args:list arg) (x:arg) 
  : Lemma
      (List.memP x args ==>
        (match x with
         | (| TD_Buffer bt _, x |) -> List.memP x (Interop.Adapters.args_b8 args)
         | _ -> True))
  = match args with
    | [] -> ()
    | a::q -> 
      args_b8_lemma q x

let readable_cons (hd:arg) (tl:list arg) (s:ME.mem)
  : Lemma VSig.(readable (hd::tl) s <==> (readable_one s hd /\ readable tl s))
  = BigOps.big_and'_cons VSig.(readable_one s) hd tl

let arg_is_registered_root (s:ME.mem) (a:arg) =
  match a with
  | (| TD_Buffer bt _, x |) ->
    List.memP x (Interop.Adapters.ptrs_of_mem s)
  | _ -> true

let core_create_lemma_readable
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures 
        (let va_s = create_initial_vale_state args h0 stack in
         VSig.readable (arg_of_sb stack::args) VS.(va_s.mem)))
  = 
    let readable_registered_one (a:arg) (s:ME.mem)
      : Lemma 
          VSig.(arg_is_registered_root s a <==> readable_one s a)
      = match a with
        | (| TD_Buffer bt _, x |) ->
          Vale.AsLowStar.MemoryHelpers.reveal_readable #(ME.TBase bt) x s
        | _ -> ()
    in
    let rec readable_registered_all 
        (args:list arg)
        (s:ME.mem {forall x. List.memP x args ==> arg_is_registered_root s x})
      : Lemma VSig.(readable args s)
      = match args with
        | [] -> ()
        | hd::tl ->
          readable_cons hd tl s;
          readable_registered_one hd s;
          readable_registered_all tl s
     in
     let readable_mk_mem
         (args:list arg)
         (h:mem_roots args)
       : Lemma 
           (let mem = Interop.Adapters.mk_mem args h in
            VSig.readable args mem)
       = let mem = Interop.Adapters.mk_mem args h in
         Interop.Adapters.mk_mem_injective args h;
         FStar.Classical.forall_intro (FStar.Classical.move_requires (args_b8_lemma args));
         readable_registered_all args mem
     in
     readable_mk_mem (arg_of_sb stack::args) h0

let readable_live_one (m:ME.mem) (a:arg)
  : Lemma (VSig.readable_one m a ==>
           live_arg (Interop.Adapters.hs_of_mem m) a)
  = match a with
    | (| TD_Buffer bt _, x |) ->
      Vale.AsLowStar.MemoryHelpers.readable_live #(ME.TBase bt) x m
    | _ -> ()

let rec readable_all_live (m:ME.mem) (args:list arg)
  : Lemma (VSig.readable args m ==>
           all_live (Interop.Adapters.hs_of_mem m) args)
  = match args with
    | [] -> ()
    | hd::tl ->
      readable_cons hd tl m;
      all_live_cons hd tl (Interop.Adapters.hs_of_mem m);
      readable_live_one m hd;
      readable_all_live m tl

let core_create_lemma_readable2
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures 
        (let va_s = create_initial_vale_state args h0 stack in
         ME.buffer_readable VS.(va_s.mem) (as_vale_buffer stack) /\
         VSig.readable args VS.(va_s.mem)))
  = core_create_lemma_readable args h0 stack;
    let va_s = create_initial_vale_state args h0 stack in
    readable_cons (arg_of_sb stack) args VS.(va_s.mem)
    
let core_create_lemma_mem_correspondance
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures
        (let va_s = create_initial_vale_state args h0 stack in
         LSig.mem_correspondence args h0 va_s))
  =
    let va_s = create_initial_vale_state args h0 stack in
    let rec aux (accu:list arg) : Lemma (LSig.mem_correspondence accu h0 va_s) =
    match accu with
    | [] -> ()
    | hd::tl -> aux tl;
      match hd with
      | (| TD_Buffer bt _, x |) -> 
        let open Vale.AsLowStar.MemoryHelpers in
        buffer_as_seq_reveal bt x args h0 stack
      | _ -> ()
    in
    aux args

let rec register_args' 
    (n:nat) 
    (args:IX64.arity_ok arg{List.length args = n}) 
    (regs:IX64.registers) 
  : prop
  = match args with
    | [] -> True
    | hd::tl ->
      register_args' (n - 1) tl regs /\
      regs (IX64.register_of_arg_i (n - 1)) == IX64.arg_as_nat64 hd

let rec lemma_register_args'_aux
    (n:nat)
    (args:IX64.arity_ok arg{List.length args = n})
    (regs1 regs2:IX64.registers) 
  : Lemma
      (requires
        register_args' n args regs1 /\
        (forall r. (forall (i:IX64.reg_nat{i >= n}). r <> (IX64.register_of_arg_i i)) /\
              r <> MS.Rsp ==>
              regs1 r == regs2 r))
      (ensures register_args' n args regs2)
  = match args with
    | [] -> ()
    | hd::tl -> lemma_register_args'_aux (n-1) tl regs1 regs2

let rec lemma_register_args' 
    (args:IX64.arity_ok arg) 
    (regs:IX64.registers) 
  : Lemma 
     (ensures 
       (let final_regs = IX64.register_of_args (List.length args) args regs in
        register_args' (List.length args) args final_regs))
  = let final_regs = IX64.register_of_args (List.length args) args regs in  
    match args with
    | [] -> ()
    | hd::tl ->
      let n = List.length args in
      let regs' = (IX64.register_of_args (n-1) tl regs) in
      lemma_register_args' tl regs;
      lemma_register_args'_aux (n-1) tl regs' final_regs

let core_create_lemma_register_args
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = create_initial_vale_state args h0 stack in
                LSig.register_args (List.length args) args va_s))
  = 
    let va_s = create_initial_vale_state args h0 stack in
    let regs' = IX64.register_of_args (List.Tot.length args) args IA.init_regs in
    lemma_register_args' args IA.init_regs;
    let open MS in
    let regs = FunctionalExtensionality.on reg (IX64.regs_with_stack regs' stack) in
    lemma_register_args'_aux (List.length args) args regs' regs;
    assert (register_args' (List.length args) args regs);
    let rec aux 
        (args:IX64.arity_ok arg) 
        (s:VS.state) 
        (args':list arg) 
        (h0:HS.mem{mem_roots_p h0 args'})
     : Lemma
         (requires 
            (forall r. VS.eval_reg r s == regs r) /\ 
            register_args' (List.length args) args regs /\
            s.VS.mem == Interop.Adapters.mk_mem args' h0)
         (ensures LSig.register_args (List.length args) args s)
    = let n = List.length args in 
      match args with
      | [] -> ()
      | hd::tl -> aux tl s args' h0; 
        let (| tag, x |) = hd in
        match tag with
        | TD_Buffer bt _ -> Vale.AsLowStar.MemoryHelpers.buffer_addr_reveal bt x args' h0
        | _ -> ()
      in
      aux args va_s (arg_of_sb stack::args) h0

let core_create_lemma_taint_hyp
    #n 
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = create_initial_vale_state args h0 stack in
                LSig.taint_hyp args va_s))
    = admit() // TODO: Requires an implementation of Interop.Adapters.create_valid_memtaint

let core_create_lemma_state
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures 
        (let va_s = create_initial_vale_state args h0 stack in
         fst (IX64.create_initial_trusted_state n args h0 stack) == SL.state_to_S va_s))
  = let va_s = create_initial_vale_state args h0 stack in
    let tr_s = fst (IX64.create_initial_trusted_state n args h0 stack) in
    let sl_s = SL.state_to_S va_s in
    assert (tr_s.TS.memTaint == va_s.VS.memTaint);
    SL.lemma_to_ok va_s;
    SL.lemma_to_flags va_s;
    SL.lemma_to_mem va_s;
    let aux_reg (r:MS.reg) : Lemma (tr_s.TS.state.BS.regs r == sl_s.TS.state.BS.regs r)
      = SL.lemma_to_reg va_s r
    in
    let aux_xmm (x:MS.xmm) : Lemma (tr_s.TS.state.BS.xmms x == sl_s.TS.state.BS.xmms x)
      = SL.lemma_to_xmm va_s x
    in
    Classical.forall_intro aux_reg;
    Classical.forall_intro aux_xmm;    
    assert (FunctionalExtensionality.feq tr_s.TS.state.BS.regs sl_s.TS.state.BS.regs);
    assert (FunctionalExtensionality.feq tr_s.TS.state.BS.xmms sl_s.TS.state.BS.xmms);
    Vale.AsLowStar.MemoryHelpers.get_heap_mk_mem_reveal args h0 stack

// unfold
// let valid_stack_slots (m:ME.mem) (rsp:int) (b:ME.buffer64) (num_slots:int) (memTaint:ME.memtaint) =
//     ME.valid_taint_buf64 b m memTaint X64.Machine_s.Public /\
//     ME.buffer_readable m b /\
//     num_slots <= ME.buffer_length b /\
//     (let open FStar.Mul in
//      rsp == ME.buffer_addr b m + 8 * num_slots /\
//      0 <= rsp - 8 * num_slots /\
//      rsp < Words_s.pow2_64)

let core_create_lemma
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures 
        (let va_s = create_initial_vale_state args h0 stack in
         fst (IX64.create_initial_trusted_state n args h0 stack) == SL.state_to_S va_s /\
         LSig.mem_correspondence args h0 va_s /\
         vale_disjoint_or_eq (arg_of_sb stack :: args) /\
         VSig.readable args VS.(va_s.mem) /\
         LSig.vale_pre_hyp stack args va_s /\
         Interop.Adapters.hs_of_mem va_s.VS.mem == h0 /\
         V.valid_stack_slots
                va_s.VS.mem
                (VS.eval_reg MS.Rsp va_s)
                (as_vale_buffer stack)
                (n / 8)
                va_s.VS.memTaint
  ))
  = let va_s = create_initial_vale_state args h0 stack in
    core_create_lemma_mem_correspondance args h0 stack;
    core_create_lemma_disjointness (arg_of_sb stack :: args);
    core_create_lemma_readable args h0 stack;
    core_create_lemma_readable2 args h0 stack;
    core_create_lemma_register_args args h0 stack;
    core_create_lemma_taint_hyp args h0 stack;
    core_create_lemma_state args h0 stack;
    let s_args = arg_of_sb stack :: args in
    Interop.Adapters.mk_mem_injective s_args h0;
    assume (ME.valid_taint_buf64 (as_vale_buffer stack) va_s.VS.mem va_s.VS.memTaint X64.Machine_s.Public);
    assume (ME.buffer_addr (as_vale_buffer stack) va_s.VS.mem == IA.addrs stack)

let rec frame_mem_correspondence_back
       (args:list arg)
       (h0:mem_roots args)
       (h1:mem_roots args)
       (va_s:V.va_state)
       (l:B.loc)
 : Lemma
     (requires
       LSig.mem_correspondence args h1 va_s /\
       B.modifies l h0 h1 /\
       B.loc_disjoint (loc_all_args args) l)
     (ensures
       LSig.mem_correspondence args h0 va_s)
 = match args with
   | [] -> ()
   | hd::tl -> 
     frame_mem_correspondence_back tl h0 h1 va_s l;
     match hd with
     | (| TD_Buffer bt _, x |) -> 
       BufferViewHelpers.lemma_bv_equal (LSig.view_of_base_typ bt) x h0 h1
     | _ -> ()

let rec frame_mem_correspondence
       (args:list arg)
       (h0:mem_roots args)
       (h1:HS.mem)
       (va_s:V.va_state)
       (l:B.loc)
 : Lemma
     (requires
       LSig.mem_correspondence args h0 va_s /\
       B.modifies l h0 h1 /\
       B.loc_disjoint (loc_all_args args) l)
     (ensures
       LSig.mem_correspondence args h1 va_s /\
       mem_roots_p h1 args)
 =  match args with
 | [] -> ()
 | hd::tl ->
   frame_mem_correspondence tl h0 h1 va_s l;
   match hd with
   | (| TD_Buffer bt _, x |) ->
     BufferViewHelpers.lemma_bv_equal (LSig.view_of_base_typ bt) x h0 h1
   | _ -> ()

let rec args_fp (args:list arg)
                (h0:mem_roots args)
                (h1:HS.mem{HS.fresh_frame h0 h1})
  : Lemma 
      (B.loc_disjoint (loc_all_args args) (B.loc_regions false (Set.singleton (HS.get_tip h1))))
  = match args with
    | [] -> ()
    | hd::tl -> args_fp tl h0 h1

let fuel_eq : squash (V.va_fuel == nat) = Vale.AsLowStar.MemoryHelpers.fuel_eq

let eval_code_ts (c:TS.tainted_code)
                 (s0:TS.traceState)
                 (f0:nat)
                 (s1:TS.traceState) : Type0 =
  VL.state_eq_opt (TS.taint_eval_code c f0 s0) (Some s1)

let eval_code_rel (c:TS.tainted_code)
                  (va_s0 va_s1:_) (f:V.va_fuel)
  : Lemma
     (requires (V.eval_code c va_s0 f va_s1))
     (ensures (eval_code_ts c (SL.state_to_S va_s0) (coerce f) (SL.state_to_S va_s1)))
  = Vale.AsLowStar.MemoryHelpers.decls_eval_code_reveal c va_s0 va_s1 f

let rec mem_correspondence_refl (args:list arg)
                                (va_s:V.va_state)
 : Lemma 
     (ensures LSig.mem_correspondence args (Interop.Adapters.hs_of_mem va_s.VS.mem) va_s)
 = 
   let h = Interop.Adapters.hs_of_mem va_s.VS.mem in
   match args with
   | [] -> ()
   | hd::tl ->
     mem_correspondence_refl tl va_s;
     match hd with
     | (| TD_Buffer bt _, x |) ->
       Vale.AsLowStar.MemoryHelpers.buffer_as_seq_reveal2 bt x va_s
     | _ -> ()

////////////////////////////////////////////////////////////////////////////////

[@__reduce__]
let prediction_pre_rel
          (#n:IX64.max_slots)
          (pre:VSig.vale_pre_tl n [])
          (code:V.va_code)
          (args:IX64.arity_ok arg)
   : IX64.prediction_pre_rel_t code args
   = fun (h0:mem_roots args) ->
      LSig.(to_low_pre pre args h0)

[@__reduce__]
let prediction_post_rel
          #n
          (post:VSig.vale_post_tl n [])
          (code:V.va_code)
          (args:IX64.arity_ok arg)
   : IX64.prediction_post_rel_t code n args
   = fun (h0:mem_roots args)
       (_s0:TS.traceState)
       (_push_h0:mem_roots args)
       (_alloc_push_h0:mem_roots args)
       (_sb:IX64.stack_buffer n)
       (fuel_mem:(nat & ME.mem))
       (_s1:TS.traceState) ->
    let open Interop.Adapters in
    exists h1_pre_pop.
      h1_pre_pop == hs_of_mem (snd fuel_mem) /\
      HS.poppable h1_pre_pop /\ (
      exists h1. h1 == HS.pop h1_pre_pop /\
        mem_roots_p h1 args /\
        LSig.(to_low_post post args h0 () h1))

let pop_is_popped (m:HS.mem{HS.poppable m})
  : Lemma (HS.popped m (HS.pop m))
  = ()

let loc_includes_union (l1 l1' l:B.loc)
  : Lemma (requires B.(loc_includes l1 l1'))
          (ensures  B.(loc_includes (loc_union l1 l) (loc_union l1' l)))
  = let open B in
    loc_includes_union_l l1 l l1'; 
    loc_includes_union_l l1 l l;    
    loc_includes_union_r (loc_union l1 l) l1' l
                      
#set-options "--z3rlimit_factor 2"
val vale_lemma_as_prediction
          (#n:IX64.max_slots)
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (pre:VSig.vale_pre_tl n [])
          (post:VSig.vale_post_tl n [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
   : IX64.prediction
             (coerce code)
             n
             args
             (prediction_pre_rel pre (coerce code) args)
             (prediction_post_rel post (coerce code) args)

let vale_lemma_as_prediction
          (#n:IX64.max_slots)
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (pre:VSig.vale_pre_tl n [])
          (post:VSig.vale_post_tl n [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
   = fun h0 s0 push_h0 alloc_push_h0 sb ->
       let c_code : TS.tainted_code = coerce code in
       let s_args = arg_of_sb sb :: args in
       let va_s0 = create_initial_vale_state args alloc_push_h0 sb in
       core_create_lemma args alloc_push_h0 sb;
       assert (SL.state_to_S va_s0 == s0);
       B.fresh_frame_modifies h0 push_h0;
       assert (B.modifies B.loc_none h0 alloc_push_h0);
       assert (LSig.mem_correspondence args alloc_push_h0 va_s0);
       frame_mem_correspondence_back args h0 alloc_push_h0 va_s0 B.loc_none;
       assert (LSig.mem_correspondence args h0 va_s0);
       assert (va_s0.VS.ok);
       assert (LSig.vale_pre_hyp sb args va_s0);
       assert (elim_nil pre va_s0 sb);
       let va_s1, f = VSig.elim_vale_sig_nil v va_s0 sb in
       assert (V.eval_code (c_code) va_s0 f va_s1);
       eval_code_rel (c_code) va_s0 va_s1 f;
       let Some s1 = TS.taint_eval_code (c_code) (coerce f) s0 in
       assert (VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1));
       assert (IX64.calling_conventions s0 s1);
       assert (ME.modifies (VSig.mloc_modified_args s_args) va_s0.VS.mem va_s1.VS.mem);
       let h1 = Interop.Adapters.hs_of_mem va_s1.VS.mem in
       let final_mem = va_s1.VS.mem in
       Vale.AsLowStar.MemoryHelpers.relate_modifies s_args va_s0.VS.mem va_s1.VS.mem;
       assert (B.modifies (loc_modified_args s_args) alloc_push_h0 h1);
       assume (FStar.HyperStack.ST.equal_domains alloc_push_h0 h1); //TODO: Vale code does not prove that it does not allocate
       Vale.AsLowStar.MemoryHelpers.state_eq_down_mem va_s1 s1;
       assert (IM.down_mem h1
                           (IA.addrs)
                           (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
       let h1_pre_pop = Interop.Adapters.hs_of_mem final_mem in
       assert (h1_pre_pop == h1);
       assert (IM.down_mem h1_pre_pop (IA.addrs) (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
       assert (va_s1.VS.mem == final_mem);
       mem_correspondence_refl args va_s1;
       assert (HS.poppable h1_pre_pop);
       let h2 = HS.pop h1_pre_pop in
       args_fp args h0 push_h0;
       assert (HS.get_tip push_h0 == HS.get_tip h1_pre_pop);
       pop_is_popped h1_pre_pop;
       assert (HS.popped h1_pre_pop h2);
       B.popped_modifies h1_pre_pop h2;
       assert (VSig.readable args VS.(va_s1.mem));
       assert (disjoint_or_eq args);
       readable_all_live VS.(va_s1.mem) args;
       assert (all_live h1_pre_pop args);
       assert (mem_roots_p h1_pre_pop args);
       frame_mem_correspondence args h1_pre_pop h2 va_s1 (B.loc_regions false (Set.singleton (HS.get_tip h1_pre_pop)));
       assert (B.modifies (loc_modified_args s_args) alloc_push_h0 h1_pre_pop);
       assert (B.modifies (loc_modified_args s_args) push_h0 h1_pre_pop);       
       let l = (B.loc_all_regions_from false (HS.get_tip push_h0)) in
       assert (B.loc_includes l (B.loc_buffer sb));
       loc_includes_union l (B.loc_buffer sb) (loc_modified_args args);
       B.modifies_fresh_frame_popped h0 push_h0 (loc_modified_args args) h1_pre_pop h2;
       assert (B.modifies (loc_modified_args args) h0 h2);
       assert (LSig.(to_low_post post args h0 () h2));
       let x : nat & ME.mem = coerce f, va_s1.VS.mem in
       x

[@__reduce__]
let rec lowstar_typ
          #n
          (#dom:list td)
          (code:V.va_code)
          (args:list arg{IX64.arity_ok_2 dom args})
          (pre:VSig.vale_pre_tl n dom)
          (post:VSig.vale_post_tl n dom)
    : Type =
    let open FStar.HyperStack.ST in
    match dom with
    | [] ->
      unit ->
      Stack unit
        (requires (fun h0 ->
          mem_roots_p h0 args /\
          LSig.to_low_pre pre args h0))
        (ensures (fun h0 _ h1 ->
          mem_roots_p h1 args /\
          LSig.to_low_post post args h0 () h1))

    | hd::tl ->
      x:td_as_type hd ->
      lowstar_typ
        #n
        #tl
        code
        ((| hd, x |)::args)
        (elim_1 pre x)
        (elim_1 post x)

#set-options "--initial_ifuel 1"
private
let rec __test__wrap #n (#dom:list td)
             (code:V.va_code)
             (args:list arg{IX64.arity_ok_2 dom args})
             (num_stack_slots:nat)
             (pre:VSig.vale_pre_tl n dom)
             (post:VSig.vale_post_tl n dom)
             (v:VSig.vale_sig_tl args (coerce code) pre post)
    : lowstar_typ code args pre post =
    match dom with
    | [] ->
      let f :
        unit ->
        ST.Stack unit
          (requires (fun h0 ->
            mem_roots_p h0 args /\
            LSig.to_low_pre pre args h0))
          (ensures (fun h0 _ h1 ->
            mem_roots_p h1 args /\
            LSig.to_low_post post args h0 () h1)) =
         fun () ->
           let h0 = ST.get () in
           let prediction =
             vale_lemma_as_prediction _ _ _ _ v in
           let _ = IX64.wrap_variadic (coerce code) n args prediction in
           ()
      in
      f <: lowstar_typ #n #[] code args pre post
    | hd::tl ->
      fun (x:td_as_type hd) ->
        __test__wrap
          code
          IX64.(x ++ args)
          num_stack_slots
          (elim_1 pre x)
          (elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)

// ////////////////////////////////////////////////////////////////////////////////
// //Wrap abstract
// ////////////////////////////////////////////////////////////////////////////////
[@__reduce__]
let rec pre_rel_generic
      (#n:_)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{IX64.arity_ok_2 dom args})
      (pre:VSig.vale_pre_tl n dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_pre_rel_t (coerce code))
   = match dom with
     | [] ->
       prediction_pre_rel pre (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       pre_rel_generic code tl IX64.(x ++ args) (elim_1 pre x)

[@__reduce__]
let rec post_rel_generic
      (#n:_)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{IX64.arity_ok_2 dom args})
      (post:VSig.vale_post_tl n dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_post_rel_t (coerce code) n)
   = match dom with
     | [] ->
       prediction_post_rel post (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       post_rel_generic code tl IX64.(x ++ args) (elim_1 post x)

let rec mk_prediction
       #n
       (code:V.va_code)
       (dom:list td)
       (args:list arg{IX64.arity_ok_2 dom args})
       (#pre:VSig.vale_pre_tl n dom)
       (#post:VSig.vale_post_tl n dom)
       (v:VSig.vale_sig_tl args (coerce code) pre post)
   :  IX64.prediction_t
          (coerce code)
          n
          dom
          args
          (pre_rel_generic code dom args pre)
          (post_rel_generic code dom args post)
   = let open IX64 in
     match dom with
     | [] ->
       vale_lemma_as_prediction _ _ _ _ v
     | hd::tl ->
       fun (x:td_as_type hd) ->
        mk_prediction
          code
          tl
          (x ++ args)
          #(elim_1 pre x)
          #(elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)
