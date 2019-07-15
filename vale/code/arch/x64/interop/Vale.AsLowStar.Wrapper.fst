module Vale.AsLowStar.Wrapper
open Vale.X64.MemoryAdapters
open Vale.Interop.Base
module B = LowStar.Buffer
module BS = Vale.X64.Machine_Semantics_s
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module SI = Vale.X64.Stack_i
module MS = Vale.X64.Machine_s
module IA = Vale.Interop.Assumptions
module I = Vale.Interop
module V = Vale.X64.Decls
module VS = Vale.X64.State
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = Vale.X64.StateLemmas
module VL = Vale.X64.Lemmas
module ST = FStar.HyperStack.ST
open FStar.Mul
open FStar.Calc

let lemma_create_initial_vale_state_core
    (#max_arity:nat)
    (#reg_arg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures (
        let s = LSig.create_initial_vale_state #max_arity #reg_arg args h0 in
        hs_of_mem (as_mem s.VS.vs_heap) == h0
      ))
  = ()

#reset-options "--initial_ifuel 2 --max_ifuel 2"
let rec core_create_lemma_disjointness
    (args:list arg{disjoint_or_eq args})
  : Lemma
    (ensures VSig.disjoint_or_eq args)
  = match args with
    | [] -> ()
    | hd::tl ->
      disjoint_or_eq_cons hd tl;
      BigOps.pairwise_and'_cons VSig.disjoint_or_eq_1 hd tl;
      core_create_lemma_disjointness tl;
      assert (VSig.disjoint_or_eq tl);
      let rec aux (n:list arg)
        : Lemma (requires (BigOps.big_and' (disjoint_or_eq_1 hd) n))
                (ensures (BigOps.big_and' (VSig.disjoint_or_eq_1 hd) n)) =
        match n with
        | [] -> ()
        | n::ns ->
          BigOps.big_and'_cons (disjoint_or_eq_1 hd) n ns;
          BigOps.big_and'_cons (VSig.disjoint_or_eq_1 hd) n ns;
          aux ns
      in
      aux tl
#reset-options

let rec args_b8_lemma (args:list arg) (x:arg)
  : Lemma
      (List.memP x args ==>
        (match x with
         | (| TD_Buffer src bt _, x |) -> List.memP (mut_to_b8 src x) (args_b8 args)
         | (| TD_ImmBuffer src bt _, x |) -> List.memP (imm_to_b8 src x) (args_b8 args)
         | _ -> True))
  = match args with
    | [] -> ()
    | a::q ->
      assert (List.memP x q ==> List.memP x args);
      args_b8_lemma q x

let readable_cons (hd:arg) (tl:list arg) (s:ME.vale_heap)
  : Lemma VSig.(readable (hd::tl) s <==> (readable_one s hd /\ readable tl s))
  = BigOps.big_and'_cons VSig.(readable_one s) hd tl

let arg_is_registered_root (s:ME.vale_heap) (a:arg) =
  match a with
  | (| TD_Buffer src bt _, x |) ->
    List.memP (mut_to_b8 src x) (ptrs_of_mem (as_mem s))
  | (| TD_ImmBuffer src bt _, x |) ->
    List.memP (imm_to_b8 src x) (ptrs_of_mem (as_mem s))
  | _ -> true

#set-options "--z3rlimit 20"

let core_create_lemma_readable
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
         VSig.readable args VS.(va_s.vs_heap)))
  =
    let readable_registered_one (a:arg) (s:ME.vale_heap)
      : Lemma VSig.(arg_is_registered_root s a <==> readable_one s a)
      = match a with
        | (| TD_Buffer src bt _, x |) ->
          Vale.AsLowStar.MemoryHelpers.reveal_readable #src #bt x s;
          Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal src bt x
        | (| TD_ImmBuffer src bt ig, x |) ->
          Vale.AsLowStar.MemoryHelpers.reveal_imm_readable #src #bt x s;
          assert_norm (ME.buffer_readable s (as_vale_immbuffer #src #bt x) <==>
                       VSig.readable_one s (| TD_ImmBuffer src bt ig, x |))
        | (| TD_Base _, _ |) -> ()
    in
    let rec readable_registered_all
        (args:list arg)
        (s:ME.vale_heap {forall x. List.memP x args ==> arg_is_registered_root s x})
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
           (let mem = mk_mem args h in
            VSig.readable args (as_vale_mem mem))
       = let mem = mk_mem args h in
         FStar.Classical.forall_intro (FStar.Classical.move_requires (args_b8_lemma args));
         readable_registered_all args (as_vale_mem mem)
     in
     readable_mk_mem args h0

let readable_live_one (m:ME.vale_heap) (a:arg)
  : Lemma (VSig.readable_one m a ==>
           live_arg (hs_of_mem (as_mem m)) a)
  = match a with
    | (| TD_Buffer src bt _, x |) ->
      Vale.AsLowStar.MemoryHelpers.readable_live #src #bt x m
    | (| TD_ImmBuffer src bt ig, x |) ->
      Vale.AsLowStar.MemoryHelpers.readable_imm_live #src #bt x m;
      assert_norm (ME.buffer_readable m (as_vale_immbuffer #src #bt x) <==>
                   VSig.readable_one m (| TD_ImmBuffer src bt ig, x |))
    | (| TD_Base _, _ |) -> ()

let rec readable_all_live (m:ME.vale_heap) (args:list arg)
  : Lemma (VSig.readable args m ==>
           all_live (hs_of_mem (as_mem m)) args)
  = match args with
    | [] -> ()
    | hd::tl ->
      readable_cons hd tl m;
      all_live_cons hd tl (hs_of_mem (as_mem m));
      readable_live_one m hd;
      readable_all_live m tl

let core_create_lemma_mem_correspondance
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
         LSig.mem_correspondence args h0 va_s))
  =
    let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
    let rec aux (accu:list arg) : Lemma
      (requires (forall x. List.memP x accu ==> (live_arg h0 x)))
      (ensures LSig.mem_correspondence accu h0 va_s) =
    match accu with
    | [] -> ()
    | hd::tl -> aux tl;
      match hd with
      | (| TD_Buffer src bt _, x |) ->
        Vale.AsLowStar.MemoryHelpers.buffer_as_seq_reveal src bt x args h0;
        let db = get_downview x in
        DV.length_eq db;
        let ub = UV.mk_buffer db (LSig.view_of_base_typ bt) in
        assert (Seq.equal (UV.as_seq h0 ub) (UV.as_seq h0 ub))
      | (| TD_ImmBuffer src bt _, x |) ->
        Vale.AsLowStar.MemoryHelpers.immbuffer_as_seq_reveal src bt x args h0;
        let db = get_downview x in
        DV.length_eq db;
        let ub = UV.mk_buffer db (LSig.view_of_base_typ bt) in
        assert (Seq.equal (UV.as_seq h0 ub) (UV.as_seq h0 ub))
      | (| TD_Base _, _ |) -> ()
    in
    BigOps.big_and'_forall (live_arg h0) args;
    aux args

let rec register_args'
    (max_arity:nat)
    (arg_reg:IX64.arg_reg_relation max_arity)
    (n:nat)
    (args:list arg{List.length args = n})
    (regs:IX64.registers)
  : prop
  = match args with
    | [] -> True
    | hd::tl ->
      register_args' max_arity arg_reg (n - 1) tl regs /\
      (if n > max_arity then True
       else regs (arg_reg.IX64.of_arg (n - 1)) == IX64.arg_as_nat64 hd)

let rec lemma_register_args'_aux
    (max_arity:nat)
    (arg_reg:IX64.arg_reg_relation max_arity)
    (n:nat)
    (args:list arg{List.length args = n})
    (regs1 regs2:IX64.registers)
  : Lemma
      (requires
        register_args' max_arity arg_reg n args regs1 /\
        (forall r. (forall (i:IX64.reg_nat max_arity{i >= n}). r <> (arg_reg.IX64.of_arg i)) /\
              r <> MS.rRsp ==>
              regs1 r == regs2 r))
      (ensures register_args' max_arity arg_reg n args regs2)
  = match args with
    | [] -> ()
    | hd::tl ->
      lemma_register_args'_aux max_arity arg_reg (n-1) tl regs1 regs2

let rec lemma_register_args'
    (max_arity:nat)
    (arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (regs:IX64.registers)
  : Lemma
     (ensures
       (let final_regs = IX64.register_of_args max_arity arg_reg (List.length args) args regs in
        register_args' max_arity arg_reg (List.length args) args final_regs))
  = let final_regs = IX64.register_of_args max_arity arg_reg (List.length args) args regs in
    match args with
    | [] -> ()
    | hd::tl ->
      let n = List.length args in
      let regs' = (IX64.register_of_args max_arity arg_reg (n-1) tl regs) in
      lemma_register_args' max_arity arg_reg tl regs;
      lemma_register_args'_aux max_arity arg_reg (n-1) tl regs' final_regs

let core_create_lemma_register_args
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
                LSig.register_args max_arity arg_reg (List.length args) args va_s))
  =
    let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
    let regs' = IX64.register_of_args max_arity arg_reg (List.Tot.length args) args IA.init_regs in
    lemma_register_args' max_arity arg_reg args IA.init_regs;
    let open MS in
    let regs = FunctionalExtensionality.on reg_64 regs' in
    lemma_register_args'_aux max_arity arg_reg (List.length args) args regs' regs;
    assert (register_args' max_arity arg_reg (List.length args) args regs);
    let rec aux
        (args:IX64.arg_list)
        (s:VS.vale_state)
        (args':list arg)
        (h0:HS.mem{mem_roots_p h0 args'})
     : Lemma
         (requires
            (forall r. VS.eval_reg_64 r s == regs r) /\
            register_args' max_arity arg_reg (List.length args) args regs /\
            s.VS.vs_heap == as_vale_mem (mk_mem args' h0))
         (ensures LSig.register_args max_arity arg_reg (List.length args) args s)
         (decreases args)
    = let n = List.length args in
      match args with
      | [] -> ()
      | hd::tl -> aux tl s args' h0;
        let (| tag, x |) = hd in
        match tag with
        | TD_Buffer src bt _ -> Vale.AsLowStar.MemoryHelpers.buffer_addr_reveal src bt x args' h0
        | TD_ImmBuffer src bt _ -> Vale.AsLowStar.MemoryHelpers.immbuffer_addr_reveal src bt x args' h0
        | TD_Base _ -> ()
      in
      aux args va_s args h0

let core_create_lemma_state
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
         fst (IX64.create_initial_trusted_state max_arity arg_reg args I.down_mem h0) == SL.state_to_S va_s))
  = let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
    let tr_s = fst (IX64.create_initial_trusted_state max_arity arg_reg args I.down_mem h0) in
    let sl_s = SL.state_to_S va_s in
    assert (tr_s.BS.ms_memTaint == va_s.VS.vs_memTaint);
    assert (tr_s.BS.ms_stackTaint == va_s.VS.vs_stackTaint);
    SL.lemma_to_ok va_s;
    let aux_flag (f:MS.flag) : Lemma (tr_s.BS.ms_flags f == sl_s.BS.ms_flags f)
      = SL.lemma_to_flags va_s f
    in
    Classical.forall_intro aux_flag;
    assert (FunctionalExtensionality.feq tr_s.BS.ms_flags sl_s.BS.ms_flags);
    SL.lemma_to_mem va_s;
    SL.lemma_to_stack va_s;
    let aux_reg (r:MS.reg) : Lemma (tr_s.BS.ms_regs r == sl_s.BS.ms_regs r)
      = SL.lemma_to_reg va_s r
    in
    Classical.forall_intro aux_reg;
    assert (FunctionalExtensionality.feq tr_s.BS.ms_regs sl_s.BS.ms_regs);
    Vale.AsLowStar.MemoryHelpers.get_heap_mk_mem_reveal args h0;
    Vale.AsLowStar.MemoryHelpers.mk_stack_reveal tr_s.BS.ms_stack

let rec stack_args' (max_arity:nat)
                    (n:nat)
                    (args:list arg{List.Tot.length args = n})
                    (rsp:int)
                    (stack:Map.t int Vale.Def.Words_s.nat8)
                    : prop =
    match args with
    | [] -> True
    | hd::tl ->
        stack_args' max_arity (n-1) tl rsp stack /\
        (if n <= max_arity then True // This arg is passed in registers
         else
           let ptr = ((n - max_arity) - 1) * 8
             + (if IA.win then 32 else 0)
             + 8
             + rsp
           in
           BS.valid_addr64 ptr stack /\
           BS.get_heap_val64 ptr stack == IX64.arg_as_nat64 hd)

let frame_update_get_heap (ptr:int) (v:MS.nat64) (mem:BS.machine_heap) (j:int) : Lemma
  (requires ptr >= j + 8)
  (ensures BS.get_heap_val64 j mem == BS.get_heap_val64 j (BS.update_heap64 ptr v mem))
  =  
  Vale.Def.Opaque_s.reveal_opaque BS.get_heap_val64_def;
  Vale.Def.Opaque_s.reveal_opaque BS.update_heap64_def

let frame_update_valid_heap (ptr:int) (v:MS.nat64) (mem:BS.machine_heap) (j:int) : Lemma
  (requires ptr >= j + 8)
  (ensures BS.valid_addr64 j mem == BS.valid_addr64 j (BS.update_heap64 ptr v mem))
  =
  FStar.Pervasives.reveal_opaque (`%BS.valid_addr64) BS.valid_addr64;
  Vale.Def.Opaque_s.reveal_opaque BS.update_heap64_def

let rec stack_of_args_stack_args'_aux
    (max_arity:nat)
    (n_init:nat)
    (n:nat)
    (args:IX64.arg_list{List.Tot.length args = n})
    (rsp:int)
    (stack:Map.t int Vale.Def.Words_s.nat8)
    (v:MS.nat64)
    : Lemma
  (requires stack_args' max_arity n args rsp stack /\ n_init >= n)
  (ensures
    (let ptr = (n_init - max_arity) * 8 + (if IA.win then 32 else 0) + 8 + rsp in
    stack_args' max_arity n args rsp (BS.update_heap64 ptr v stack)))
  = match args with
    | [] -> ()
    | hd::tl ->
      stack_of_args_stack_args'_aux max_arity n_init (n-1) tl rsp stack v;
      if n <= max_arity then ()
      else (
        let fixed = (n_init - max_arity) * 8 + (if IA.win then 32 else 0) + 8 + rsp in
        let ptr = ((n - max_arity) - 1) * 8
          + (if IA.win then 32 else 0)
          + 8
          + rsp
        in
        calc ( <= ) {
          ((n - max_arity) - 1) * 8;
          ( <= ) { FStar.Math.Lemmas.lemma_mult_le_right 8 ((n - max_arity) - 1) (n_init - max_arity) }
          (n_init - max_arity) * 8;
        };
        frame_update_get_heap fixed v stack ptr;
        frame_update_valid_heap fixed v stack ptr
     )

#push-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 150 --z3refresh"
let rec stack_of_args_stack_args'
    (max_arity:nat)
    (n:nat)
    (args:IX64.arg_list{List.Tot.length args = n})
    (init_rsp:MS.nat64{init_rsp >= 4096}) : Lemma
    (let mem = Map.const_on Set.empty 0 in
    stack_args' max_arity n args init_rsp (IX64.stack_of_args max_arity n init_rsp args mem))
    =
    FStar.Pervasives.reveal_opaque (`%BS.valid_addr64) BS.valid_addr64;
    FStar.Pervasives.reveal_opaque (`%BS.valid_addr128) BS.valid_addr128;
    let rec aux (args:IX64.arg_list) (accu:Map.t int Vale.Def.Words_s.nat8) : Lemma (ensures (
      stack_args' max_arity (List.length args) args init_rsp
        (IX64.stack_of_args max_arity (List.length args) init_rsp args accu)))
      (decreases (List.length args))
      =
      FStar.Pervasives.reveal_opaque (`%BS.valid_addr64) BS.valid_addr64;
      FStar.Pervasives.reveal_opaque (`%BS.valid_addr128) BS.valid_addr128;
      match args with
      | [] -> ()
      | hd::tl ->
        aux tl accu;
        let n = List.length args in
        if n <= max_arity then ()
        else (
          let ptr = ((n - max_arity) - 1) * 8 // Arguments on the stack are pushed from right to left
            + (if IA.win then 32 else 0) // The shadow space on Windows comes next
            + 8 // The return address is then pushed on the stack
            + init_rsp // And we then have all the extra slots required for the Vale procedure
          in
          let accu' = IX64.stack_of_args max_arity (n-1) init_rsp tl accu in
          let v = IX64.arg_as_nat64 hd in // We will store the arg hd
          let h_final = BS.update_heap64 ptr v accu' in
          stack_of_args_stack_args'_aux max_arity (n-1) (n-1) tl init_rsp accu' v;
          Vale.X64.Bytes_Semantics.correct_update_get ptr v accu';
          Vale.Def.Opaque_s.reveal_opaque BS.update_heap64_def
        )


    in aux args (Map.const_on Set.empty 0)
#pop-options

#reset-options "--z3rlimit 40"
let core_create_lemma_stack_args
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
                LSig.stack_args max_arity (List.length args) args va_s))
  = let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
    let init_rsp = IA.init_regs MS.rRsp in
    let stack = Map.const_on Set.empty 0 in
    let stack_map = IX64.stack_of_args max_arity (List.Tot.length args) init_rsp args stack in
    let stack_f = BS.Machine_stack init_rsp stack_map in
    let rec aux (accu:IX64.arg_list{List.length accu <= List.length args}) : Lemma
      (requires
         stack_args' max_arity (List.length accu) accu init_rsp stack_map)
      (ensures LSig.stack_args max_arity (List.length accu) accu va_s)
      (decreases (List.length accu))
    =
    match accu with
      | [] -> ()
      | hd::tl ->
        aux tl;
        let i = List.length accu in
        if i <= max_arity then ()
        else (
          let ptr =
            ((i  - max_arity) - 1) * 8
             + (if IA.win then 32 else 0)
             + 8
             + init_rsp
          in
          Vale.AsLowStar.MemoryHelpers.mk_stack_reveal stack_f;
          SI.lemma_valid_taint_stack64_reveal ptr MS.Public va_s.VS.vs_stackTaint;
          let aux2 () : Lemma (IX64.arg_as_nat64 hd == LSig.arg_as_nat64 hd va_s) =
            match hd with
            | (| TD_Buffer src bt _, x |) ->
              Vale.AsLowStar.MemoryHelpers.buffer_addr_reveal src bt x args h0
            | (| TD_ImmBuffer src bt _, x |) ->
              Vale.AsLowStar.MemoryHelpers.immbuffer_addr_reveal src bt x args h0
            | _ -> ()
          in aux2()
        )
    in
    stack_of_args_stack_args' max_arity (List.length args) args init_rsp;
    aux args

let core_create_lemma
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
         fst (IX64.create_initial_trusted_state max_arity arg_reg args I.down_mem h0) == SL.state_to_S va_s /\
         LSig.mem_correspondence args h0 va_s /\
         VSig.disjoint_or_eq args /\
         VSig.readable args VS.(va_s.vs_heap) /\
         LSig.vale_pre_hyp #max_arity #arg_reg args va_s /\
         ST.equal_domains h0 (hs_of_mem (as_mem va_s.VS.vs_heap))
  ))
  = let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
    let t_state = fst (IX64.create_initial_trusted_state max_arity arg_reg args I.down_mem h0) in
    let t_stack = t_state.BS.ms_stack in
    core_create_lemma_mem_correspondance #max_arity #arg_reg args h0;
    core_create_lemma_disjointness args;
    core_create_lemma_readable #max_arity #arg_reg args h0;
    core_create_lemma_register_args #max_arity #arg_reg args h0;
    core_create_lemma_stack_args #max_arity #arg_reg args h0;
    Vale.AsLowStar.MemoryHelpers.mk_stack_reveal t_stack;
    Vale.AsLowStar.MemoryHelpers.core_create_lemma_taint_hyp #max_arity #arg_reg args h0;
    core_create_lemma_state #max_arity #arg_reg args h0

let eval_code_ts (c:BS.code)
                 (s0:BS.machine_state)
                 (f0:nat)
                 (s1:BS.machine_state) : Type0 =
  VL.state_eq_opt (BS.machine_eval_code c f0 s0) (Some s1)

let eval_code_rel (c:BS.code)
                  (va_s0 va_s1:_) (f:V.va_fuel)
  : Lemma
     (requires (V.eval_code c va_s0 f va_s1))
     (ensures (eval_code_ts c (SL.state_to_S va_s0) (coerce f) (SL.state_to_S va_s1)))
  = Vale.AsLowStar.MemoryHelpers.decls_eval_code_reveal c va_s0 va_s1 f

let rec mem_correspondence_refl (args:list arg)
                                (va_s:V.va_state)
 : Lemma
     (ensures LSig.mem_correspondence args (hs_of_mem (as_mem va_s.VS.vs_heap)) va_s)
 =
   let h = hs_of_mem (as_mem va_s.VS.vs_heap) in
   match args with
   | [] -> ()
   | hd::tl ->
     mem_correspondence_refl tl va_s;
     match hd with
     | (| TD_Buffer src bt _, x |) ->
       Vale.AsLowStar.MemoryHelpers.buffer_as_seq_reveal2 src bt x va_s
     | (| TD_ImmBuffer src bt _, x |) ->
       Vale.AsLowStar.MemoryHelpers.immbuffer_as_seq_reveal2 src bt x va_s
     | _ -> ()

////////////////////////////////////////////////////////////////////////////////

[@__reduce__]
let prediction_pre_rel
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          (pre:VSig.vale_pre_tl [])
          (code:V.va_code)
          (args:IX64.arg_list)
   : IX64.prediction_pre_rel_t code args
   = fun (h0:mem_roots args) ->
      LSig.(to_low_pre #max_arity #arg_reg pre args h0)

[@__reduce__]
let prediction_post_rel
          (#max_arity:nat)
          (post:VSig.vale_post_tl [])
          (code:V.va_code)
          (args:IX64.arg_list)
   : IX64.prediction_post_rel_t code args
   = fun (h0:mem_roots args)
       (_s0:BS.machine_state)
       (rax_fuel_mem:(UInt64.t & nat & ME.vale_heap))
       (s1:BS.machine_state) ->
    let rax, fuel, mem = rax_fuel_mem in
    exists h1.
      h1 == hs_of_mem (as_mem mem) /\
      mem_roots_p h1 args /\
      LSig.(to_low_post post args h0 rax h1)

let loc_includes_union (l1 l1' l:B.loc)
  : Lemma (requires B.(loc_includes l1 l1'))
          (ensures  B.(loc_includes (loc_union l1 l) (loc_union l1' l)))
  = let open B in
    loc_includes_union_l l1 l l1';
    loc_includes_union_l l1 l l;
    loc_includes_union_r (loc_union l1 l) l1' l

#set-options "--z3rlimit_factor 2"
val vale_lemma_as_prediction
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          (#regs_modified:MS.reg_64 -> bool)
          (#xmms_modified:MS.reg_xmm -> bool)
          (code:V.va_code)
          (args:IX64.arg_list)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
   : IX64.prediction
             max_arity
             arg_reg
             regs_modified
             xmms_modified
             I.down_mem
             (coerce code)
             args
             (prediction_pre_rel #max_arity #arg_reg pre (coerce code) args)
             (prediction_post_rel #max_arity post (coerce code) args)

let vale_lemma_as_prediction
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          (#regs_modified:MS.reg_64 -> bool)
          (#xmms_modified:MS.reg_xmm -> bool)
          (code:V.va_code)
          (args:IX64.arg_list)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
   = fun h0 s0 ->
       let c_code : BS.code = coerce code in
       let va_s0 = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
       core_create_lemma #max_arity #arg_reg args h0;
       assert (SL.state_to_S va_s0 == s0);
       assert (LSig.mem_correspondence args h0 va_s0);
       assert (va_s0.VS.vs_ok);
       assert (LSig.vale_pre_hyp #max_arity #arg_reg args va_s0);
       assert (elim_nil pre va_s0);
       let va_s1, f = VSig.elim_vale_sig_nil v va_s0 in
       assert (V.eval_code code va_s0 f va_s1);
       eval_code_rel (c_code) va_s0 va_s1 f;
       let Some s1 = BS.machine_eval_code (c_code) (coerce f) s0 in
       assert (VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1));
       assert (VSig.vale_calling_conventions va_s0 va_s1 regs_modified xmms_modified);
       assert (IX64.calling_conventions s0 s1 regs_modified xmms_modified);
       assert (ME.modifies (VSig.mloc_modified_args args) va_s0.VS.vs_heap va_s1.VS.vs_heap);
       let final_mem = va_s1.VS.vs_heap in
       let h1= hs_of_mem (as_mem final_mem) in
       Vale.AsLowStar.MemoryHelpers.relate_modifies args va_s0.VS.vs_heap va_s1.VS.vs_heap;
       assert (B.modifies (loc_modified_args args) h0 h1);
       Vale.AsLowStar.MemoryHelpers.modifies_equal_domains
         (VSig.mloc_modified_args args) va_s0.VS.vs_heap final_mem;
       Vale.AsLowStar.MemoryHelpers.modifies_same_roots
         (VSig.mloc_modified_args args) va_s0.VS.vs_heap final_mem;
       Vale.AsLowStar.MemoryHelpers.state_eq_down_mem va_s1 s1;
       assert (I.down_mem (as_mem final_mem) == s1.BS.ms_heap);
       mem_correspondence_refl args va_s1;
       assert (VSig.readable args VS.(va_s1.vs_heap));
       assert (disjoint_or_eq args);
       readable_all_live VS.(va_s1.vs_heap) args;
       assert (all_live h1 args);
       assert (mem_roots_p h1 args);
       assert (B.modifies (loc_modified_args args) h0 h1);
       assert (LSig.(to_low_post post args h0 (IX64.return_val s1) h1));
       IX64.return_val s1, coerce f, as_mem va_s1.VS.vs_heap

[@__reduce__]
let rec lowstar_typ
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          (#dom:list td)
          (code:V.va_code)
          (args:IX64.arg_list{List.length args + List.length dom <= 20})
          (pre:VSig.vale_pre_tl dom)
          (post:VSig.vale_post_tl dom)
    : Type =
    let open FStar.HyperStack.ST in
    match dom with
    | [] ->
      unit ->
      Stack UInt64.t
        (requires (fun h0 ->
          mem_roots_p h0 args /\
          LSig.to_low_pre #max_arity #arg_reg pre args h0))
        (ensures (fun h0 v h1 ->
          mem_roots_p h1 args /\
          LSig.to_low_post post args h0 v h1))

    | hd::tl ->
      x:td_as_type hd ->
      lowstar_typ
        #max_arity
        #arg_reg
        #tl
        code
        ((| hd, x |)::args)
        (elim_1 pre x)
        (elim_1 post x)

#set-options "--initial_ifuel 1"
private
let rec __test__wrap
             (#max_arity:nat)
             (#arg_reg:IX64.arg_reg_relation max_arity)
             (#regs_modified:MS.reg_64 -> bool)
             (#xmms_modified:MS.reg_xmm -> bool)
             (#dom:list td)
             (code:V.va_code)
             (args:list arg{List.length dom + List.length args <= 20})
             (pre:VSig.vale_pre_tl dom)
             (post:VSig.vale_post_tl dom)
             (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
    : lowstar_typ code args pre post =
    match dom with
    | [] ->
      let f :
        unit ->
        ST.Stack UInt64.t
          (requires (fun h0 ->
            mem_roots_p h0 args /\
            LSig.to_low_pre #max_arity #arg_reg pre args h0))
          (ensures (fun h0 r h1 ->
            mem_roots_p h1 args /\
            LSig.to_low_post post args h0 r h1)) =
         fun () ->
           let h0 = ST.get () in
           let prediction =
             vale_lemma_as_prediction code args pre post v in
           let rax, ret = IX64.wrap_variadic (coerce code) max_arity arg_reg regs_modified xmms_modified I.down_mem args prediction in
           rax
      in
      f <: lowstar_typ #max_arity #arg_reg #[] code args pre post
    | hd::tl ->
      fun (x:td_as_type hd) ->
        __test__wrap
          #max_arity
          #arg_reg
          code
          IX64.(x ++ args)
          (elim_1 pre x)
          (elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)

// ////////////////////////////////////////////////////////////////////////////////
// //Wrap abstract
// ////////////////////////////////////////////////////////////////////////////////
[@__reduce__]
let rec pre_rel_generic
      (#max_arity:nat)
      (#arg_reg:IX64.arg_reg_relation max_arity)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= 20})
      (pre:VSig.vale_pre_tl dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_pre_rel_t (coerce code))
   = match dom with
     | [] ->
       prediction_pre_rel #max_arity #arg_reg pre (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       pre_rel_generic #max_arity #arg_reg code tl IX64.(x ++ args) (elim_1 pre x)

[@__reduce__]
let rec post_rel_generic
      (#max_arity:nat)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= 20})
      (post:VSig.vale_post_tl dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_post_rel_t (coerce code))
   = match dom with
     | [] ->
       prediction_post_rel #max_arity post (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       post_rel_generic #max_arity code tl IX64.(x ++ args) (elim_1 post x)

let rec mk_prediction
       (#max_arity:nat)
       (#arg_reg:IX64.arg_reg_relation max_arity)
       (#regs_modified:MS.reg_64 -> bool)
       (#xmms_modified:MS.reg_xmm -> bool)
       (code:V.va_code)
       (dom:list td)
       (args:list arg{List.length dom + List.length args <= 20})
       (#pre:VSig.vale_pre_tl dom)
       (#post:VSig.vale_post_tl dom)
       (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
   :  IX64.prediction_t
          max_arity
          arg_reg
          regs_modified
          xmms_modified
          I.down_mem
          (coerce code)
          dom
          args
          (pre_rel_generic #max_arity #arg_reg code dom args pre)
          (post_rel_generic #max_arity code dom args post)
   = let open IX64 in
     match dom with
     | [] ->
       vale_lemma_as_prediction #max_arity #arg_reg _ _ _ _ v
     | hd::tl ->
       fun (x:td_as_type hd) ->
        mk_prediction
          #max_arity
          #arg_reg
          code
          tl
          (x ++ args)
          #(elim_1 pre x)
          #(elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)
