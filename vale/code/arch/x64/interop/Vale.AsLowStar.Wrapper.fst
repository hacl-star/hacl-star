module Vale.AsLowStar.Wrapper
open X64.MemoryAdapters
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module I = Interop
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = X64.Vale.StateLemmas
module VL = X64.Vale.Lemmas
module ST = FStar.HyperStack.ST
open FStar.Mul

let lemma_create_initial_vale_state_core
    (#max_arity:nat)
    (#reg_arg:IX64.arg_reg_relation max_arity)
    (#n:IX64.max_slots)
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\    
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (
        let s = LSig.create_initial_vale_state #max_arity #reg_arg args h0 stack in
        let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in
        hs_of_mem (as_mem s.VS.mem) == h1
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

let readable_cons (hd:arg) (tl:list arg) (s:ME.mem)
  : Lemma VSig.(readable (hd::tl) s <==> (readable_one s hd /\ readable tl s))
  = BigOps.big_and'_cons VSig.(readable_one s) hd tl

let arg_is_registered_root (s:ME.mem) (a:arg) =
  match a with
  | (| TD_Buffer src bt _, x |) ->
    List.memP (mut_to_b8 src x) (ptrs_of_mem (as_mem s))
  | (| TD_ImmBuffer src bt _, x |) ->
    List.memP (imm_to_b8 src x) (ptrs_of_mem (as_mem s))    
  | _ -> true

let core_create_lemma_readable
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\    
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
         VSig.readable (arg_of_sb stack::args) VS.(va_s.mem)))
  =
    let readable_registered_one (a:arg) (s:ME.mem)
      : Lemma
          VSig.(arg_is_registered_root s a <==> readable_one s a)
      = match a with
        | (| TD_Buffer src bt _, x |) ->
          Vale.AsLowStar.MemoryHelpers.reveal_readable #src #bt x s;
          Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal src bt x
        | (| TD_ImmBuffer src bt _, x |) ->
          Vale.AsLowStar.MemoryHelpers.reveal_imm_readable #src #bt x s
        | (| TD_Base _, _ |) -> ()
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
           (let mem = mk_mem args h in
            VSig.readable args (as_vale_mem mem))
       = let mem = mk_mem args h in
         FStar.Classical.forall_intro (FStar.Classical.move_requires (args_b8_lemma args));
         readable_registered_all args (as_vale_mem mem)
     in
     let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in
     IX64.live_arg_modifies h0 h1 args stack;     
     readable_mk_mem (arg_of_sb stack::args) h1

let readable_live_one (m:ME.mem) (a:arg)
  : Lemma (VSig.readable_one m a ==>
           live_arg (hs_of_mem (as_mem m)) a)
  = match a with
    | (| TD_Buffer src bt _, x |) ->
      Vale.AsLowStar.MemoryHelpers.readable_live #src #bt x m
    | (| TD_ImmBuffer src bt _, x |) ->
      Vale.AsLowStar.MemoryHelpers.readable_imm_live #src #bt x m
    | (| TD_Base _, _ |) -> ()

let rec readable_all_live (m:ME.mem) (args:list arg)
  : Lemma (VSig.readable args m ==>
           all_live (hs_of_mem (as_mem m)) args)
  = match args with
    | [] -> ()
    | hd::tl ->
      readable_cons hd tl m;
      all_live_cons hd tl (hs_of_mem (as_mem m));
      readable_live_one m hd;
      readable_all_live m tl

let core_create_lemma_readable2
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\    
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
         ME.buffer_readable VS.(va_s.mem) (as_vale_buffer stack) /\
         VSig.readable args VS.(va_s.mem)))
  = core_create_lemma_readable #max_arity #arg_reg args h0 stack;
    let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
    readable_cons (arg_of_sb stack) args VS.(va_s.mem)

let core_create_lemma_mem_correspondance
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\    
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
         LSig.mem_correspondence args h0 va_s))
  =
    let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
    let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in    
    let rec aux (accu:list arg) : Lemma 
      (requires (forall x. List.memP x accu ==> (
        disjoint_or_eq_1 (arg_of_sb stack) x /\
        live_arg h0 x)))
      (ensures LSig.mem_correspondence accu h0 va_s) =
    match accu with
    | [] -> ()
    | hd::tl -> aux tl;
        IX64.live_arg_modifies h0 h1 args stack;      
      match hd with
      | (| TD_Buffer src bt _, x |) ->
        Vale.AsLowStar.MemoryHelpers.buffer_as_seq_reveal src bt x args h1 stack;
        Vale.AsLowStar.MemoryHelpers.same_buffer_same_upviews #src #bt x h0 h1;
        let db = get_downview x in
        DV.length_eq db;
        let ub = UV.mk_buffer db (LSig.view_of_base_typ bt) in
        assert (Seq.equal (UV.as_seq h0 ub) (UV.as_seq h1 ub))
      | (| TD_ImmBuffer src bt _, x |) ->
        Vale.AsLowStar.MemoryHelpers.immbuffer_as_seq_reveal src bt x args h1 stack;
        Vale.AsLowStar.MemoryHelpers.same_immbuffer_same_upviews #src #bt x h0 h1;
        let db = get_downview x in
        DV.length_eq db;
        let ub = UV.mk_buffer db (LSig.view_of_base_typ bt) in
        assert (Seq.equal (UV.as_seq h0 ub) (UV.as_seq h1 ub))        
      | (| TD_Base _, _ |) -> ()
    in
    BigOps.big_and'_forall (disjoint_or_eq_1 (arg_of_sb stack)) args;
    BigOps.big_and'_forall (live_arg h0) args;
    aux args

#set-options "--z3rlimit 20"

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
              r <> MS.Rsp ==>
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
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\    
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
                LSig.register_args max_arity arg_reg (List.length args) args va_s))
  =
    let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
    let regs' = IX64.register_of_args max_arity arg_reg (List.Tot.length args) args IA.init_regs in
    lemma_register_args' max_arity arg_reg args IA.init_regs;
    let open MS in
    let regs = FunctionalExtensionality.on reg (IX64.regs_with_stack regs' stack) in
    lemma_register_args'_aux max_arity arg_reg (List.length args) args regs' regs;
    assert (register_args' max_arity arg_reg (List.length args) args regs);
    let rec aux
        (args:IX64.arg_list)
        (s:VS.state)
        (args':list arg)
        (h0:HS.mem{mem_roots_p h0 args'})
     : Lemma
         (requires
            (forall r. VS.eval_reg r s == regs r) /\
            register_args' max_arity arg_reg (List.length args) args regs /\
            s.VS.mem == as_vale_mem (mk_mem args' h0))
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
      let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in  
      IX64.live_arg_modifies h0 h1 args stack;      
      aux args va_s (arg_of_sb stack::args) h1

let core_create_lemma_state
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
         fst (IX64.create_initial_trusted_state max_arity arg_reg n args I.down_mem h0 stack) == SL.state_to_S va_s))
  = let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
    let tr_s = fst (IX64.create_initial_trusted_state max_arity arg_reg n args I.down_mem h0 stack) in
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
    let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in  
    IX64.live_arg_modifies h0 h1 args stack;       
    Vale.AsLowStar.MemoryHelpers.get_heap_mk_mem_reveal args h1 stack

let rec stack_of_args_equal_domains
    (#num_b8_slots:_)
    (max_arity:nat)
    (n:nat)
    (args:IX64.arg_list{List.Tot.length args = n})
    (stack_b:IX64.stack_buffer num_b8_slots
      {B.length stack_b >= num_b8_slots/8 + (List.Tot.length args - max_arity) + 5 })
    (h:HS.mem{B.live h stack_b}) : Lemma
    (ST.equal_domains h (IX64.stack_of_args max_arity n args stack_b h))
    = match args with
    | [] -> ()
    | hd::tl ->
    if n <= max_arity then ()
    else 
      let i = (n - max_arity) - 1 // Arguments on the stack are pushed from right to left
        + (if IA.win then 4 else 0) // The shadow space on Windows comes next
        + 1 // The return address is then pushed on the stack
        + num_b8_slots / 8 // And we then have all the extra slots required for the Vale procedure
      in
      let h1 = IX64.stack_of_args max_arity (n-1) tl stack_b h in      
      let v = UInt64.uint_to_t (IX64.arg_as_nat64 hd) in // We will store the arg hd
      B.g_upd_seq_as_seq stack_b (Seq.upd (B.as_seq h1 stack_b) i v) h1;
      stack_of_args_equal_domains max_arity (n-1) tl stack_b h

let rec stack_args' (max_arity:nat)
                   (num_b8_slots:IX64.max_slots)
                   (n:nat)
                   (args:list arg{List.Tot.length args = n})
                   (h0:HS.mem)
                   (stack_b:IX64.stack_buffer num_b8_slots
                      {B.length stack_b >= num_b8_slots/8 + (List.Tot.length args - max_arity) + 5 })
                   : prop =
    match args with
    | [] -> True
    | hd::tl ->
        stack_args' max_arity num_b8_slots (n - 1) tl h0 stack_b /\
        (if n <= max_arity then True // This arg is passed in registers
         else 
           let i = (n - max_arity) - 1
             + (if IA.win then 4 else 0)
             + 1
             + num_b8_slots/8
           in
           UInt64.v (B.get h0 stack_b i) == IX64.arg_as_nat64 hd)

let rec stack_of_args_stack_args'
    (#num_b8_slots:_)
    (max_arity:nat)
    (n:nat)
    (args:IX64.arg_list{List.Tot.length args = n})
    (stack_b:IX64.stack_buffer num_b8_slots
      {B.length stack_b >= num_b8_slots/8 + (List.Tot.length args - max_arity) + 5 })
    (h0:HS.mem{B.live h0 stack_b}) : Lemma
    (stack_args' max_arity num_b8_slots n args (IX64.stack_of_args max_arity n args stack_b h0) stack_b)
    = match args with
    | [] -> ()
    | hd::tl ->
      if n <= max_arity then stack_of_args_stack_args' max_arity (n-1) tl stack_b h0
      else
      let i = (n - max_arity) - 1 // Arguments on the stack are pushed from right to left
        + (if IA.win then 4 else 0) // The shadow space on Windows comes next
        + 1 // The return address is then pushed on the stack
        + num_b8_slots / 8 // And we then have all the extra slots required for the Vale procedure
      in
      let v = UInt64.uint_to_t (IX64.arg_as_nat64 hd) in // We will store the arg hd
      let h1 = IX64.stack_of_args max_arity (n-1) tl stack_b h0 in
      B.g_upd_seq_as_seq stack_b (Seq.upd (B.as_seq h1 stack_b) i v) h1;
      stack_of_args_stack_args' max_arity (n-1) tl stack_b h0;
      let h_f = IX64.stack_of_args max_arity n args stack_b h0 in
      let rec aux (accu:list arg{List.length accu < n}) : Lemma
        (requires 
          Seq.equal (B.as_seq h_f stack_b) (Seq.upd (B.as_seq h1 stack_b) i v) /\
          stack_args' max_arity num_b8_slots (List.length accu) accu h1 stack_b)
        (ensures stack_args' max_arity num_b8_slots (List.length accu) accu h_f stack_b)
      = match accu with
      | [] -> ()
      | hd::tl -> aux tl
      in aux tl

let core_create_lemma_stack_args
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\    
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
                LSig.stack_args max_arity n (List.length args) args stack va_s))
  =
    let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
    let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in
    IX64.live_arg_modifies h0 h1 args stack;
    assert (mem_roots_p h1 (arg_of_sb stack::args));   
    let rec aux (accu:IX64.arg_list{List.length accu <= List.length args}) : Lemma
      (requires 
        mem_roots_p h1 (arg_of_sb stack::args) /\
        stack_args' max_arity n (List.length accu) accu h1 stack)
      (ensures LSig.stack_args max_arity n (List.length accu) accu stack va_s)
    = match accu with
      | [] -> ()
      | hd::tl -> aux tl;
        let i = List.length accu in
        if i <= max_arity then ()
        else (
          let j = (i - max_arity) - 1 + (if IA.win then 4 else 0) + 1 + n/8 in
          assert (UInt64.v (B.get h1 stack j) == IX64.arg_as_nat64 hd);
          DV.length_eq (get_downview stack);
          let aux2 () : Lemma (IX64.arg_as_nat64 hd == LSig.arg_as_nat64 hd va_s) =
            match hd with
            | (| TD_Buffer src bt _, x |) ->
              Vale.AsLowStar.MemoryHelpers.buffer_addr_reveal src bt x (arg_of_sb stack::args) h1
            | (| TD_ImmBuffer src bt _, x |) ->              
              Vale.AsLowStar.MemoryHelpers.immbuffer_addr_reveal src bt x (arg_of_sb stack::args) h1
            | _ -> ()
          in aux2();
          Vale.AsLowStar.MemoryHelpers.buffer_as_seq_reveal2 TUInt64 TUInt64 stack va_s;
          Vale.AsLowStar.MemoryHelpers.down_up_buffer_read_reveal TUInt64 h1 va_s.VS.mem stack j
        )
    in
    stack_of_args_stack_args' max_arity (List.length args) args stack h0;
    aux args


let core_create_lemma
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    #n
    (args:IX64.arg_list)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{
      B.length stack >= n/8 + (List.Tot.length args - max_arity) + 5 /\
      mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures
        (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
         fst (IX64.create_initial_trusted_state max_arity arg_reg n args I.down_mem h0 stack) == SL.state_to_S va_s /\
         LSig.mem_correspondence args h0 va_s /\
         VSig.disjoint_or_eq (arg_of_sb stack :: args) /\
         VSig.readable args VS.(va_s.mem) /\
         LSig.vale_pre_hyp #max_arity #arg_reg args stack va_s /\
         ST.equal_domains h0 (hs_of_mem (as_mem va_s.VS.mem)) /\
         V.valid_stack_slots
                va_s.VS.mem
                (VS.eval_reg MS.Rsp va_s)
                (as_vale_buffer stack)
                (n / 8)
                va_s.VS.memTaint
  ))
  =  
  let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 stack in
    core_create_lemma_mem_correspondance #max_arity #arg_reg args h0 stack;
    core_create_lemma_disjointness (arg_of_sb stack :: args);
    core_create_lemma_readable #max_arity #arg_reg args h0 stack;
    core_create_lemma_readable2 #max_arity #arg_reg args h0 stack;
    core_create_lemma_register_args #max_arity #arg_reg args h0 stack;
    core_create_lemma_stack_args #max_arity #arg_reg args h0 stack;
    Vale.AsLowStar.MemoryHelpers.core_create_lemma_taint_hyp #max_arity #arg_reg args h0 stack;
    core_create_lemma_state #max_arity #arg_reg args h0 stack;
    Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 stack;
    let s_args = arg_of_sb stack :: args in
    let h1 = IX64.stack_of_args max_arity (List.Tot.length args) args stack h0 in  
    stack_of_args_equal_domains max_arity (List.Tot.length args) args stack h0;
    IX64.live_arg_modifies h0 h1 args stack;           
    Vale.AsLowStar.MemoryHelpers.buffer_addr_reveal _ _ stack (arg_of_sb stack :: args) h1;
    DV.length_eq (get_downview stack);
    Vale.AsLowStar.MemoryHelpers.as_vale_buffer_len stack;
    FStar.Math.Lemmas.lemma_div_le n (B.length stack * 8) 8

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
     | (| TD_Buffer src bt _, x |) | (| TD_ImmBuffer src bt _, x |) ->
       BufferViewHelpers.lemma_dv_equal (down_view src) x h0 h1;
       DV.length_eq (get_downview x);
       BufferViewHelpers.lemma_uv_equal (LSig.view_of_base_typ bt) (get_downview x) h0 h1
     | (| TD_Base _, _ |) -> ()

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
 = match args with
   | [] -> ()
   | hd::tl ->
     frame_mem_correspondence tl h0 h1 va_s l;
     match hd with
     | (| TD_Buffer src bt _, x |) | (| TD_ImmBuffer src bt _, x |) ->
       BufferViewHelpers.lemma_dv_equal (down_view src) x h0 h1;
       DV.length_eq (get_downview x);
       BufferViewHelpers.lemma_uv_equal (LSig.view_of_base_typ bt) (get_downview x) h0 h1     
     | (| TD_Base _, _ |) -> ()

let rec args_fp (args:list arg)
                (h0:mem_roots args)
                (h1:HS.mem{HS.fresh_frame h0 h1})
  : Lemma
      (B.loc_disjoint (loc_all_args args) (B.loc_regions false (Set.singleton (HS.get_tip h1))))
  = match args with
    | [] -> ()
    | hd::tl -> args_fp tl h0 h1; 
      match hd with
      | (| TD_Buffer _ _ _, _ |) | (| TD_Base _, _ |) -> ()
      | (| TD_ImmBuffer _ _ _, x |) -> 
        assert (B.loc_includes (B.loc_not_unused_in h0) (B.loc_buffer x))

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
     (ensures LSig.mem_correspondence args (hs_of_mem (as_mem va_s.VS.mem)) va_s)
 =
   let h = hs_of_mem (as_mem va_s.VS.mem) in
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
          (#n:IX64.max_slots)
          (pre:VSig.vale_pre_tl n [])
          (code:V.va_code)
          (args:IX64.arg_list)
   : IX64.prediction_pre_rel_t code args
   = fun (h0:mem_roots args) ->
      LSig.(to_low_pre #max_arity #arg_reg pre args h0)

[@__reduce__]
let prediction_post_rel
          (#max_arity:nat)
          #n
          (post:VSig.vale_post_tl n [])
          (code:V.va_code)
          (args:IX64.arg_list)
   : IX64.prediction_post_rel_t code n args
   = fun (h0:mem_roots args)
       (_s0:TS.traceState)
       (_push_h0:mem_roots args)
       (_alloc_push_h0:mem_roots args)
       (_sb:IX64.stack_buffer n)
       (rax_fuel_mem:(UInt64.t & nat & ME.mem))
       (s1:TS.traceState) ->
    let rax, fuel, mem = rax_fuel_mem in
    exists h1_pre_pop.
      h1_pre_pop == hs_of_mem (as_mem mem) /\
      HS.poppable h1_pre_pop /\ (
      exists h1. h1 == HS.pop h1_pre_pop /\
        mem_roots_p h1 args /\
        LSig.(to_low_post post args h0 rax h1))

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
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          (#regs_modified:MS.reg -> bool)
          (#xmms_modified:MS.xmm -> bool)          
          (#n:IX64.max_slots)
          (code:V.va_code)
          (args:IX64.arg_list)
          (pre:VSig.vale_pre_tl n [])
          (post:VSig.vale_post_tl n [])
          (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
   : IX64.prediction
             max_arity
             arg_reg
             regs_modified
             xmms_modified
             I.down_mem
             (coerce code)
             n
             args
             (prediction_pre_rel #max_arity #arg_reg pre (coerce code) args)
             (prediction_post_rel #max_arity post (coerce code) args)

let vale_lemma_as_prediction
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          (#regs_modified:MS.reg -> bool)
          (#xmms_modified:MS.xmm -> bool)
          (#n:IX64.max_slots)
          (code:V.va_code)
          (args:IX64.arg_list)
          (pre:VSig.vale_pre_tl n [])
          (post:VSig.vale_post_tl n [])
          (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
   = fun h0 s0 push_h0 alloc_push_h0 sb ->
       let c_code : TS.tainted_code = coerce code in
       let s_args = arg_of_sb sb :: args in
       let va_s0 = LSig.create_initial_vale_state #max_arity #arg_reg args alloc_push_h0 sb in
       core_create_lemma #max_arity #arg_reg args alloc_push_h0 sb;
       assert (SL.state_to_S va_s0 == s0);
       B.fresh_frame_modifies h0 push_h0;
       assert (B.modifies B.loc_none h0 alloc_push_h0);
       assert (LSig.mem_correspondence args alloc_push_h0 va_s0);
       frame_mem_correspondence_back args h0 alloc_push_h0 va_s0 B.loc_none;
       assert (LSig.mem_correspondence args h0 va_s0);
       assert (va_s0.VS.ok);
       assert (LSig.vale_pre_hyp #max_arity #arg_reg args sb va_s0);
       assert (elim_nil pre va_s0 sb);
       let va_s1, f = VSig.elim_vale_sig_nil v va_s0 sb in
       assert (V.eval_code code va_s0 f va_s1);
       eval_code_rel (c_code) va_s0 va_s1 f;
       let Some s1 = TS.taint_eval_code (c_code) (coerce f) s0 in
       assert (VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1));
       assert (VSig.vale_calling_conventions va_s0 va_s1 regs_modified xmms_modified);
       assert (IX64.calling_conventions s0 s1 regs_modified xmms_modified);
       assert (ME.modifies (VSig.mloc_modified_args s_args) va_s0.VS.mem va_s1.VS.mem);
       let final_mem = va_s1.VS.mem in
       let h1_pre_pop = hs_of_mem (as_mem final_mem) in
       Vale.AsLowStar.MemoryHelpers.relate_modifies s_args va_s0.VS.mem va_s1.VS.mem;
       assert (B.modifies (loc_modified_args s_args) alloc_push_h0 h1_pre_pop);
       Vale.AsLowStar.MemoryHelpers.modifies_equal_domains
         (VSig.mloc_modified_args s_args) va_s0.VS.mem final_mem;       
       Vale.AsLowStar.MemoryHelpers.modifies_same_roots 
         (VSig.mloc_modified_args s_args) va_s0.VS.mem final_mem;
       Vale.AsLowStar.MemoryHelpers.state_eq_down_mem va_s1 s1;
       assert (I.down_mem (as_mem final_mem) == s1.TS.state.BS.mem);
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
       assert (LSig.(to_low_post post args h0 (IX64.return_val s1) h2));
       IX64.return_val s1, coerce f, as_mem va_s1.VS.mem

[@__reduce__]
let rec lowstar_typ
          (#max_arity:nat)
          (#arg_reg:IX64.arg_reg_relation max_arity)
          #n
          (#dom:list td)
          (code:V.va_code)
          (args:IX64.arg_list{List.length args + List.length dom <= 20})
          (pre:VSig.vale_pre_tl n dom)
          (post:VSig.vale_post_tl n dom)
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
        #n
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
             (#regs_modified:MS.reg -> bool)
             (#xmms_modified:MS.xmm -> bool)
             #n (#dom:list td)
             (code:V.va_code)
             (args:list arg{List.length dom + List.length args <= 20})
             (num_stack_slots:nat)
             (pre:VSig.vale_pre_tl n dom)
             (post:VSig.vale_post_tl n dom)
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
             vale_lemma_as_prediction _ _ _ _ v in
           let rax, _ = IX64.wrap_variadic (coerce code) max_arity arg_reg regs_modified xmms_modified I.down_mem n args prediction in
           rax
      in
      f <: lowstar_typ #max_arity #arg_reg #n #[] code args pre post
    | hd::tl ->
      fun (x:td_as_type hd) ->
        __test__wrap
          #max_arity 
          #arg_reg
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
      (#max_arity:nat)
      (#arg_reg:IX64.arg_reg_relation max_arity)
      (#n:_)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= 20})
      (pre:VSig.vale_pre_tl n dom)
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
      (#n:_)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{List.length dom + List.length args <= 20})
      (post:VSig.vale_post_tl n dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_post_rel_t (coerce code) n)
   = match dom with
     | [] ->
       prediction_post_rel #max_arity post (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       post_rel_generic #max_arity code tl IX64.(x ++ args) (elim_1 post x)

let rec mk_prediction
       (#max_arity:nat)
       (#arg_reg:IX64.arg_reg_relation max_arity)
       (#regs_modified:MS.reg -> bool)
       (#xmms_modified:MS.xmm -> bool)
       #n
       (code:V.va_code)
       (dom:list td)
       (args:list arg{List.length dom + List.length args <= 20})
       (#pre:VSig.vale_pre_tl n dom)
       (#post:VSig.vale_post_tl n dom)
       (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
   :  IX64.prediction_t
          max_arity
          arg_reg
          regs_modified
          xmms_modified
          I.down_mem
          (coerce code)
          n
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
