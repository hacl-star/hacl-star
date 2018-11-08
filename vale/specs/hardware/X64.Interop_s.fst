module X64.Interop_s

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
//open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
//open X64.Vale.State
//open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
//open X64.Vale.StateLemmas
//open X64.Vale.Lemmas
module TS = X64.Taint_Semantics_s
module ME = X64.Memory_s
module BS = X64.Bytes_Semantics_s

friend X64.Memory_s
friend X64.Memory
//friend X64.Vale.Decls
//friend X64.Vale.StateLemmas

let make_h_equals_refine (a:Type) (x:a) (p:a -> Type0) (q:squash (p x)) : h_equals_refine a x (y:a{p y}) x =
  HReflRefine p q

let prove_squash (a:Type) (x:a) : Lemma (squash a) = ()

let to_b8 #bt m =
  let p (b:b8) : Type0 = B.length b % view_n (TBase bt) == 0 in
  let h : h_equals_refine b8 m (y:b8{p y}) m = make_h_equals_refine b8 m p () in //HReflRefine p () in
  prove_squash (h_equals_refine b8 m (ME.buffer (TBase bt)) m) h;
  m

let rec equiv_disjoint_or_eq_l (roots:list b8)
  : Lemma (ensures (disjoint_or_eq_l roots <==> Interop.list_disjoint_or_eq roots))
          [SMTPatOr [[SMTPat (disjoint_or_eq_l roots)];
                     [SMTPat (Interop.list_disjoint_or_eq roots)]]]
  = 
  let rec equiv_disjoint_or_eq_l_aux (b:b8) (tl:list b8) : Lemma
    (disjoint_or_eq_l_aux b tl <==> (forall p. List.memP p tl ==> Interop.disjoint_or_eq b p))
  = match tl with
    | [] -> ()
    | a::q -> equiv_disjoint_or_eq_l_aux b q
  in
  match roots with
    | [] -> ()
    | a::q -> 
      equiv_disjoint_or_eq_l_aux a q;
      equiv_disjoint_or_eq_l q

let rec equiv_live_l (h:HS.mem) (roots:list b8)
  : Lemma (ensures (live_l h roots <==> Interop.list_live h roots))
          [SMTPatOr [[SMTPat (live_l h roots)];
                     [SMTPat (Interop.list_live h roots)]]]
  = match roots with
    | [] -> ()
    | a::q -> equiv_live_l h q

// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let create_initial_trusted_state_core acc regs xmms taint h0 stack =
    let acc = stack::acc in
    let (mem:mem) = {
      addrs = addrs;
      ptrs = acc;
      hs = h0
    } in
    let regs = FunctionalExtensionality.on reg (regs_with_stack regs stack) in
    let xmms = FunctionalExtensionality.on xmm xmms in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = 0;
      BS.mem = Interop.down_mem h0 addrs acc
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = create_valid_memtaint mem acc taint
    },
    mem

let prediction_pre c acc down h0 s0 push_h0 alloc_push_h0 b =
  HS.fresh_frame h0 push_h0 /\
  M.modifies loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  s0 == fst (elim_down_nil acc down alloc_push_h0 b)

let prediction_post c acc down h0 s0 push_h0 alloc_push_h0 b (fuel, final_mem) =
  Some? (TS.taint_eval_code c fuel s0) /\ (
    let sN = Some?.v (TS.taint_eval_code c fuel s0) in
    Interop.down_mem final_mem.hs final_mem.addrs final_mem.ptrs == sN.TS.state.BS.mem /\
    Interop_assumptions.calling_conventions win s0 sN
//    save_reg Rbx s0 sN /\
//    save_reg Rsi s0 sN /\
//    save_reg Rdi s0 sN /\
//    save_reg Rbp s0 sN /\
//    save_reg Rsp s0 sN /\
//    save_reg R12 s0 sN /\
//    save_reg R13 s0 sN /\
//    save_reg R14 s0 sN /\
//    save_reg R15 s0 sN /\
//    // TODO: callee-save for xmms
//    sN.TS.state.BS.ok
  )

let as_lowstar_sig_post c acc down h0 predict push_h0 alloc_push_h0 b fuel final_mem h1 =
  let s0 = fst (elim_down_nil acc down alloc_push_h0 b) in
  HS.fresh_frame h0 push_h0 /\
  M.modifies loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  (fuel, final_mem) == predict s0 push_h0 alloc_push_h0 b /\
  HS.poppable final_mem.hs /\
  h1 == HS.pop (final_mem.hs)

let rec wrap_tl
         (c:code)
         (dom:list vale_type)
         (acc:list b8)
         (down:create_trusted_initial_state_t dom acc)
    : as_lowstar_sig_tl c dom acc down
    = match dom with
      | [] ->
        let f : as_lowstar_sig_tl c [] acc down =
          let ff (h0:HS.mem) (predict:prediction c acc down h0)
            : Stack (as_lowstar_sig_ret acc)
              (requires fun h0' -> h0 == h0' /\ mem_roots_p h0 acc /\ True)
              (ensures fun h0 (As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem) h1 ->
                as_lowstar_sig_post c acc down h0 predict push_h0 alloc_push_h0 b fuel final_mem h1)
            =
            let h0' = get () in
            push_frame ();
            let h1 = get () in
            let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
            let h2 = get () in
            assert (HS.fresh_frame h0 h1);
            assert (mem_roots_p h2 acc);
            assert (mem_roots_p h2 (stack_b::acc));
            let (fuel, final_mem) = st_put (fun h0' -> h0' == h2) (fun h0' ->
              let va_s0, mem_s0 = elim_down_nil acc down h0' stack_b in
              let (fuel, final_mem) = predict va_s0 h1 h2 stack_b in
              assert (B.frameOf stack_b = HS.get_tip h0');
              assert (B.live h0' stack_b);
              let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
              ((fuel, final_mem), final_mem.hs)
            ) in //conveniently, st_put assumes that the shape of the stack did not change
            pop_frame ();
            As_lowstar_sig_ret h1 h2 stack_b fuel final_mem
          in ff
(*
          fun (h0:HS.mem) (predict:prediction c acc down h0) ->
            let h0' = get () in
            push_frame ();
            let h1 = get () in
            let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
            let h2 = get () in
            assert (HS.fresh_frame h0 h1);
            assert (mem_roots_p h2 acc);
            st_put (fun h0' -> h0' == h2) (fun h0' ->
              let va_s0, mem_s0 = elim_down_nil acc down h0' stack_b in
              let (fuel, final_mem) = predict va_s0 h1 h2 stack_b in
              assert (B.frameOf stack_b = HS.get_tip h0');
              assert (B.live h0' stack_b);
              let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
              (), final_mem.hs
            ); //conveniently, st_put assumes that the shape of the stack did not change
            pop_frame ();
            (h1, h2, stack_b)
*)
        in
        f <: as_lowstar_sig_tl c [] acc down

      | hd::tl ->
        let f (x:vale_type_as_type hd)
           : as_lowstar_sig_tl c tl (maybe_cons_buffer hd x acc)
                               (elim_down_cons hd tl acc down x)
           = wrap_tl c tl
                  (maybe_cons_buffer hd x acc)
                  (elim_down_cons hd tl acc down x)
        in
        f


let wrap c dom =
  wrap_tl c dom [] (create_trusted_initial_state win dom)
