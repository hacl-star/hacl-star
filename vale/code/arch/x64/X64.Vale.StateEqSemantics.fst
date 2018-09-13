module X64.Vale.StateEqSemantics

open X64.Machine_s
open X64.Vale.StateLemmas
module BS = X64.Bytes_Semantics_s
module TS = X64.Taint_Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2 --max_ifuel 2 --initial_ifuel 2 --z3rlimit 20"

(* This is a needed assumption *)
assume val eq_all_havoc (ins:BS.ins) (s1 s2:BS.state) : Lemma
  (requires state_eq_BS s1 s2)
  (ensures BS.havoc s1 ins == BS.havoc s2 ins)
  [SMTPat (BS.havoc s1 ins); SMTPat (state_eq_BS s1 s2)]


(* This is wrong with the current semantics *)
(* TODO: Fix it *)

val eval_operand_eq_all (o:operand) (s1 s2:BS.state) : Lemma
  (requires state_eq_BS s1 s2)
  (ensures BS.eval_operand o s1 == BS.eval_operand o s2) 
  [SMTPat (BS.eval_operand o s1); SMTPat (state_eq_BS s1 s2)]

let eval_operand_eq_all o s1 s2 = admit()

val update_operand_preserve_flags_eq_all (o:operand) (v:nat64) (s1 s2:BS.state) : Lemma
  (requires state_eq_BS s1 s2)
  (ensures state_eq_BS
    (BS.update_operand_preserve_flags' o v s1)
    (BS.update_operand_preserve_flags' o v s2)
  )
  [SMTPat (BS.update_operand_preserve_flags' o v s1); SMTPat (state_eq_BS s1 s2)]

let update_operand_preserve_flags_eq_all o v s1 s2 = match o with
  | OMem m -> ()
  | OReg r -> 
    let s1' = BS.update_operand_preserve_flags' o v s1 in
    let s2' = BS.update_operand_preserve_flags' o v s2 in
    assert (FunctionalExtensionality.feq s1'.BS.regs s2'.BS.regs)
  | _ -> ()

val update_operand_eq_all (o:operand) (ins:BS.ins) (v:nat64) (s1 s2:BS.state) : Lemma
  (requires state_eq_BS s1 s2)
  (ensures state_eq_BS
    (BS.update_operand' o ins v s1)
    (BS.update_operand' o ins v s2)
  )
  [SMTPat (BS.update_operand' o ins v s1); SMTPat (state_eq_BS s1 s2)]

let update_operand o ins v s1 s2 = ()


val eval_ins_bs_eq_all (c:BS.ins) (s1 s2:BS.state) : Lemma
  (requires state_eq_BS s1 s2)
  (ensures state_eq_BS (BS.run (BS.eval_ins c) s1) (BS.run (BS.eval_ins c) s2))

let eval_ins_bs_eq_all c s1 s2 = admit() (*
  if BS.Add64? c then (
    let BS.Add64 dst src = c in
    let s1' = BS.run (BS.check (BS.valid_operand src)) s1 in
    let s2' = BS.run (BS.check (BS.valid_operand src)) s2 in
    let s1' = BS.run (BS.check (BS.valid_dst_operand dst)) s1' in
    let s2' = BS.run (BS.check (BS.valid_dst_operand dst)) s2' in
    assert (state_eq_BS s1' s2');
    ()
  ) else admit()
*)

val eq_update_taint_list 
  (memTaint1 memTaint2:memTaint_t)
  (dsts:list operand)
  (t:taint)
  (s1 s2:BS.state) : Lemma
  (requires memTaint1 == memTaint2 /\ state_eq_BS s1 s2)
  (ensures TS.update_taint_list memTaint1 dsts t s1 == TS.update_taint_list memTaint2 dsts t s2)
  (decreases %[dsts])

let rec eq_update_taint_list memTaint1 memTaint2 dsts t s1 s2 = match dsts with
  | [] -> ()
  | a :: q -> eq_update_taint_list
    (TS.update_taint memTaint1 a t s1)
    (TS.update_taint memTaint2 a t s2)
    q t s1 s2

val eq_all_taint_match_list: 
  (srcs:list operand) ->
  (t:taint) ->
  (memTaint1:memTaint_t) ->
  (memTaint2:memTaint_t) ->
  (s1:BS.state) ->
  (s2:BS.state) ->
  Lemma 
    (requires memTaint1 == memTaint2 /\ state_eq_BS s1 s2)
    (ensures TS.taint_match_list srcs t memTaint1 s1 == TS.taint_match_list srcs t memTaint2 s2)

let rec eq_all_taint_match_list srcs t memTaint1 memTaint2 s1 s2 =
  match srcs with
  | [] -> ()
  | a::q -> eq_all_taint_match_list q t memTaint1 memTaint2 s1 s2

val eval_ins_same_memTaint (c:TS.tainted_ins) (s1 s2:TS.traceState) : Lemma
  (requires state_eq_S s1 s2)
  (ensures (TS.taint_eval_ins c s1).TS.memTaint == (TS.taint_eval_ins c s2).TS.memTaint)

let eval_ins_same_memTaint c s1 s2 =
  let i, dsts, srcs = c.TS.ops in
  let t = c.TS.t in
  if BS.Mulx64? i then (
    let s1' = BS.run (BS.check (TS.taint_match_list srcs t s1.TS.memTaint)) s1.TS.state in
    let s2' = BS.run (BS.check (TS.taint_match_list srcs t s2.TS.memTaint)) s2.TS.state in  
    let BS.Mulx64 dst_hi dst_lo src = i in
    eq_all_taint_match_list srcs t s1.TS.memTaint s2.TS.memTaint s1.TS.state s2.TS.state;
    let lo1 = FStar.UInt.mul_mod #64 (BS.eval_reg Rdx s1') (BS.eval_operand src s1') in
    let lo2 = FStar.UInt.mul_mod #64 (BS.eval_reg Rdx s2') (BS.eval_operand src s2') in
    let s1'' = BS.update_operand_preserve_flags' dst_lo lo1 s1' in
    let s2'' = BS.update_operand_preserve_flags' dst_lo lo2 s2' in
    let memTaint1 = TS.update_taint s1.TS.memTaint dst_lo t s1' in
    let memTaint2 = TS.update_taint s2.TS.memTaint dst_lo t s2' in
    let memTaint1 = TS.update_taint memTaint1 dst_hi t s1'' in
    let memTaint2 = TS.update_taint memTaint2 dst_hi t s2'' in
    assert (memTaint1 == memTaint2)
  )
  else if BS.MOVDQU? i then ()
  else if BS.Push? i then ()
  else if BS.Mulx64? i then ()
  else 
    let s1' = BS.run (BS.check (TS.taint_match_list srcs t s1.TS.memTaint)) s1.TS.state in
    let s2' = BS.run (BS.check (TS.taint_match_list srcs t s2.TS.memTaint)) s2.TS.state in
    eq_all_taint_match_list srcs t s1.TS.memTaint s2.TS.memTaint s1.TS.state s2.TS.state;
    eq_update_taint_list s1.TS.memTaint s2.TS.memTaint dsts t s1' s2'

let eval_ins_eq_all c =
  let i, dsts, srcs = c.TS.ops in
  let t = c.TS.t in
  let aux (s1 s2:TS.traceState) : Lemma 
    (requires state_eq_S s1 s2)
    (ensures state_eq_S (TS.taint_eval_ins c s1) (TS.taint_eval_ins c s2)) = 
    eval_ins_same_memTaint c s1 s2;
    if BS.MOVDQU? i then (
      let BS.MOVDQU dst src = i in
      let s1' = BS.run (BS.check (TS.taint_match128 src t s1.TS.memTaint)) s1.TS.state in
      let s2' = BS.run (BS.check (TS.taint_match128 src t s2.TS.memTaint)) s2.TS.state in
      eval_ins_bs_eq_all i s1' s2'
    ) else (
      let s1' = BS.run (BS.check (TS.taint_match_list srcs t s1.TS.memTaint)) s1.TS.state in
      let s2' = BS.run (BS.check (TS.taint_match_list srcs t s2.TS.memTaint)) s2.TS.state in
      eq_all_taint_match_list srcs t s1.TS.memTaint s2.TS.memTaint s1.TS.state s2.TS.state;
      eval_ins_bs_eq_all i s1' s2'
    )
  in
  Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (fun () -> aux s1 s2) ())
