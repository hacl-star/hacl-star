module Vale.Interop.Cast

module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open FStar.HyperStack.ST

open Interop.Base
module IA = Interop.Assumptions
open Vale.AsLowStar.MemoryHelpers
module LSig = Vale.AsLowStar.LowStarSig

open FStar.Mul


let rec ghost_copy_down (#t:base_typ) (b:b_t t) (b8:b_t TUInt8{B.length b8 == B.length b * view_n t /\ B.length b8 % view_n t = 0}) 
  (h0:HS.mem{B.live h0 b /\ B.live h0 b8}) 
  (h_accu:HS.mem{B.live h_accu b /\ B.live h_accu b8 /\ 
    equal_domains h0 h_accu /\
    B.modifies (B.loc_buffer b8) h0 h_accu})
  (n:nat{B.length b == n /\ B.length b8 / view_n t = n})
  (i:nat{i <= n}) : 
  Ghost (x:HS.mem{equal_domains h0 x})
  (requires (forall (j:nat{j < i}). 
    Seq.index (B.as_seq h0 b) j == low_buffer_read t h_accu b8 j))
  (ensures fun h1 ->
    B.live h1 b /\ B.live h1 b8 /\
    B.modifies (B.loc_buffer b8) h0 h1 /\
    (forall (j:nat{j < n}). {:pattern low_buffer_read t h1 b8 j} Seq.index (B.as_seq h0 b) j == low_buffer_read t h1 b8 j))
   (decreases %[n - i])
  =
  if i >= n then h_accu
  else
    let view = LSig.view_of_base_typ t in
    let bv = BV.mk_buffer_view b8 view in
    let v = Seq.index (B.as_seq h0 b) i in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq bv;      
    BV.upd_equal_domains h_accu bv i v;
    BV.upd_modifies h_accu bv i v;
    let h1 = BV.upd h_accu bv i v in
    let aux (j:nat{j <= i}) : Lemma
      (Seq.index (B.as_seq h0 b) j == low_buffer_read t h1 b8 j) =
      BV.sel_upd bv i j v h_accu
    in Classical.forall_intro aux;  
    ghost_copy_down b b8 h0 h1 n (i+1)


let copy_down #t b b8 =
    FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);
    FStar.Math.Lemmas.multiple_modulo_lemma (B.length b) (view_n t);
    IA.st_put 
      (fun h0 -> B.live h0 b /\ B.live h0 b8) 
      (fun h0 -> (), ghost_copy_down b b8 h0 h0 (B.length b) 0)

let rec ghost_imm_copy_down (#t:base_typ) (b:ib_t t) (b8:ib_t TUInt8{B.length b8 == B.length b * view_n t /\ B.length b8 % view_n t = 0}) 
  (h0:HS.mem{B.live h0 b /\ B.live h0 b8}) 
  (h_accu:HS.mem{B.live h_accu b /\ B.live h_accu b8 /\ 
    equal_domains h0 h_accu /\
    B.modifies (B.loc_buffer b8) h0 h_accu})
  (n:nat{B.length b == n /\ B.length b8 / view_n t = n})
  (i:nat{i <= n}) : 
  Ghost (x:HS.mem{equal_domains h0 x})
  (requires (forall (j:nat{j < i}). 
    Seq.index (B.as_seq h0 b) j == imm_low_buffer_read t h_accu b8 j))
  (ensures fun h1 ->
    B.live h1 b /\ B.live h1 b8 /\
    B.modifies (B.loc_buffer b8) h0 h1 /\
    (forall (j:nat{j < n}). {:pattern imm_low_buffer_read t h1 b8 j} Seq.index (B.as_seq h0 b) j == imm_low_buffer_read t h1 b8 j))
   (decreases %[n - i])
  =
  if i >= n then h_accu
  else
    let view = LSig.view_of_base_typ t in
    let bv = BV.mk_buffer_view b8 view in
    let v = Seq.index (B.as_seq h0 b) i in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq bv;      
    BV.upd_equal_domains h_accu bv i v;
    BV.upd_modifies h_accu bv i v;
    let h1 = BV.upd h_accu bv i v in
    let aux (j:nat{j <= i}) : Lemma
      (Seq.index (B.as_seq h0 b) j == imm_low_buffer_read t h1 b8 j) =
      BV.sel_upd bv i j v h_accu
    in Classical.forall_intro aux;  
    ghost_imm_copy_down b b8 h0 h1 n (i+1)

let copy_imm_down #t b b8 =
    FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);
    FStar.Math.Lemmas.multiple_modulo_lemma (B.length b) (view_n t);
    IA.st_put 
      (fun h0 -> B.live h0 b /\ B.live h0 b8) 
      (fun h0 -> (), ghost_imm_copy_down b b8 h0 h0 (B.length b) 0)

let ghost_copy_up (#t:base_typ) (b:b_t t) 
  (b8:b_t TUInt8{B.length b8 == B.length b * view_n t /\ B.length b8 % view_n t = 0})
  (h0:HS.mem{B.live h0 b /\ B.live h0 b8})
  : Ghost (x:HS.mem{equal_domains h0 x})
  (requires True)
  (ensures fun h1 ->
    B.live h1 b /\ B.live h1 b8 /\
    B.modifies (B.loc_buffer b) h0 h1 /\
    (forall (j:nat{j < B.length b}). Seq.index (B.as_seq h1 b) j == low_buffer_read t h0 b8 j)) 
  = let view = LSig.view_of_base_typ t in
    let bv = BV.mk_buffer_view b8 view in
    let s = BV.as_seq h0 bv in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq bv;
    B.g_upd_seq_as_seq b s h0;
    Classical.forall_intro (BV.as_seq_sel h0 bv);
    B.g_upd_seq b s h0

let imm_ghost_copy_up (#t:base_typ) (b:b_t t) 
  (b8:b_t TUInt8{B.length b8 == B.length b * view_n t /\ B.length b8 % view_n t = 0})
  (h0:HS.mem{B.live h0 b /\ B.live h0 b8 /\
    (forall (j:nat{j < B.length b /\ j < B.length b8 / view_n t}). Seq.index (B.as_seq h0 b) j == low_buffer_read t h0 b8 j)})
  : Ghost  (x:HS.mem{equal_domains h0 x})
  (requires True)
  (ensures fun h1 -> h1 == h0)
  = let view = LSig.view_of_base_typ t in
    let bv = BV.mk_buffer_view b8 view in
    let s = BV.as_seq h0 bv in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq bv;
    FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);
    B.g_upd_seq_as_seq b s h0;
    Classical.forall_intro (BV.as_seq_sel h0 bv);
    assert (Seq.equal (B.as_seq h0 b) (BV.as_seq h0 bv));
    B.lemma_g_upd_with_same_seq b h0;
    B.g_upd_seq b s h0


let imm_ghost_imm_copy_up (#t:base_typ) (b:ib_t t) 
  (b8:ib_t TUInt8{B.length b8 == B.length b * view_n t /\ B.length b8 % view_n t = 0})
  (h0:HS.mem{B.live h0 b /\ B.live h0 b8 /\
    (forall (j:nat{j < B.length b /\ j < B.length b8 / view_n t}). Seq.index (B.as_seq h0 b) j == imm_low_buffer_read t h0 b8 j)})
  : Ghost  (x:HS.mem{equal_domains h0 x})
  (requires True)
  (ensures fun h1 -> h1 == h0)
  = let view = LSig.view_of_base_typ t in
    let bv = BV.mk_buffer_view b8 view in
    let s = BV.as_seq h0 bv in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq bv;
    FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);    
    B.g_upd_seq_as_seq b s h0;
    Classical.forall_intro (BV.as_seq_sel h0 bv);
    assert (Seq.equal (B.as_seq h0 b) (BV.as_seq h0 bv));
    B.lemma_g_upd_with_same_seq b h0;
    B.g_upd_seq b s h0

let copy_up #t b b8 = 
  FStar.Math.Lemmas.multiple_modulo_lemma (B.length b) (view_n t);    
  FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);    
  IA.st_put (fun h0 -> B.live h0 b /\ B.live h0 b8) (fun h0 -> (), ghost_copy_up b b8 h0)

let imm_copy_up #t b b8
  = FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);
    IA.st_put 
    (fun h0 -> B.live h0 b /\ B.live h0 b8 /\ 
      (forall (j:nat{j < B.length b}). Seq.index (B.as_seq h0 b) j == low_buffer_read t h0 b8 j))
    (fun h0 -> (), imm_ghost_copy_up b b8 h0)

let imm_copy_imm_up #t b b8
  = FStar.Math.Lemmas.multiple_division_lemma (B.length b) (view_n t);
  IA.st_put 
    (fun h0 -> B.live h0 b /\ B.live h0 b8 /\ 
      (forall (j:nat{j < B.length b}). Seq.index (B.as_seq h0 b) j == imm_low_buffer_read t h0 b8 j))
    (fun h0 -> (), imm_ghost_imm_copy_up b b8 h0)

