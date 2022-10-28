module Hacl.Spec.PrecompBaseTable

open FStar.Mul
open Lib.IntTypes

module FL = FStar.List.Tot
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation.Definition
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
class mk_precomp_base_table (t:Type) (a_t:BE.inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  concr_ops: SE.concrete_ops t;
  to_cm: x:BE.to_comm_monoid a_t len ctx_len{x.BE.a_spec == concr_ops.SE.to.SE.a_spec};
  to_list: t -> x:list (uint_t a_t SEC){FL.length x = v len /\ to_cm.BE.linv (Seq.seq_of_list x)};
  lemma_refl: x:t ->
    Lemma (concr_ops.SE.to.SE.refl x == to_cm.BE.refl (Seq.seq_of_list (to_list x)));
}


inline_for_extraction noextract
let g_i_acc_t (t:Type) (a_t:BE.inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) (i:nat) =
  t & acc:list (uint_t a_t SEC){FL.length acc == (i + 1) * v len}

inline_for_extraction noextract
let precomp_base_table_f (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (i:nat) ((g_i,acc): g_i_acc_t t a_t len ctx_len i) : g_i_acc_t t a_t len ctx_len (i + 1) =
  let acc = FL.(acc @ k.to_list g_i) in
  let g_i = k.concr_ops.SE.mul g_i g in
  g_i, acc


let rec precomp_base_table_list_rec
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:nat) (acc:g_i_acc_t t a_t len ctx_len 0) : Tot (g_i_acc_t t a_t len ctx_len n) (decreases n) =

  if n = 0 then acc
  else precomp_base_table_f k g (n - 1) (precomp_base_table_list_rec k g (n - 1) acc)


let precomp_base_table_list (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t) (n:nat) :
  x:list (uint_t a_t SEC){FL.length x = (n + 1) * v len} =
  snd (precomp_base_table_list_rec k g n (g, k.to_list (k.concr_ops.SE.one ())))


let precomp_base_table_lseq (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:nat{(n + 1) * v len <= max_size_t}) : LSeq.lseq (uint_t a_t SEC) ((n + 1) * v len) =
  Seq.seq_of_list (precomp_base_table_list k g n)

//--------------------------------------------

val seq_of_list_append_lemma: #a:Type -> x:list a -> y:list a ->
  Lemma (let xy_lseq = Seq.seq_of_list FL.(x @ y) in
    Seq.slice xy_lseq 0 (FL.length x) == Seq.seq_of_list x /\
    Seq.slice xy_lseq (FL.length x) (FL.length x + FL.length y) == Seq.seq_of_list y)

//--------------------------------------------

let pow_base (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t) (i:nat) : k.concr_ops.SE.to.a_spec =
  LE.pow k.concr_ops.SE.to.comm_monoid (k.concr_ops.SE.to.refl g) i

unfold
let precomp_base_table_acc_inv
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (table_len:nat{table_len * v len <= max_size_t})
  (table:LSeq.lseq (uint_t a_t SEC) (table_len * v len))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right (v len) j table_len;
  Math.Lemmas.lemma_mult_le_right (v len) (j + 1) table_len;
  let bj = LSeq.sub table (j * v len) (v len) in
  k.to_cm.BE.linv bj /\ k.to_cm.BE.refl bj == pow_base k g j


val precomp_base_table_lemma
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (table_len:pos{table_len * v len <= max_size_t})
  (table:LSeq.lseq (uint_t a_t SEC) (table_len * v len)) :
  Lemma (forall (i:nat{i < table_len}).
    precomp_base_table_acc_inv k g table_len (precomp_base_table_lseq k g (table_len - 1)) i)
