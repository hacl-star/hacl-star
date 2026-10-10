module Vale.Wrapper.X64.GCM.Helpers

open FStar.Mul
open Vale.Interop.Base
open Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters

module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
module V = Vale.X64.Decls
module ME = Vale.X64.Memory

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let stdcall_constants () : Lemma
  (Vale.Interop.X64.max_stdcall == (if Vale.Interop.Assumptions.win then 4 else 6) /\
   FStar.List.Tot.length ([] <: list Vale.Interop.Base.arg) == 0) =
  assert_norm (Vale.Interop.X64.max_stdcall ==
    (if Vale.Interop.Assumptions.win then 4 else 6));
  assert_norm (FStar.List.Tot.length ([] <: list Vale.Interop.Base.arg) == 0)

private let block_length_bound (n:nat) : Lemma
  (256 * ((16 * n) / 16) <= 4096 * n) =
  FStar.Math.Lemmas.cancel_mul_div n 16;
  FStar.Math.Lemmas.lemma_mult_le_right n 256 4096

unfold let buffer_prepared (b:buf_t TUInt8 TUInt128) (n:nat) : GTot Type0 =
    DV.length (get_downview b) == B.length b /\
    B.length b * 1 == B.length b /\
    DV.length (get_downview b) % 16 == 0 /\
    V.buffer_length (as_vale_buffer #TUInt8 #TUInt128 b) == n /\
    ME.buffer_writeable (as_vale_buffer #TUInt8 #TUInt128 b) /\
    (forall (vh:ME.vale_heap) (vb:ME.buffer TUInt128).
      {:pattern ME.buffer_addr #TUInt128 vb vh}
      vb == as_vale_buffer #TUInt8 #TUInt128 b ==>
      ME.buffer_addr #TUInt128 vb vh + DV.length (get_downview b) < Vale.Def.Words_s.pow2_64)

private let prepare_buffer (h:HS.mem) (b:B.buffer UInt8.t) (n:nat) : Lemma
  (requires B.live h b /\ B.length b == 16 * n)
  (ensures buffer_prepared b n) =
  DV.length_eq (get_downview b);
  FStar.Math.Lemmas.cancel_mul_mod n 16;
  FStar.Math.Lemmas.cancel_mul_div n 16;
  as_vale_buffer_len #TUInt8 #TUInt128 b;
  buffer_writeable_reveal TUInt8 TUInt128 b;
  bounded_buffer_addrs_all TUInt8 TUInt128 h b

let prepare_buffers (key_blocks:nat)
  (h:HS.mem) (auth_b:B.buffer UInt8.t) (auth_num:UInt64.t)
  (keys_b iv_b hkeys_b abytes_b in128x6_b out128x6_b:B.buffer UInt8.t)
  (len128x6:UInt64.t) (in128_b out128_b:B.buffer UInt8.t) (len128_num:UInt64.t)
  (inout_b scratch_b tag_b:B.buffer UInt8.t) : Lemma
  (requires
    B.live h auth_b /\ B.length auth_b == 16 * (UInt64.v auth_num) /\
    B.live h keys_b /\ B.length keys_b == 16 * key_blocks /\
    B.live h iv_b /\ B.length iv_b == 16 * 1 /\
    B.live h hkeys_b /\ B.length hkeys_b == 16 * 8 /\
    B.live h abytes_b /\ B.length abytes_b == 16 * 1 /\
    B.live h in128x6_b /\ B.length in128x6_b == 16 * (UInt64.v len128x6) /\
    B.live h out128x6_b /\ B.length out128x6_b == 16 * (UInt64.v len128x6) /\
    B.live h in128_b /\ B.length in128_b == 16 * (UInt64.v len128_num) /\
    B.live h out128_b /\ B.length out128_b == 16 * (UInt64.v len128_num) /\
    B.live h inout_b /\ B.length inout_b == 16 * 1 /\
    B.live h scratch_b /\ B.length scratch_b == 16 * 9 /\
    B.live h tag_b /\ B.length tag_b == 16 * 1 /\
    B.disjoint iv_b auth_b /\
    B.disjoint iv_b keys_b /\
    B.disjoint iv_b hkeys_b /\
    B.disjoint iv_b abytes_b /\
    B.disjoint iv_b in128x6_b /\
    B.disjoint iv_b out128x6_b /\
    B.disjoint iv_b in128_b /\
    B.disjoint iv_b out128_b /\
    B.disjoint iv_b inout_b /\
    B.disjoint iv_b scratch_b /\
    B.disjoint tag_b iv_b)
  (ensures
    buffer_prepared auth_b (UInt64.v auth_num) /\
    buffer_prepared keys_b key_blocks /\
    buffer_prepared iv_b 1 /\
    buffer_prepared hkeys_b 8 /\
    buffer_prepared abytes_b 1 /\
    buffer_prepared in128x6_b (UInt64.v len128x6) /\
    buffer_prepared out128x6_b (UInt64.v len128x6) /\
    buffer_prepared in128_b (UInt64.v len128_num) /\
    buffer_prepared out128_b (UInt64.v len128_num) /\
    buffer_prepared inout_b 1 /\
    buffer_prepared scratch_b 9 /\
    buffer_prepared tag_b 1 /\
    ~(iv_b === auth_b) /\
    ~(iv_b === keys_b) /\
    ~(iv_b === hkeys_b) /\
    ~(iv_b === abytes_b) /\
    ~(iv_b === in128x6_b) /\
    ~(iv_b === out128x6_b) /\
    ~(iv_b === in128_b) /\
    ~(iv_b === out128_b) /\
    ~(iv_b === inout_b) /\
    ~(iv_b === scratch_b) /\
    ~(iv_b === tag_b) /\
    256 * ((16 * UInt64.v len128_num) / 16) <= 4096 * UInt64.v len128_num) =
  B.disjoint_neq iv_b auth_b;
  B.disjoint_neq iv_b keys_b;
  B.disjoint_neq iv_b hkeys_b;
  B.disjoint_neq iv_b abytes_b;
  B.disjoint_neq iv_b in128x6_b;
  B.disjoint_neq iv_b out128x6_b;
  B.disjoint_neq iv_b in128_b;
  B.disjoint_neq iv_b out128_b;
  B.disjoint_neq iv_b inout_b;
  B.disjoint_neq iv_b scratch_b;
  B.disjoint_neq tag_b iv_b;
  prepare_buffer h auth_b (UInt64.v auth_num);
  prepare_buffer h keys_b key_blocks;
  prepare_buffer h iv_b 1;
  prepare_buffer h hkeys_b 8;
  prepare_buffer h abytes_b 1;
  prepare_buffer h in128x6_b (UInt64.v len128x6);
  prepare_buffer h out128x6_b (UInt64.v len128x6);
  prepare_buffer h in128_b (UInt64.v len128_num);
  prepare_buffer h out128_b (UInt64.v len128_num);
  prepare_buffer h inout_b 1;
  prepare_buffer h scratch_b 9;
  prepare_buffer h tag_b 1;
  block_length_bound (UInt64.v len128_num)
