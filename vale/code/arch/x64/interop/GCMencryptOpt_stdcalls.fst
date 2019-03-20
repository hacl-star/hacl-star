module GCMencryptOpt_stdcalls

open Vale.Stdcalls.GCMencryptOpt 
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
module V = X64.Vale.Decls
open Gcm_simplify
open GCM_helpers
open FStar.Calc

#set-options "--z3rlimit 400 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma (n * 1 == n) = ()

let gcm128_encrypt key auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
  in128x6_b out128x6_b len128x6 in128_b out128_b len128_num inout_b plain_num scratch_b tag_b =
  
  let h0 = get() in

  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview keys_b); 
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview hkeys_b); 
  DV.length_eq (get_downview abytes_b);
  DV.length_eq (get_downview in128x6_b);
  DV.length_eq (get_downview out128x6_b);
  DV.length_eq (get_downview in128_b);
  DV.length_eq (get_downview out128_b);
  DV.length_eq (get_downview inout_b);
  DV.length_eq (get_downview scratch_b);
  DV.length_eq (get_downview tag_b);

  math_aux (B.length auth_b);
  math_aux (B.length keys_b);
  math_aux (B.length iv_b);
  math_aux (B.length hkeys_b);
  math_aux (B.length in128x6_b);
  math_aux (B.length scratch_b);
  math_aux (B.length out128_b);
  FStar.Math.Lemmas.cancel_mul_mod (UInt64.v auth_num) 16;
  assert_norm (176 % 16 = 0);
  assert_norm (16 % 16 = 0);
  assert_norm (160 % 16 = 0);
  assert_norm (128 % 16 = 0);
  FStar.Math.Lemmas.cancel_mul_mod (UInt64.v len128x6) 16;
  FStar.Math.Lemmas.cancel_mul_mod (UInt64.v len128_num) 16;

  calc (<=) {
    256 * ((16 * UInt64.v len128_num) / 16);
    (==) {  FStar.Math.Lemmas.cancel_mul_div (UInt64.v len128_num) 16 }
    256 * (UInt64.v len128_num);
    ( <= ) { assert_norm (256 <= 4096); FStar.Math.Lemmas.lemma_mult_le_right (UInt64.v len128_num) 256 4096 }
    4096 * (UInt64.v len128_num);
  };

  assert (DV.length (get_downview tag_b) % 16 = 0);
  assert (DV.length (get_downview scratch_b) % 16 = 0);
  assert (DV.length (get_downview out128_b) % 16 = 0);

  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 hkeys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 abytes_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out128x6_b;
  as_vale_buffer_len #TUInt8 #TUInt128 in128x6_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out128x6_b;
  as_vale_buffer_len #TUInt8 #TUInt128 in128_b;
  as_vale_buffer_len #TUInt8 #TUInt128 inout_b;
  as_vale_buffer_len #TUInt8 #TUInt128 scratch_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in128x6_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out128x6_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in128_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out128_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 inout_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 iv_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 keys_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 hkeys_b);  

  let x, _ = gcm128_encrypt  key auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
  in128x6_b out128x6_b len128x6 in128_b out128_b len128_num inout_b plain_num scratch_b tag_b () in

  let h1 = get() in
  ()
  // gcm_simplify1 plain_b h0 (UInt64.v plain_num);
  // gcm_simplify1 auth_b h0 (UInt64.v auth_num);
  // gcm_simplify1 out_b h1 (UInt64.v plain_num);
  // gcm_simplify2 tag_b h1;
  // gcm_simplify3 iv_b h0

