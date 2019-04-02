module GCMdecrypt_stdcalls

open Vale.Stdcalls.GCMdecrypt
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
module V = X64.Vale.Decls
open Gcm_simplify
open GCM_helpers

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma (n * 1 == n) = ()

let gcm128_decrypt key cipher_b cipher_num auth_b auth_num iv_b out_b tag_b keys_b =
  let h0 = get() in
  bytes_to_quad_size_no_extra_bytes (UInt64.v cipher_num);
  bytes_to_quad_size_no_extra_bytes (UInt64.v auth_num);

  FStar.Math.Lemmas.lemma_div_mod (UInt64.v cipher_num) 16;
  FStar.Math.Lemmas.lemma_div_mod (UInt64.v auth_num) 16;

  DV.length_eq (get_downview cipher_b);
  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview tag_b);
  DV.length_eq (get_downview keys_b); 

  math_aux (B.length cipher_b);
  math_aux (B.length auth_b);
  math_aux (B.length iv_b);
  math_aux (B.length keys_b);
  
  as_vale_buffer_len #TUInt8 #TUInt128 cipher_b;
  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 cipher_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out_b);

  let x, _ = gcm128_decrypt key cipher_b cipher_num auth_b auth_num iv_b keys_b out_b tag_b () in

  let h1 = get() in

  gcm_simplify1 cipher_b h0 (UInt64.v cipher_num);
  gcm_simplify1 auth_b h0 (UInt64.v auth_num);
  gcm_simplify1 out_b h1 (UInt64.v cipher_num);
  gcm_simplify2 tag_b h0;
  gcm_simplify3 iv_b h0;

  x


let gcm256_decrypt key cipher_b cipher_num auth_b auth_num iv_b out_b tag_b keys_b =
  let h0 = get() in
  bytes_to_quad_size_no_extra_bytes (UInt64.v cipher_num);
  bytes_to_quad_size_no_extra_bytes (UInt64.v auth_num);

  FStar.Math.Lemmas.lemma_div_mod (UInt64.v cipher_num) 16;
  FStar.Math.Lemmas.lemma_div_mod (UInt64.v auth_num) 16;

  DV.length_eq (get_downview cipher_b);
  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview tag_b);
  DV.length_eq (get_downview keys_b); 

  math_aux (B.length cipher_b);
  math_aux (B.length auth_b);
  math_aux (B.length iv_b);
  math_aux (B.length keys_b);

  as_vale_buffer_len #TUInt8 #TUInt128 cipher_b;
  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 cipher_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out_b);
  
  let x, _ = gcm256_decrypt key cipher_b cipher_num auth_b auth_num iv_b keys_b out_b tag_b () in

  let h1 = get() in

  gcm_simplify1 cipher_b h0 (UInt64.v cipher_num);
  gcm_simplify1 auth_b h0 (UInt64.v auth_num);
  gcm_simplify1 out_b h1 (UInt64.v cipher_num);
  gcm_simplify2 tag_b h0;
  gcm_simplify3 iv_b h0;

  x
