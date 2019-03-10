module GCMencrypt_stdcalls

open Vale.Stdcalls.GCMencrypt
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
module V = X64.Vale.Decls

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let gcm128_encrypt key plain_b plain_num auth_b auth_num iv_b out_b tag_b keys_b =
  let h0 = get() in
  DV.length_eq (get_downview plain_b);
  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview tag_b);
  DV.length_eq (get_downview keys_b); 

  as_vale_buffer_len #TUInt8 #TUInt128 plain_b;
  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 plain_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out_b);

  // TODO: Add a condition about length of stack in lowstarsig to prove length stack_b >= 37

  let x, _ = gcm128_encrypt key plain_b plain_num auth_b auth_num iv_b keys_b out_b tag_b () in
  ()
