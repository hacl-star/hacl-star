module Crypto.AEAD.MAC_Wrapper.Invariant

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.AEAD.Encoding 
open Crypto.Symmetric.PRF

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC    = Crypto.Symmetric.MAC
module CMA    = Crypto.Symmetric.UF1CMA
module Cipher = Crypto.Symmetric.Cipher
module PRF    = Crypto.Symmetric.PRF
module Plain  = Crypto.Plain

open Crypto.AEAD.Invariant
open Crypto.AEAD.Encrypt.Invariant

#set-options "--initial_ifuel 0 --max_ifuel 0"

(*
 * framing of aead_entries_are_refined by mac_wrapper
 * the proof relies on nonce being different from all the nonces in the aead table, and hence,
 * the mac still being set (mac_wrapper only modifies the mac log for nonce)
 * otp entries are trivial, since table0 = table1
 *)
private val frame_aead_entries_are_refined_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (safeId i ==>
             (let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
	      let table_0 = HS.sel h0 (itable i aead_st.prf) in
	      let entries_1 = HS.sel h1 (st_ilog aead_st) in
	      let table_1 = HS.sel h1 (itable i aead_st.prf) in
	      entries_0 == entries_1 /\
	      table_0 == table_1 /\
	      aead_entries_are_refined table_0 entries_0 h1)))
#set-options "--z3rlimit 150" //17-02-14 doubled
let frame_aead_entries_are_refined_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 =
  let open FStar.Seq in
  let open FStar.Classical in
  if safeId i then begin
    let entries_0 = HS.sel h0 (st_ilog aead_st) in
    let table_0 = HS.sel h0 (itable i aead_st.prf) in
    let entries_1 = HS.sel h1 (st_ilog aead_st) in
    let table_1 = HS.sel h1 (itable i aead_st.prf) in
    assert (entries_0 == entries_1);
    assert (table_0 == table_1);
    assert (aead_entries_are_refined table_0 entries_0 h0);
    assert (HS.modifies_ref aead_st.prf.mac_rgn (Set.singleton (HS.as_addr (as_hsref (CMA.(ilog mac_st.log))))) h0 h1);
    let h1: (h:HS.mem{safeId i}) = h1 in
    let aux (e:aead_entry i) : Lemma
    	(requires (entries_1 `contains` e))
  	(ensures (refines_one_entry table_1 e h1)) =
      let dom_0 = {iv=e.nonce; ctr=PRF.ctr_0 i} in
      match PRF.find_mac table_1 dom_0 with
      | Some mac_st_e ->
        //nonce of all the aead entries is different from nonce
  	lemma_fresh_nonce_implies_all_entries_nonces_are_different entries_1 nonce;
	//and hence we can apply framing to get that the mac log for all the aead entries remains unchaged
	lemma_mac_log_framing mac_st h0 h1 mac_st_e;
	()
    in
    forall_intro (move_requires aux)
  end

(*
 * framing of unused_aead_id_for_prf by mac_wrapper for nonce' <> nonce
 * since table0 = table1, none_above is straightforward
 * if mac entry does not exist in the prf table, then we are done
 * else we rely on lemma_mac_log_framing to establish that mac log for nonce' is not modified by mac_wrapper
 *)
private val frame_unused_aead_id_for_prf_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw{safeMac i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem)
  (nonce':Cipher.iv (alg i)) : Lemma
  (requires (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             mac_wrapper_h0_h1 aead_st nonce aad plain ct mac_st h0 h1 /\
             unused_aead_iv_for_prf table_0 nonce' h0 /\
	     nonce <> nonce'))
  (ensures  (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_0 nonce' h1))
#reset-options "--z3rlimit 300 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_unused_aead_id_for_prf_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain ct mac_st h0 h1 nonce' =
   let dom_0 = {iv=nonce'; ctr=PRF.ctr_0 i} in
   let prf_table = HS.sel h0 (itable i aead_st.prf) in
   assert (none_above (PRF.incr i dom_0) prf_table);
   (match PRF.find_mac prf_table dom_0 with
    | None           -> ()
    | Some mac_range -> 
      assert (CMA.mac_is_unset (i, nonce') aead_st.prf.mac_rgn mac_range h0);
      MAC.frame_norm h0 h1 CMA.(mac_range.r);
      lemma_mac_log_framing mac_st h0 h1 mac_range)

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"      
private val frame_unused_aead_id_for_prf_mac_wrapper_forall
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw{safeMac i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:ctagbuf plainlen)
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             forall (nonce':Cipher.iv (alg i)). (nonce' <> nonce /\ unused_aead_iv_for_prf table_0 nonce' h0) ==>
	                                   unused_aead_iv_for_prf table_0 nonce' h1))
let frame_unused_aead_id_for_prf_mac_wrapper_forall #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 =
  let open FStar.Classical in
  forall_intro (move_requires (frame_unused_aead_id_for_prf_mac_wrapper aead_st nonce aad plain cipher_tagged mac_st h0 h1))

(*
 * mac_wrapper does not modify the aead log and the prf table
 *)
private val frame_entries_and_table_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32) 
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:ctagbuf plainlen)
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (safeMac i ==>
             (let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
              let entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	      let table_0 = HS.sel h0 (itable i aead_st.prf) in
	      let table_1 = HS.sel h1 (itable i aead_st.prf) in
	      entries_0 == entries_1 /\ table_0 == table_1)))
let frame_entries_and_table_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 = 
  frame_aead_entries_are_refined_mac_wrapper aead_st nonce aad plain cipher_tagged mac_st h0 h1
module CMAWrapper = Crypto.AEAD.Wrappers.CMA
private val frame_prf_table_mac_modifies
  (#i:id)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (st:aead_state i Writer{prf i})
  (n:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (ak:CMA.state (i, n))
  (acc:CMA.accBuffer (i, n))
  (h0 h1:mem) : Lemma 
  (requires ( let tag = Buffer.sub ct plainlen MAC.taglen in	
              enc_dec_separation st aad plain ct  /\
              enc_dec_liveness st aad plain ct h0 /\
              aead_liveness st h0 /\
              HS.(is_stack_region h0.tip) /\
              Buffer.frameOf (MAC.as_buffer (CMA.abuf acc)) = HS.(h0.tip) /\
              CMA.(ak.region = PRF.(st.prf.mac_rgn)) /\
              CMAWrapper.mac_modifies i n tag ak acc h0 h1))
  (ensures (let blocks_0 : prf_table st.prf.mac_rgn i = HS.sel h0 (itable i st.prf) in
            let blocks_1 : prf_table st.prf.mac_rgn i = HS.sel h1 (itable i st.prf) in
            blocks_0 == blocks_1))
#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 3 --max_ifuel 3"      
let frame_prf_table_mac_modifies #i #aadlen #plainlen st n aad plain ct ak acc h0 h1 =
  let table = itable i st.prf in
  let abuf = MAC.as_buffer (CMA.abuf acc) in
  let tag = Buffer.sub ct plainlen MAC.taglen in	
  assert (HS.contains h0 table);
  assert (HH.disjoint (HS.frameOf table) (Buffer.frameOf abuf));
  assert (HH.disjoint (HS.frameOf table) (Buffer.frameOf tag));  
  if safeMac i
  then let log = FStar.Monotonic.RRef.as_hsref CMA.(ilog ak.log) in
       let _ = assert (HH.extends (HS.frameOf log) (HS.frameOf table)) in
       assert (HS.modifies (Set.as_set [Buffer.frameOf abuf; Buffer.frameOf tag; HS.frameOf log]) h0 h1)
  else assert (HS.modifies (Set.as_set [Buffer.frameOf abuf; Buffer.frameOf tag]) h0 h1)

//17-02-14  brittle proof
#reset-options "--z3rlimit 600 --initial_fuel 0 --max_fuel 2 --initial_ifuel 0 --max_ifuel 2"      
(*
 * mac_wrapper does not modify the plain text buffer and the ciphertext part of the ciphertext buffer
 *)
private let frame_plain_and_cipher
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain ct mac_st h0 h1))
  (ensures (mac_wrapper_h0_h1 aead_st nonce aad plain ct mac_st h0 h1 /\
	   (safeMac i ==> 
	       Plain.sel_plain h0 plainlen plain == Plain.sel_plain h1 plainlen plain /\
	       Buffer.as_seq h0 (cbuf ct) == Buffer.as_seq h1 (cbuf ct)))) = ()



val mac_modifies_preserves_norm_keys
  (#i:id)
  (#j:CMA.id)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (st:aead_state i Writer)
  (n:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (ak:CMA.state (i, n))
  (acc:CMA.accBuffer (i, n))
  (h0 h1:mem)
  (r:MAC.elemB j) : Lemma 
  (requires ( let tag = Buffer.sub ct plainlen MAC.taglen in	
              let b = MAC.as_buffer r in
              enc_dec_separation st aad plain ct  /\
              enc_dec_liveness st aad plain ct h0 /\
              HS.(is_stack_region h0.tip) /\
              Buffer.frameOf (MAC.as_buffer (CMA.abuf acc)) = HS.(h0.tip) /\
              CMA.(ak.region = PRF.(st.prf.mac_rgn)) /\
              CMAWrapper.mac_modifies i n tag ak acc h0 h1 /\
              Buffer.frameOf b = PRF.(st.prf.mac_rgn) /\
              fst j == i /\
              MAC.norm_r h0 r))
  (ensures (MAC.norm_r h1 r))
#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"
let mac_modifies_preserves_norm_keys #i #j #aadlen #plainlen st n aad plain ct ak acc h0 h1 r =
  let open CMA in
  let tag = Buffer.sub ct plainlen MAC.taglen in	
  let abuf = MAC.as_buffer (abuf acc) in
  let b = MAC.reveal_elemB r in
  assert (Buffer.disjoint b tag);
  assert (Buffer.disjoint b abuf);
  let _ =
    if safeMac i then assume (Buffer.disjoint_ref_1 b (FStar.Monotonic.RRef.as_hsref (CMA.(ilog ak.log)))) else ()
  in
  match macAlg_of_id i with
  | POLY1305 -> 
    assert (Buffer.live h1 b);
    assert (MAC.norm_r h1 r)
  | GHASH -> 
    assert (MAC.norm_r h1 r)

val mac_preserves_prf_inv
  (#i:id)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (st:aead_state i Writer)
  (n:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (ak:CMA.state (i, n))
  (acc:CMA.accBuffer (i, n))
  (h0 h1:mem) : Lemma 
  (requires ( let tag = Buffer.sub ct plainlen MAC.taglen in	
              enc_dec_separation st aad plain ct  /\
              enc_dec_liveness st aad plain ct h0 /\
              aead_liveness st h0 /\
              HS.(is_stack_region h0.tip) /\
              Buffer.frameOf (MAC.as_buffer (CMA.abuf acc)) = HS.(h0.tip) /\
              CMA.(ak.region = PRF.(st.prf.mac_rgn)) /\
              CMAWrapper.mac_modifies i n tag ak acc h0 h1 /\
              (prf i ==> (
                let blocks : prf_table st.prf.mac_rgn i = HS.sel h0 (itable i st.prf) in
                prf_mac_inv blocks h0))))
  (ensures (prf i ==>  (
                let blocks : prf_table st.prf.mac_rgn i = HS.sel h1 (itable i st.prf) in
                prf_mac_inv #i #st.prf.mac_rgn blocks h1)))
let mac_preserves_prf_inv #i #aadlen #plainlen st n aad plain ct ak acc h0 h1 =
  let open CMA in
  if prf i then begin
    let table = itable i st.prf in
    let blocks_0 : prf_table st.prf.mac_rgn i = HS.sel h0 table in
    let blocks_1 : prf_table st.prf.mac_rgn i = HS.sel h1 table in
    frame_prf_table_mac_modifies st n aad plain ct ak acc h0 h1;
    assert (blocks_0 == blocks_1);
    let h1 : (h:mem{prf i}) = h1 in
    let aux (x:domain_mac i) : Lemma (PRF.prf_mac_inv blocks_1 x h1) =
        match PRF.find_mac blocks_1 x with 
        | None -> ()
        | Some mc -> mac_modifies_preserves_norm_keys st n aad plain ct ak acc h0 h1 mc.r
    in
    FStar.Classical.forall_intro aux
  end

(*
 * propagating the invariant across mac_wrapper
 *)
val lemma_propagate_inv_mac_wrapper
  (#i:id)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i Writer)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (mac_st:CMA.state (i, nonce))
  (acc:CMA.accBuffer (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (let tag = Buffer.sub ct plainlen MAC.taglen in	
             CMAWrapper.mac_modifies i nonce tag mac_st acc h0 h1 /\
             Buffer.frameOf (MAC.as_buffer (CMA.abuf acc)) = HS.(h0.tip) /\
             mac_wrapper_h0_h1 aead_st nonce aad plain ct mac_st h0 h1))
  (ensures  (enxor_and_maybe_mac true aead_st nonce aad plain ct h1))
let lemma_propagate_inv_mac_wrapper #i #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st acc h0 h1 =
  let open FStar.Classical in 
  mac_preserves_prf_inv aead_st nonce aad plain cipher_tagged mac_st acc h0 h1;
  if safeMac i 
  then begin 
    frame_plain_and_cipher                          aead_st nonce aad plain cipher_tagged mac_st h0 h1;
    frame_entries_and_table_mac_wrapper             aead_st nonce aad plain cipher_tagged mac_st h0 h1;
    frame_aead_entries_are_refined_mac_wrapper      aead_st nonce aad plain cipher_tagged mac_st h0 h1;
    frame_unused_aead_id_for_prf_mac_wrapper_forall aead_st nonce aad plain cipher_tagged mac_st h0 h1
  end
