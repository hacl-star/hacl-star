module Crypto.AEAD

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// Implements agile, conditionally secure Authenticated Encryption
// with Associated Data (AEAD) for TLS 1.2 and 1.3, given secure, 
// agile PRF cipher and UF-1CMA MAC. 

// For the security proof, we maintain a stateful invariant that
// precisely relates the contents of the AEAD log to the states of the
// PRF and the MACs.

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant
(* open Crypto.AEAD.Wrappers *)
open FStar.HyperStack.ST

module HS       = FStar.HyperStack
module MAC      = Crypto.Symmetric.MAC
module CMA      = Crypto.Symmetric.UF1CMA
module Plain    = Crypto.Plain
module Cipher   = Crypto.Symmetric.Cipher
module PRF      = Crypto.Symmetric.PRF
module Enxor    = Crypto.AEAD.EnxorDexor
module Dexor    = Crypto.AEAD.EnxorDexor
module PRF_MAC  = Crypto.AEAD.Wrappers.PRF
module Encoding = Crypto.AEAD.Encoding   

(* Key management *)

val gen: 
  i:id -> 
  rgn:eternal_region -> 
  ST (aead_state i Writer)
     (requires (fun _ -> True))
     (ensures  (fun h0 st h1 -> True))

(** ref_as_aead_log: A coercion from a conditional log to the ideal case *)
private
let ref_as_aead_log (#r:rgn) (#i:id) (x:rref r (aead_entries i){safeMac i})
  : aead_log r i
  = x

#set-options "--z3rlimit 50"
let gen i rgn = 
  let prf = PRF.gen rgn i in 
  if Flag.prf i then recall (PRF.itable i prf);
  let log : aead_log rgn i =
    if safeMac i 
    then ref_as_aead_log (ralloc rgn Seq.createEmpty)
    else () in
  let ak = if CMA.skeyed i then CMA.mk_akey (PRF.prf_sk0 #i prf) else CMA.mk_akey_null () in 
  AEADState #i #Writer #rgn log prf ak
#reset-options

val coerce: 
    i:id{~(prf i)} -> 
    rgn:eternal_region -> 
    key:lbuffer (v (PRF.keylen i)) -> 
    ST (aead_state i Writer)
       (requires (fun h -> Buffer.live h key))
       (ensures  (fun h0 st h1 -> True))
let coerce i rgn key = 
  let prf = PRF.coerce rgn i key in
  if Flag.prf i then recall (PRF.itable i prf);
  let log : aead_log rgn i = () in
  let ak = if CMA.skeyed i then CMA.mk_akey (PRF.prf_sk0 #i prf) else CMA.mk_akey_null () in 
  AEADState #i #Writer #rgn log prf ak

val genReader: #i:id -> st:aead_state i Writer -> ST (aead_state i Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let genReader #i st =
  AEADState #i #Reader #st.log_region st.log st.prf st.ak

val leak: #i:id{~(prf i)} -> st:aead_state i Writer -> ST (lbuffer (v (PRF.statelen i)))
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let leak #i st = PRF.leak st.prf

include Crypto.AEAD.Encrypt
include Crypto.AEAD.Decrypt
//17-02-14 shall we provide a more abstract API, 
//17-02-14 e.g. make inv opaque
