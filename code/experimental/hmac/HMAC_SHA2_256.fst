module HMAC_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.UInt32

module Buffer = FStar.Buffer
module MAC    = Hacl.HMAC.SHA2.L256


(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t

let suint8_t  = Hacl.UInt8.t
let suint32_t = Hacl.UInt32.t
let suint64_t = Hacl.UInt64.t

let suint32_p = Buffer.buffer suint32_t
let suint8_p  = Buffer.buffer suint8_t



//
// HMAC
//

inline_for_extraction let hashsize_256 = MAC.hashsize
inline_for_extraction let blocksize_256 = MAC.blocksize
inline_for_extraction let size_state_256 = MAC.size_state


val hmac_sha2_init_256:
  state :suint32_p{length state = v size_state_256} ->
  key   :suint8_p ->
  len   :uint32_t {v len = length key} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 key))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let hmac_sha2_init_256 state key len = MAC.init state key len



val hmac_sha2_update_256 :
  state :suint32_p{length state = v size_state_256} ->
  data  :suint8_p {length data = v blocksize_256} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let hmac_sha2_update_256 state data = MAC.update state data



val hmac_sha2_update_multi_256:
  state :suint32_p{length state = v size_state_256} ->
  data  :suint8_p ->
  n     :uint32_t{v n * v blocksize_256 <= length data} ->
  idx   :uint32_t{v idx <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let hmac_sha2_update_multi_256 state data n idx = MAC.update_multi state data n idx



val hmac_sha2_update_last_256:
  state :suint32_p{length state = v size_state_256} ->
  data  :suint8_p {length data <= v blocksize_256} ->
  len   :uint32_t {v len = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let hmac_sha2_update_last_256 state data len = MAC.update_last state data len



val hmac_sha2_finish_256:
  state :suint32_p{length state = v size_state_256} ->
  mac   :suint8_p {length mac = v hashsize_256} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 mac))
        (ensures  (fun h0 _ h1 -> live h1 state /\ live h1 mac /\ modifies_2 state mac h0 h1))

let hmac_sha2_finish_256 state mac = MAC.finish state mac



val hmac_sha2_256:
  mac     :suint8_p{length mac = v hashsize_256} ->
  key     :suint8_p ->
  keylen  :uint32_t{v keylen = length key} ->
  data    :suint8_p ->
  datalen :uint32_t{v datalen = length data /\ v datalen + v blocksize_256 <= pow2 32} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data ))
        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_sha2_256 mac key keylen data datalen = MAC.hmac mac key keylen data datalen
