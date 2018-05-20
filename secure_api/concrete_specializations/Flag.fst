module Flag
(* These is the concrete version of ideal_flags/Flag.fstar
   It sets all the flags to false to extract only the concrete
   version of the code, without any of the cryptographic idealizations
*)
 
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Crypto.Indexing

// controls idealization of each cipher as a perfect random function
inline_for_extraction
let cipher_prf (c:cipherAlg) = false

// controls existence of logs for all MACs
inline_for_extraction
let mac_log = false

// idealizes each one-time MAC as perfectly INT-1CMA.
inline_for_extraction
let mac_int1cma (m:macAlg) = false

// controls 2nd, perfect idealization step in enxor/dexor for all PRFs.
inline_for_extraction
let prf_cpa = false


(* CONDITIONAL IDEALIZATION *) 

// guarantees fresh record keys (to be defined by TLS Handshake)
inline_for_extraction
let safeHS (i:id) = false

// controls PRF idealization of ciphers (move to PRF?)
inline_for_extraction
let prf (i: id): Tot bool = false

// controls INT1CMA idealization of MACs (move to MAC?)
inline_for_extraction
let mac1 (i:id) : Tot bool = false

// controls abstraction of plaintexts
// (kept abstract, but requires all the crypto steps above)
inline_for_extraction
let safeId (i:id) = false

(* IDEALIZATION DEPENDENCIES *) 

// review usage of these lemmas

let mac1_implies_mac_log (i:id) : Lemma
  (requires (mac1 i))
  (ensures mac_log)
  [SMTPat (mac1 i)] = ()

let mac1_implies_prf (i:id) : Lemma
  (requires (mac1 i))
  (ensures (prf i))
  [SMTPat (mac1 i)] = ()

let safeId_implies_mac1 (i:id): Lemma
  (requires (safeId i))
  (ensures (mac1 i))
  [SMTPat (safeId i)] = ()

let safeId_implies_cpa (i:id) : Lemma
  (requires (safeId i))
  (ensures (prf_cpa))
  [SMTPat (safeId i)] = ()

inline_for_extraction
let aes_ct = false
