module Hacl.Impl.HPKE

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.Buffer
open Lib.IntTypes

module S = Spec.Agile.HPKE

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let key_dh_public (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_dh_public cs))
inline_for_extraction noextract
let key_dh_secret (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_dh_key cs))
inline_for_extraction noextract
let key_aead (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_aead_key cs))
inline_for_extraction noextract
let nonce_aead (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_aead_nonce cs))

inline_for_extraction noextract
let setupBaseI_st (cs:S.ciphersuite) =
     o_pkE: key_dh_public cs
  -> o_k: key_aead cs
  -> o_n: nonce_aead cs
  -> skE: key_dh_secret cs
  -> pkR: key_dh_public cs
  -> infolen: size_t{v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> ST unit
     (requires fun h0 ->
        (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
          Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
        live h0 o_pkE /\ live h0 o_k /\ live h0 o_n /\
        live h0 skE /\ live h0 pkR /\ live h0 info /\
        disjoint o_pkE skE /\ disjoint o_pkE pkR /\ disjoint o_pkE info /\
        disjoint o_pkE o_k /\ disjoint o_pkE o_n /\
        disjoint o_k o_n)
     (ensures fun h0 _ h1 -> modifies (loc o_pkE |+| loc o_k |+| loc o_n) h0 h1 /\
       (let pkE, k, n = S.setupBaseI cs (as_seq h0 skE) (as_seq h0 pkR) (as_seq h0 info) in
        as_seq h1 o_pkE == pkE /\
        as_seq h1 o_k == k /\
        as_seq h1 o_n == n)
     )

inline_for_extraction noextract
let setupBaseR_st (cs:S.ciphersuite) =
     o_key_aead: key_aead cs
  -> o_nonce_aead: nonce_aead cs
  -> pkE: key_dh_public cs
  -> skR: key_dh_secret cs
  -> infolen: size_t{v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> ST unit
     (requires fun h0 ->
        (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
          Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
        live h0 o_key_aead /\ live h0 o_nonce_aead /\
        live h0 pkE /\ live h0 skR /\ live h0 info /\
        disjoint o_key_aead o_nonce_aead)
     (ensures fun h0 _ h1 -> modifies (loc o_key_aead |+| loc o_nonce_aead) h0 h1 /\
       (let k, n = S.setupBaseR cs (as_seq h0 pkE) (as_seq h0 skR) (as_seq h0 info) in
        as_seq h1 o_key_aead == k /\
        as_seq h1 o_nonce_aead == n)
     )

inline_for_extraction noextract
let sealBase_st (cs:S.ciphersuite) =
     skE: key_dh_secret cs
  -> pkR: key_dh_public cs
  -> mlen: size_t{v mlen <= S.max_length cs /\ v mlen + S.size_dh_public cs + 16 <= max_size_t}
  -> m:lbuffer uint8 mlen
  -> infolen: size_t {v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> output: lbuffer uint8 (size (v mlen + S.size_dh_public cs + 16))
  -> ST unit
       (requires fun h0 ->
        (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
         Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
         live h0 output /\ live h0 skE /\ live h0 pkR /\
         live h0 m /\ live h0 info /\
         disjoint output pkR /\ disjoint output info /\ disjoint output m /\ disjoint output skE)
       (ensures fun h0 _ h1 -> modifies (loc output) h0 h1 /\
         as_seq h1 output `Seq.equal` S.sealBase cs (as_seq h0 skE) (as_seq h0 pkR) (as_seq h0 m) (as_seq h0 info))

inline_for_extraction noextract
let openBase_st (cs:S.ciphersuite) =
     pkE: key_dh_public cs
  -> skR: key_dh_secret cs
  -> mlen: size_t{S.size_dh_public cs + S.size_aead_tag cs <= v mlen /\ v mlen <= S.max_length cs}
  -> m:lbuffer uint8 mlen
  -> infolen: size_t {v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> output: lbuffer uint8 (size (v mlen - S.size_dh_public cs - S.size_aead_tag cs))
  -> ST UInt32.t
       (requires fun h0 ->
        (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
          Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
         live h0 output /\ live h0 pkE /\ live h0 skR /\
         live h0 m /\ live h0 info /\
         disjoint output info /\ disjoint output m)
       (ensures fun h0 z h1 -> modifies (loc output) h0 h1 /\
         (let plain = S.openBase cs (as_seq h0 skR) (as_seq h0 m) (as_seq h0 info) in
         match z with
         | 0ul -> Some? plain /\ as_seq h1 output == Some?.v plain
         | 1ul -> None? plain
         | _ -> False))

noextract inline_for_extraction
val setupBaseI: #cs:S.ciphersuite -> setupBaseI_st cs

noextract inline_for_extraction
val setupBaseR: #cs:S.ciphersuite -> setupBaseR_st cs

noextract inline_for_extraction
val sealBase: #cs:S.ciphersuite -> sealBase_st cs

noextract inline_for_extraction
val openBase: #cs:S.ciphersuite -> openBase_st cs
