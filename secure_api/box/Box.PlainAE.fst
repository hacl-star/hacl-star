(**
   This module contains the plaintext type of AE and functions to access it.
*)
module Box.PlainAE

open FStar.Seq

open Box.Flags
open Box.Indexing
open Box.PlainBox

type bytes = seq UInt8.t

(**
   The protected plaintext type of AE. It is associated with an id and acts as a wrapper around a protected pkae plaintext.
   The ids associated with both plaintexts must be equal.
*)
abstract type protected_ae_plain (i:id{AE_id? i}) = p:protected_pkae_plain{get_index p = i}

(**
   The unprotected plaintext type.
*)
type ae_plain = b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32}

(**
   This function can bypass the abstraction protection of the protected plaintext type. However, this is only possible
   if ae_ind_cpa is not idealized, or if the id associated with the plaintext is dishonest.
*)
val repr: #i:id{AE_id? i} -> p:protected_ae_plain i{not ae_ind_cpa \/ (dishonest i)} -> Tot (ae_plain)
let repr #i p =
    PlainBox.repr p

(**
   This function allows the creation of protected plaintexts. Protected plaintexts can only be created by the adversary if
   either ae_int_cca is not idealized or of the id associated with the newly created plaintext is dishonest.
*)
val coerce: #i:id{AE_id? i} -> p:ae_plain{not ae_ind_cca \/ (dishonest i)} -> Tot (protected_ae_plain i)
let coerce #i p =
  PlainBox.coerce #i p

(**
   This is a helper function used by the top-level box function to encapsulate the payload before
   passing it on to AE.encrypt.
*)
val ae_message_wrap: #i:id{AE_id? i} -> p:protected_pkae_plain{get_index p = i} -> Tot (protected_ae_plain i)
let ae_message_wrap #i p = p

(**
   This is the reverse function to ae_message_wrap. box_open uses it to extract a
   protected ae payload.
*)
val ae_message_unwrap: #i:id{AE_id? i} -> p:protected_ae_plain i -> Tot (p:protected_pkae_plain{get_index p = i})
let ae_message_unwrap #i p = p

  (**
     A helper function to obtain the length of a protected plaintext.
     *)
val length: #i:id{AE_id? i} -> (protected_ae_plain i) -> Tot (n:nat {n / Spec.Salsa20.blocklen < pow2 32})
let length #i p = PlainBox.length p
