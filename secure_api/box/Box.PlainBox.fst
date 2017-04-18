(**
   This module contains the plaintext type of the top-level construction and functions to access it.
   TODO:
   * Change protected_pkae_plain to expect an id as parameter
   *
*)
module Box.PlainBox

open Box.Flags
open Box.Indexing

open FStar.Seq

type bytes = seq UInt8.t

(**
   The protected plaintext type of the pkae construction. It is associated with an id and bytes, that
   match the required format for encryption with the Salsa20 spec.
*)
noeq abstract type protected_pkae_plain =
  | Prot_pkae_p: #i:id{AE_id? i} -> b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32} -> protected_pkae_plain

(**
   The unprotected plaintext type.
*)
type pkae_plain = b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32}

(**
   A helper function to get the index of the abstract, protected plaintext.
*)
val get_index: p:protected_pkae_plain -> Tot (i:id{i=p.i})
let get_index p =
  p.i

(**
   This function can bypass the abstraction protection of the protected plaintext type. However, this is only possible
   if pkae_ind_cpa is not idealized, or if the id associated with the plaintext is dishonest.
*)
val repr: p:protected_pkae_plain{not pkae_ind_cpa \/ (dishonest p.i) } -> Tot (b:pkae_plain{Seq.length b / Spec.Salsa20.blocklen < pow2 32})
let repr p = p.b

(**
   This function allows the creation of protected plaintexts. Protected plaintexts can only be created by the adversary if
   either pkae_int_ctxt is not idealized or of the id associated with the newly created plaintext is dishonest.
*)
val coerce: #i:id{AE_id? i} -> p:pkae_plain{not pkae_int_ctxt \/ (dishonest i)} -> Tot (prot:protected_pkae_plain{i=prot.i})
let coerce #i p =
  Prot_pkae_p #i p

(**
   A helper function to obtain the length of a protected plaintext.
*)
val length:  protected_pkae_plain -> Tot (n:nat{n / Spec.Salsa20.blocklen < pow2 32})
let length p = Seq.length p.b
