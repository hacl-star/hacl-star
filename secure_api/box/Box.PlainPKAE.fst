(**
   TODO: Documentation and some cleaup.
*)
module Box.PlainPKAE

open Box.Flags
open Box.Indexing

open FStar.Seq

type bytes = seq UInt8.t

noeq abstract type protected_pkae_plain = 
  | Prot_pkae_p: #i:id{AE_id? i} -> b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32} -> protected_pkae_plain

type pkae_plain = b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32}

val get_index: p:protected_pkae_plain -> Tot (i:id{i=p.i})
let get_index p =
  p.i

(* two pure functions, never called when ideal *)
val repr: p:protected_pkae_plain{not pkae \/ (dishonest p.i) } -> Tot pkae_plain
let repr p = p.b

// Change this if we want to use signcryption with pkae_int-ctxt
val coerce: #i:id{AE_id? i} -> p:pkae_plain{not pkae \/ (dishonest i)} -> Tot (prot:protected_pkae_plain{i=prot.i})
let coerce #i p = 
  Prot_pkae_p #i p  

val length:  protected_pkae_plain -> Tot (n:nat{n / Spec.Salsa20.blocklen < pow2 32})
let length p = Seq.length p.b

// Create coece_keyshare function
