module Flag
(* These is the concrete version of ideal_flags/Flag.fstar
   It sets all the flags to false to extract only the concrete
   version of the code, without any of the cryptographic idealizations
*)

module ST = FStar.HyperStack.ST

// Secret-dependant access to sbox, dangerous
inline_for_extraction
let aes_ct = false
