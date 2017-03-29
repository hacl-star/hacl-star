module Spec.SHA2.Specialization



//
// SHA-512
//

let size_hash_w = 8

let h_0 =
  Seq.seq_of_list [
  0x6a09e667f3bcc908uL; 0xbb67ae8584caa73buL; 0x3c6ef372fe94f82buL; 0xa54ff53a5f1d36f1uL;
  0x510e527fade682d1uL; 0x9b05688c2b3e6c1fuL; 0x1f83d9abfb41bd6buL; 0x5be0cd19137e2179uL] 
