module Hacl

open Hacl.Constants
open Hacl.Core


////////////////////////////////////////////////////////////////// 
//
// Hashing functions
//

let hash alg output data len = Hacl.Core.hash alg output data len
  
let hash_sha2_256 output data len =
  Hacl.Core.hash SHA2_256 output data len
  
let hash_sha2_512 output data len =
  Hacl.Core.hash SHA2_512 output data len

let hash_sha3_256 output data len =
  Hacl.Core.hash SHA3_256 output data len
  
let hash_sha3_512 output data len =
  Hacl.Core.hash SHA3_512 output data len


////////////////////////////////////////////////////////////////// 
//
// Authenticated encryption functions for secret-key cryptography
//

//
// Function : crypto_secretbox
//

assume val hacl_secretbox': alg:aead_alg -> input:bytes -> len:nat{len = length input} -> n:nonce{length n = aeadRealIVSize alg} -> k:key{length k = aeadKeySize alg} -> Tot (output:ciphertext{length output = len})


//
// Function : crypto_secretbox_open
//

assume val hacl_secretbox_open': alg:aead_alg -> input:ciphertext -> len:nat{len = length input} -> n:nonce{length n = aeadRealIVSize alg} -> k:key{length k = aeadKeySize alg} -> Tot (output:bytes{length output = len})


////////////////////////////////////////////////////////////////// 
//
// Authenticated encryption functions for public-key cryptography
//

//
// Function : crypto_box_keypair
//

assume val hacl_box_keypair': ec:ec_curve -> Tot (pk:ec_point{ec_point_is_on_curve ec pkey} * sk:ec_key{ec_point_is_pkey_of_skey ec skey pkey})


//
// Function : crypto_box
//

assume val hacl_box': ec:ec_curve -> alg:aead_cipher -> input:bytes -> len:nat{len = length input} -> n:nonce{length n = aeadRealIVSize alg} -> pkey:ec_point{ec_point_is_on_curve ec pkey} -> skey:ec_key{ec_point_is_pkey_of_skey ec skey pkey} -> Tot (output:ciphertext{length output = len})


//
// Function : crypto_box_open
//

assume val hacl_box_open': ec:ec_curve -> alg:aead_alg -> input:ciphertext -> len:nat{len = length ciphertext} -> n:nonce{length n = aeadRealIVSize alg} -> pkey:ec_point{ec_point_is_on_curve ec pkey} -> skey:ec_key{ec_point_is_pkey_of_skey ec skey pkey} -> Tot (output:bytes{length output = len})
