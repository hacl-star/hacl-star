module HaCl

open HaCl.Base

//open Hash.Sha1
//open Hash.Sha224
open Hash.Sha256
//open Hash.Sha384
//open Hash.Sha512



////////////////////////////////////////////////////////////////// 
//
// Hashing functions
//

assume val hacl_hash': alg:hash_alg -> data:bytes -> len:bytes{len = length data} -> Tot (hash:bytes{length hash = hashSize alg})

let hacl_hash alg hash data len =
  match alg with
//  | SHA1 -> sha1 hash data len
//  | SHA224 -> sha224 hash data len
  | SHA256 -> sha256 hash data len 
//  | SHA384 -> sha384 hash data len 
//  | SHA512 -> sha512 hash data len


let hacl_hash_sha256 hash data len =
  sha256 hash data len


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
