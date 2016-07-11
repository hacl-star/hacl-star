module HaCl

open FStar.HyperStack
open HaCl.Base


////////////////////////////////////////////////////////////////// 
//
// Hashing functions
//

val hacl_hash: alg:hash_alg -> hash:bytes{length hash = hashSize alg} -> data:bytes -> len:nat{len = length data} 
  -> STL (retcode:int)
        (requires (fun h -> live h hash /\ live h data))
        (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 data /\ modifies_1 hash h0 h1 /\ hash = (hacl_hash' alg data len)))


////////////////////////////////////////////////////////////////// 
//
// Authenticated encryption functions for secret-key cryptography
//

//
// Function : crypto_secretbox
//

assume val hacl_secretbox: alg:aead_alg -> output:ciphertext -> input:bytes -> len:nat{len = length input} -> n:nonce{length n = aeadRealIVSize alg} -> k:key{length k = aeadKeySize alg}
  -> STL (retcode:int)
        (requires (fun h -> live h output /\ live h input /\ live h n /\ live h k))
        (ensures  (fun h0 r h1 -> live h1 output /\ live h1 input /\ live h1 n /\ live h1 k 
                             /\ modifies_1 output h0 h1 /\ output = (hacl_secretbox' alg input len n k)))

//
// Function : crypto_secretbox_open
//

assume val hacl_secretbox_open: alg:aead_alg -> output:bytes -> input:ciphertext -> len:nat{len = length input} -> n:nonce{length n = aeadRealIVSize alg} -> k:key{length k = aeadKeySize alg} 
  -> STL (retcode:int)
        (requires (fun h -> live h output /\ live h input /\ live h n /\ live h k))
        (ensures  (fun h0 r h1 -> live h1 output /\ live h1 input /\ live h1 n /\ live h1 k
                             /\ modifies_1 output h0 h1 /\ output = (hacl_secretbox_open' alg input len n k)))


////////////////////////////////////////////////////////////////// 
//
// Authenticated encryption functions for public-key cryptography
//

//
// Function : crypto_box_keypair
//

assume val hacl_box_keypair: ec:ec_curve -> pkey:ec_point_bytes -> skey:ec_key_bytes 
  -> STL (retcode:int)
        (requires (fun h -> live h pkey /\ live h skey))
        (ensures  (fun h0 r h1 -> live h1 pkey /\ live h1 skey 
                             /\ modifies_1 pkey h0 h1 /\ modifies_2 skey h0 h1
                             /\ pkey = serialize_ec_point (first (hacl_box_keypair' ()))
                             /\ skey = serialize_ec_key (snd (hacl_box_keypair' ()))))

//
// Function : crypto_box
//

assume val hacl_box: ec:ec_curve -> alg:aead_cipher -> output:ciphertext -> input:bytes -> len:nat{len = length input} -> n:nonce{length n = aeadRealIVSize alg} -> pkey:ec_point_bytes -> skey:ec_key_bytes
  -> STL (retcode:int)
        (requires (fun h -> live h output /\ live h input /\ live h n /\ live h pkey /\ live h skey))
        (ensures  (fun h0 r h1 -> live h1 output /\ live h1 input /\ live h1 n /\ live h1 pkey /\ live h1 skey
                             /\ modifies_1 output h0 h1 
                             /\ output = (hacl_box' ec alg input len n (parsing_ec_point pkey) (parsing_ec_key skey))))

//
// Function : crypto_box_open
//

assume val hacl_box_open: ec:ec_curve -> alg:aead_cipher -> output:bytes -> input:ciphertext -> len:nat{len = length ciphertext} -> n:nonce{length n = aeadRealIVSize alg} -> pkey:ec_point_bytes -> skey:ec_key_bytes
  -> STL (retcode:int)
        (requires (fun h -> live h output /\ live h input /\ live h n /\ live h pkey /\ live h skey))
        (ensures  (fun h0 r h1 -> live h1 output /\ live h1 input /\ live h1 n /\ live h1 pkey /\ live h1 skey
                             /\ modifies_1 output h0 h1
                             /\ output = (hacl_box_open' ec alg input len n (parsing_ec_point pkey) (parsing_ec_key skey))))
