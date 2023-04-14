// Separate module because -no-prefix
module EverCrypt.Hash.Incremental.Macros

(* These definitions for the benefits of C clients. *)
[@ CMacro ] let md5_hash_len = 16ul
[@ CMacro ] let sha1_hash_len = 20ul
[@ CMacro ] let sha2_224_hash_len = 28ul
[@ CMacro ] let sha2_256_hash_len = 32ul
[@ CMacro ] let sha2_384_hash_len = 48ul
[@ CMacro ] let sha2_512_hash_len = 64ul
[@ CMacro ] let sha3_224_hash_len = 28ul
[@ CMacro ] let sha3_256_hash_len = 32ul
[@ CMacro ] let sha3_384_hash_len = 48ul
[@ CMacro ] let sha3_512_hash_len = 64ul
[@ CMacro ] let blake2s_hash_len = 32ul
[@ CMacro ] let blake2b_hash_len = 64ul
