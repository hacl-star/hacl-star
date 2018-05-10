module EverCrypt.Specs

let sha256_init_pre = fun _ -> False
let sha256_init_post = fun _ _ _ -> True
let sha256_update_pre = fun _ -> False
let sha256_update_post = fun _ _ _ -> True
let sha256_update_multi_pre = fun _ -> False
let sha256_update_multi_post = fun _ _ _ -> True
let sha256_update_last_pre = fun _ -> False
let sha256_update_last_post = fun _ _ _ -> True
let sha256_finish_pre = fun _ -> False
let sha256_finish_post = fun _ _ _ -> True
let sha256_hash_pre = fun _ -> False
let sha256_hash_post = fun _ _ _ -> True

let sha384_init_pre = fun _ -> False
let sha384_init_post = fun _ _ _ -> True
let sha384_update_pre = fun _ -> False
let sha384_update_post = fun _ _ _ -> True
let sha384_update_multi_pre = fun _ -> False
let sha384_update_multi_post = fun _ _ _ -> True
let sha384_update_last_pre = fun _ -> False
let sha384_update_last_post = fun _ _ _ -> True
let sha384_finish_pre = fun _ -> False
let sha384_finish_post = fun _ _ _ -> True
let sha384_hash_pre = fun _ -> False
let sha384_hash_post = fun _ _ _ -> True

let sha512_init_pre = fun _ -> False
let sha512_init_post = fun _ _ _ -> True
let sha512_update_pre = fun _ -> False
let sha512_update_post = fun _ _ _ -> True
let sha512_update_multi_pre = fun _ -> False
let sha512_update_multi_post = fun _ _ _ -> True
let sha512_update_last_pre = fun _ -> False
let sha512_update_last_post = fun _ _ _ -> True
let sha512_finish_pre = fun _ -> False
let sha512_finish_post = fun _ _ _ -> True
let sha512_hash_pre = fun _ -> False
let sha512_hash_post = fun _ _ _ -> True

let curve_x25519_pre = fun _ -> False
let curve_x25519_post = fun _ _ _ -> True

let aes256_gcm_encrypt_pre = fun _ -> False
let aes256_gcm_encrypt_post = fun _ _ _ -> True
