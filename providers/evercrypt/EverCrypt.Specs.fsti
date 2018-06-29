module EverCrypt.Specs

let curve_x25519_pre = fun _ -> False
let curve_x25519_post = fun _ _ _ -> True

let aes128_gcm_encrypt_pre = fun _ -> False
let aes128_gcm_encrypt_post = fun _ _ _ -> True
let aes128_gcm_decrypt_pre = fun _ -> False
let aes128_gcm_decrypt_post = fun _ _ _ -> True
let aes256_gcm_encrypt_pre = fun _ -> False
let aes256_gcm_encrypt_post = fun _ _ _ -> True
let aes256_gcm_decrypt_pre = fun _ -> False
let aes256_gcm_decrypt_post = fun _ _ _ -> True

let chacha20_poly1305_encode_length_pre = fun _ -> False
let chacha20_poly1305_encode_length_post = fun _ _ _ -> True
let chacha20_poly1305_encrypt_pre = fun _ -> False
let chacha20_poly1305_encrypt_post = fun _ _ _ -> True
let chacha20_poly1305_decrypt_pre = fun _ -> False
let chacha20_poly1305_decrypt_post = fun _ _ _ -> True
