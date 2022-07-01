module EverCrypt.Specs

inline_for_extraction noextract let curve_x25519_pre = fun _ -> False
inline_for_extraction noextract let curve_x25519_post = fun _ _ _ -> True

inline_for_extraction noextract let random_init_pre = fun _ -> False
inline_for_extraction noextract let random_init_post = fun _ _ _ -> True
inline_for_extraction noextract let random_sample_pre = fun _ -> False
inline_for_extraction noextract let random_sample_post = fun _ _ _ -> True
inline_for_extraction noextract let random_cleanup_pre = fun _ -> False
inline_for_extraction noextract let random_cleanup_post = fun _ _ _ -> True

inline_for_extraction noextract let aes128_create_pre = fun _ -> False
inline_for_extraction noextract let aes128_create_post = fun _ _ _ -> True
inline_for_extraction noextract let aes128_compute_pre = fun _ -> False
inline_for_extraction noextract let aes128_compute_post = fun _ _ _ -> True
inline_for_extraction noextract let aes128_free_pre = fun _ -> False
inline_for_extraction noextract let aes128_free_post = fun _ _ _ -> True

inline_for_extraction noextract let aes256_create_pre = fun _ -> False
inline_for_extraction noextract let aes256_create_post = fun _ _ _ -> True
inline_for_extraction noextract let aes256_compute_pre = fun _ -> False
inline_for_extraction noextract let aes256_compute_post = fun _ _ _ -> True
inline_for_extraction noextract let aes256_free_pre = fun _ -> False
inline_for_extraction noextract let aes256_free_post = fun _ _ _ -> True

inline_for_extraction noextract let chacha20_pre = fun _ -> False
inline_for_extraction noextract let chacha20_post = fun _ _ _ -> True

inline_for_extraction noextract let aes128_gcm_encrypt_pre = fun _ -> False
inline_for_extraction noextract let aes128_gcm_encrypt_post = fun _ _ _ -> True
inline_for_extraction noextract let aes128_gcm_decrypt_pre = fun _ -> False
inline_for_extraction noextract let aes128_gcm_decrypt_post = fun _ _ _ -> True
inline_for_extraction noextract let aes256_gcm_encrypt_pre = fun _ -> False
inline_for_extraction noextract let aes256_gcm_encrypt_post = fun _ _ _ -> True
inline_for_extraction noextract let aes256_gcm_decrypt_pre = fun _ -> False
inline_for_extraction noextract let aes256_gcm_decrypt_post = fun _ _ _ -> True

inline_for_extraction noextract let chacha20_poly1305_encrypt_pre = fun _ -> False
inline_for_extraction noextract let chacha20_poly1305_encrypt_post = fun _ _ _ -> True
inline_for_extraction noextract let chacha20_poly1305_decrypt_pre = fun _ -> False
inline_for_extraction noextract let chacha20_poly1305_decrypt_post = fun _ _ _ -> True

inline_for_extraction noextract let aead_create_pre = fun _ -> False
inline_for_extraction noextract let aead_create_post = fun _ _ _ -> True
inline_for_extraction noextract let aead_encrypt_pre = fun _ -> False
inline_for_extraction noextract let aead_encrypt_post = fun _ _ _ -> True
inline_for_extraction noextract let aead_decrypt_pre = fun _ -> False
inline_for_extraction noextract let aead_decrypt_post = fun _ _ _ -> True
inline_for_extraction noextract let aead_free_pre = fun _ -> False
inline_for_extraction noextract let aead_free_post = fun _ _ _ -> True

