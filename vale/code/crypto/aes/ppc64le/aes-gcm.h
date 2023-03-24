
struct gcm_args {
  unsigned char*           auth_final_block;
  const unsigned char*     plaintext;
  unsigned char*           ciphertext;
  unsigned long long       plain_block_num;
  unsigned char*           text_final_block;
  unsigned long long       plain_len;
  const unsigned char*     additional_data;
  unsigned long long       auth_block_num;
  unsigned long long       additional_data_len;
  unsigned char*           iv;
  const unsigned char*     expanded_key;
  const unsigned char*     expanded_h_key;
  unsigned char*           tag;       // const in case of decrypt
};


// Layout of keyhash expanded key
// *------------------------------------------------------*
// |   (H << 1)   mod (reduction polynomial)  (128-bit)   |
// |   (H^2 << 1) mod (reduction polynomial)  (128-bit)   |
// |                     H                    (128-bit)   |
// *------------------------------------------------------*

// gcm_decrypt return 0 in case content of tag buffer is equal
// to computed authentication hash. Otherwise, return > 0


//AES-128 functions
extern "C" void aes128_key_expansion(unsigned char* expanded_key, const unsigned char* key);
extern "C" void aes128_keyhash_init(unsigned char* expanded_h_key, const unsigned char* expanded_aes_key);
extern "C" void gcm128_encrypt(struct gcm_args* args);
extern "C" int  gcm128_decrypt(struct gcm_args* args);

//AES-256 functions
extern "C" void aes256_key_expansion(unsigned char* expanded_key, const unsigned char* key);
extern "C" void aes256_keyhash_init(unsigned char* expanded_h_key, const unsigned char* expanded_aes_key);
extern "C" void gcm256_encrypt(struct gcm_args* args);
extern "C" int  gcm256_decrypt(struct gcm_args* args);
