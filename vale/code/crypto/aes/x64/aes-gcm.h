
struct gcm_args {
  unsigned char* plaintext;
  unsigned int   plain_len;
  unsigned char* additional_data;
  unsigned int   additional_data_len;
  unsigned char* iv;
  unsigned char* expanded_key_ptr;
  unsigned char* ciphertext_ptr;
  unsigned char* tag_ptr;
  unsigned char* tmp_ptr;   // Should point to a buffer of (at least) 8*64 bits
};

extern void gcm_encrypt(struct gcm_args* args);
