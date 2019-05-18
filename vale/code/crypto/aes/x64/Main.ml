let _ =
  CmdLineParser.parse_cmdline [
      ("old_aes128_key_expansion", (fun win -> Vale_AES_X64_AES.va_code_KeyExpansionStdcall win Vale_AES_AES_s.AES_128));
      ("aes128_key_expansion", (fun win -> Vale_AES_X64_AES.va_code_KeyExpansionStdcall win Vale_AES_AES_s.AES_128));
      ("aes128_keyhash_init", (fun win -> Vale_AES_X64_GF128_Init.va_code_Keyhash_init win Vale_AES_AES_s.AES_128));
      ("old_aes256_key_expansion", (fun win -> Vale_AES_X64_AES.va_code_KeyExpansionStdcall win Vale_AES_AES_s.AES_256));
      ("aes256_key_expansion", (fun win -> Vale_AES_X64_AES.va_code_KeyExpansionStdcall win Vale_AES_AES_s.AES_256));
      ("aes256_keyhash_init", (fun win -> Vale_AES_X64_GF128_Init.va_code_Keyhash_init win Vale_AES_AES_s.AES_256));
      ("gctr128_bytes",            (fun win -> Vale_AES_X64_GCTR.va_code_gctr_bytes_stdcall win Vale_AES_AES_s.AES_128));
      ("gctr256_bytes",            (fun win -> Vale_AES_X64_GCTR.va_code_gctr_bytes_stdcall win Vale_AES_AES_s.AES_256));
      ("old_gcm128_encrypt",       (fun win -> Vale_AES_X64_GCMencrypt.va_code_gcm_encrypt_stdcall win Vale_AES_AES_s.AES_128));
      ("gcm128_encrypt",       (fun win -> Vale_AES_X64_GCMencrypt.va_code_gcm_encrypt2_stdcall win Vale_AES_AES_s.AES_128));
      ("old_gcm128_decrypt",       (fun win -> Vale_AES_X64_GCMdecrypt.va_code_gcm_decrypt_stdcall win Vale_AES_AES_s.AES_128));
      ("gcm128_decrypt",           (fun win -> Vale_AES_X64_GCMdecrypt.va_code_gcm_decrypt2_stdcall win Vale_AES_AES_s.AES_128));
      ("old_gcm256_encrypt",       (fun win -> Vale_AES_X64_GCMencrypt.va_code_gcm_encrypt_stdcall win Vale_AES_AES_s.AES_256));
      ("gcm256_encrypt",           (fun win -> Vale_AES_X64_GCMencrypt.va_code_gcm_encrypt2_stdcall win Vale_AES_AES_s.AES_256));
      ("old_gcm256_decrypt",       (fun win -> Vale_AES_X64_GCMdecrypt.va_code_gcm_decrypt_stdcall win Vale_AES_AES_s.AES_256));
      ("gcm256_decrypt",           (fun win -> Vale_AES_X64_GCMdecrypt.va_code_gcm_decrypt2_stdcall win Vale_AES_AES_s.AES_256));
      ("gcm128_encrypt_opt",       (fun win -> Vale_AES_X64_GCMencryptOpt.va_code_gcm_blocks_stdcall win Vale_AES_AES_s.AES_128));
      ("gcm256_encrypt_opt",       (fun win -> Vale_AES_X64_GCMencryptOpt.va_code_gcm_blocks_stdcall win Vale_AES_AES_s.AES_256));
      ("gcm128_decrypt_opt",       (fun win -> Vale_AES_X64_GCMdecryptOpt.va_code_gcm_blocks_decrypt_stdcall win Vale_AES_AES_s.AES_128));
      ("gcm256_decrypt_opt",       (fun win -> Vale_AES_X64_GCMdecryptOpt.va_code_gcm_blocks_decrypt_stdcall win Vale_AES_AES_s.AES_256));
    ]
