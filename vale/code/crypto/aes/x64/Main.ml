let _ =
  CmdLineParser.parse_cmdline [
    ("aes128_key_expansion", (fun win -> Vale_AES_X64_AES.va_code_KeyExpansionStdcall win Vale_AES_AES_s.AES_128, Vale_AES_X64_AES.va_codegen_success_KeyExpansionStdcall win Vale_AES_AES_s.AES_128), 2, false);
    ("aes128_keyhash_init", (fun win -> Vale_AES_X64_GF128_Init.va_code_Keyhash_init win Vale_AES_AES_s.AES_128, Vale_AES_X64_GF128_Init.va_codegen_success_Keyhash_init win Vale_AES_AES_s.AES_128), 2, false);
    ("aes256_key_expansion", (fun win -> Vale_AES_X64_AES.va_code_KeyExpansionStdcall win Vale_AES_AES_s.AES_256, Vale_AES_X64_AES.va_codegen_success_KeyExpansionStdcall win Vale_AES_AES_s.AES_256), 2, false);
    ("aes256_keyhash_init", (fun win -> Vale_AES_X64_GF128_Init.va_code_Keyhash_init win Vale_AES_AES_s.AES_256, Vale_AES_X64_GF128_Init.va_codegen_success_Keyhash_init win Vale_AES_AES_s.AES_256), 2, false);
    ("gctr128_bytes",            (fun win -> Vale_AES_X64_GCTR.va_code_Gctr_bytes_stdcall win Vale_AES_AES_s.AES_128, Vale_AES_X64_GCTR.va_codegen_success_Gctr_bytes_stdcall win Vale_AES_AES_s.AES_128), 7, false);
    ("gctr256_bytes",            (fun win -> Vale_AES_X64_GCTR.va_code_Gctr_bytes_stdcall win Vale_AES_AES_s.AES_256, Vale_AES_X64_GCTR.va_codegen_success_Gctr_bytes_stdcall win Vale_AES_AES_s.AES_256), 7, false);
    ("compute_iv_stdcall",       (fun win -> Vale_AES_X64_GCMencryptOpt.va_code_Compute_iv_stdcall win, Vale_AES_X64_GCMencryptOpt.va_codegen_success_Compute_iv_stdcall win), 6, false);
    ("gcm128_encrypt_opt",       (fun win -> Vale_AES_X64_GCMencryptOpt.va_code_Gcm_blocks_stdcall win Vale_AES_AES_s.AES_128, Vale_AES_X64_GCMencryptOpt.va_codegen_success_Gcm_blocks_stdcall win Vale_AES_AES_s.AES_128), 17, false);
    ("gcm256_encrypt_opt",       (fun win -> Vale_AES_X64_GCMencryptOpt.va_code_Gcm_blocks_stdcall win Vale_AES_AES_s.AES_256, Vale_AES_X64_GCMencryptOpt.va_codegen_success_Gcm_blocks_stdcall win Vale_AES_AES_s.AES_256), 17, false);
    ("gcm128_decrypt_opt",       (fun win -> Vale_AES_X64_GCMdecryptOpt.va_code_Gcm_blocks_decrypt_stdcall win Vale_AES_AES_s.AES_128, Vale_AES_X64_GCMdecryptOpt.va_codegen_success_Gcm_blocks_decrypt_stdcall win Vale_AES_AES_s.AES_128), 17, false);
    ("gcm256_decrypt_opt",       (fun win -> Vale_AES_X64_GCMdecryptOpt.va_code_Gcm_blocks_decrypt_stdcall win Vale_AES_AES_s.AES_256, Vale_AES_X64_GCMdecryptOpt.va_codegen_success_Gcm_blocks_decrypt_stdcall win Vale_AES_AES_s.AES_256), 17, false);
  ]
