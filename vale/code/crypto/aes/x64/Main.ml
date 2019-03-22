let _ =
  CmdLineParser.parse_cmdline [
      ("aes128_key_expansion", (fun win -> X64_AES.va_code_KeyExpansionStdcall win AES_s.AES_128));
      ("aes256_key_expansion", (fun win -> X64_AES.va_code_KeyExpansionStdcall win AES_s.AES_256));
(*      ("gcm128_encrypt_old",       (fun win -> X64_GCMencrypt.va_code_gcm_encrypt_stdcall win AES_s.AES_128));  *)
      ("gcm128_encrypt",       (fun win -> X64_GCMencrypt.va_code_gcm_encrypt2_stdcall win AES_s.AES_128));
      ("gcm128_decrypt",       (fun win -> X64_GCMdecrypt.va_code_gcm_decrypt_stdcall win AES_s.AES_128));
(*      ("gcm256_encrypt_old",       (fun win -> X64_GCMencrypt.va_code_gcm_encrypt_stdcall win AES_s.AES_256)); *)
      ("gcm256_encrypt",       (fun win -> X64_GCMencrypt.va_code_gcm_encrypt2_stdcall win AES_s.AES_256));
      ("gcm256_decrypt",       (fun win -> X64_GCMdecrypt.va_code_gcm_decrypt_stdcall win AES_s.AES_256));
      ("gcm128_encrypt_opt",       (fun win -> X64_GCMencryptOpt.va_code_gcm_blocks_stdcall win AES_s.AES_128));
    ]
