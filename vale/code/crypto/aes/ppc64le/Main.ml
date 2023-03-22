let _ =
  CmdLineParser.parse_cmdline_ppc64le [
    ("aes128_key_expansion", (fun () -> Vale_AES_PPC64LE_AES.va_code_KeyExpansionStdcall Vale_AES_AES_common_s.AES_128), 2, false);
    ("aes128_keyhash_init", (fun () -> Vale_AES_PPC64LE_GF128_Init.va_code_Keyhash_init Vale_AES_AES_common_s.AES_128), 2, false);
    ("aes256_key_expansion", (fun () -> Vale_AES_PPC64LE_AES.va_code_KeyExpansionStdcall Vale_AES_AES_common_s.AES_256), 2, false);
    ("aes256_keyhash_init", (fun () -> Vale_AES_PPC64LE_GF128_Init.va_code_Keyhash_init Vale_AES_AES_common_s.AES_256), 2, false);
    ("compute_iv_stdcall", Vale_AES_PPC64LE_GCMencrypt.va_code_Compute_iv_stdcall, 6, false);
    ("gcm128_encrypt", (fun () -> Vale_AES_PPC64LE_GCMencrypt.va_code_Gcm_blocks_stdcall Vale_AES_AES_common_s.AES_128), 1, false);
    ("gcm256_encrypt", (fun () -> Vale_AES_PPC64LE_GCMencrypt.va_code_Gcm_blocks_stdcall Vale_AES_AES_common_s.AES_256), 1, false);
    ("gcm128_decrypt", (fun () -> Vale_AES_PPC64LE_GCMdecrypt.va_code_Gcm_blocks_decrypt_stdcall Vale_AES_AES_common_s.AES_128), 1, false);
    ("gcm256_decrypt", (fun () -> Vale_AES_PPC64LE_GCMdecrypt.va_code_Gcm_blocks_decrypt_stdcall Vale_AES_AES_common_s.AES_256), 1, false);
  ]
