let _ =
  CmdLineParser.parse_cmdline [
      ("aes128_key_expansion", (fun win -> X64_AES.va_code_KeyExpansionStdcall win AES_s.AES_128));
      ("aes256_key_expansion", (fun win -> X64_AES.va_code_KeyExpansionStdcall win AES_s.AES_256));
      ("gcm128_encrypt",       (fun win -> X64_GCMencrypt.va_code_gcm_encrypt_stdcall win AES_s.AES_128));
      ("gcm128_decrypt",       (fun win -> X64_GCMdecrypt.va_code_gcm_decrypt_stdcall win AES_s.AES_128));
      ("gcm256_encrypt",       (fun win -> X64_GCMencrypt.va_code_gcm_encrypt_stdcall win AES_s.AES_256));
      ("gcm256_decrypt",       (fun win -> X64_GCMdecrypt.va_code_gcm_decrypt_stdcall win AES_s.AES_256));
      ("AESEncryptBlock_win_aes128_encrypt_block_win", (fun win -> X64_AES.va_code_AESEncryptBlockStdcall win AES_s.AES_128));
      ("AESEncryptBE_win_aes128_encrypt_block_be_win", (fun win -> X64_AES.va_code_AESEncryptBlockStdcall_BE win AES_s.AES_128));
      ("GCTR_win_gctr_bytes_extra_buffer_win", (fun win ->
  if win then X64_GCTR.va_code_gctr_bytes_extra_buffer_win AES_s.AES_128
  else X64_GCTR.va_code_gctr_bytes_extra_stdcall AES_s.AES_128));
      ("GHash_stdcall_win_ghash_incremental_bytes_stdcall_win", (fun win ->
  if win then X64_GHash.va_code_ghash_incremental_bytes_stdcall_win ()
  else X64_GHash.va_code_ghash_incremental_bytes_stdcall ()));
      ("GHash_one_block_win_ghash_incremental_one_block_buffer_win", (fun win ->
  if win then X64_GHash.va_code_ghash_incremental_one_block_buffer_win ()
  else X64_GHash.va_code_ghash_incremental_one_block_buffer ()));
      ("GHash_extra_win_ghash_incremental_extra_stdcall_win", (fun win ->
  if win then X64_GHash.va_code_ghash_incremental_extra_stdcall_win ()
  else X64_GHash.va_code_ghash_incremental_extra_stdcall ()));
      ("Gcm_load_xor_win_gcm_load_xor_store_buffer_win", (fun win ->
  if win then X64_Util.va_code_gcm_load_xor_store_buffer_win ()
  else X64_Util.va_code_gcm_load_xor_store_buffer ()));
      ("Inc32_win_inc32_buffer_win", (fun win ->
  if win then X64_GCTR.va_code_inc32_buffer_win ()
  else X64_GCTR.va_code_inc32_buffer ()));
      ("Zero_quad32_win_zero_quad32_buffer", (fun win ->
  if win then X64_Util.va_code_zero_quad32_buffer_win ()
  else X64_Util.va_code_zero_quad32_buffer ()));
      ("Mk_quad32_1_win_mk_quad32_lo0_be_1_buffer_win", (fun win ->
  if win then X64_Util.va_code_mk_quad32_lo0_be_1_buffer_win ()
  else X64_Util.va_code_mk_quad32_lo0_be_1_buffer ()));
      ("Gcm_make_length_win_gcm_make_length_quad_buffer_win", (fun win ->
  if win then X64_GCMencrypt.va_code_gcm_make_length_quad_buffer_win ()
  else X64_GCMencrypt.va_code_gcm_make_length_quad_buffer ()));
      ("Quad32_xor_win_quad32_xor_buffer_win", (fun win ->
  if win then X64_Util.va_code_quad32_xor_buffer_win ()
  else X64_Util.va_code_quad32_xor_buffer ()));
      ("Reverse_quad32_win_reverse_bytes_quad32_buffer_win", (fun win ->
  if win then X64_Util.va_code_reverse_bytes_quad32_buffer_win ()
  else X64_Util.va_code_reverse_bytes_quad32_buffer ()))
    ]
