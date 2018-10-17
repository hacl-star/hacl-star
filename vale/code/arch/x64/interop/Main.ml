open Interop_Printer




(* let poly = ("poly", [("ctx", TBuffer TUInt64); ("inp", TBuffer TUInt64); ("len", TBase TUInt64)]) *)

(* let aes = ("aes", [("input_key", TBuffer TUInt128); ("output_key", TBuffer TUInt128)]) *)
	    
(* let gcmencrypt = ("gcmencrypt", [
  ("plain_b", TBuffer TUInt128); ("plain_num_bytes", TBase TUInt64);
  ("auth_b", TBuffer TUInt128); ("auth_num_bytes", TBase TUInt64);
  ("iv_b", TBuffer TUInt128); 
  ("key", TGhost "aes_key_LE AES_128"); ("keys_b", TBuffer TUInt128);
  ("cipher_b", TBuffer TUInt128); ("tag_b", TBuffer TUInt128)
  ],
    Stk (Prims.parse_int "18"))
*)

let aes_encrypt_block = ("AESEncryptBlockStdcall", [
  ("output_b", TBuffer TUInt128, Sec); ("input_b", TBuffer TUInt128, Sec);
  ("key", TGhost "aes_key_LE AES_128", Pub); ("keys_b", TBuffer TUInt128, Sec)
  ], 
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"), 
  Modifies ["output_b"],
  Return Unit)

let aes_encrypt_block_be = ("aes_EncryptBlockBEStdcall", [
  ("output_b", TBuffer TUInt128, Sec); ("input_b", TBuffer TUInt128, Sec);
  ("key", TGhost "aes_key_LE AES_128", Pub); ("keys_b", TBuffer TUInt128, Sec)
  ], 
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"),
  Modifies ["output_b"],
  Return Unit
  )

let ghash = ("ghash_incremental_bytes_stdcall", [
  ("h_b", TBuffer TUInt128, Sec); ("hash_b", TBuffer TUInt128, Sec);
  ("input_b", TBuffer TUInt128, Sec); ("num_bytes", TBase TUInt64, Pub)
  ], 
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"),
  Modifies ["hash_b"],
  Return Unit)

let ghash_extra = ("ghash_extra_stdcall", [
  ("in_b", TBuffer TUInt128, Sec); ("hash_b", TBuffer TUInt128, Sec);
  ("h_b", TBuffer TUInt128, Sec); ("num_bytes", TBase TUInt64, Pub);
  ("orig_hash", TGhost "quad32", Pub)], 
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"),
  Modifies ["hash_b"],
  Return Unit)

let ghash_one_block = ("ghash_one_block", [
  ("h_b", TBuffer TUInt128, Sec); ("hash_b", TBuffer TUInt128, Sec);
  ("input_b", TBuffer TUInt128, Sec); ("offset", TBase TUInt64, Pub)
  ], 
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"),
  Modifies ["hash_b"],
  Return Unit)

let gcm_load_xor = ("gcm_load_xor_stdcall", [
  ("plain_b", TBuffer TUInt128, Sec); ("mask_b", TBuffer TUInt128, Sec);
  ("cipher_b", TBuffer TUInt128, Sec); ("offset", TBase TUInt64, Sec);
  ("num_blocks", TGhost "nat64", Pub);
  ("key", TGhost "aes_key_LE AES_128", Pub); ("iv", TGhost "quad32", Pub)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["cipher_b"],
  Return Unit)

let inc32 = ("inc32_stdcall", [("iv_b", TBuffer TUInt128, Sec)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["iv_b"],
  Return Unit)

let zero_quad32 = ("zero_quad32_stdcall", [("b", TBuffer TUInt128, Sec)],
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["b"],
  Return Unit)

let reverse_quad32 = ("reverse_quad32_stdcall", [("b", TBuffer TUInt128, Sec)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["b"],
  Return Unit)

let mk_quad1 = ("mk_quad32_lo0_be_1_stdcall", [("b", TBuffer TUInt128, Sec)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["b"],
  Return Unit)

let gcm_make_length = ("gcm_make_length_stdcall", [
  ("plain_num_bytes", TBase TUInt64, Pub); ("auth_num_bytes", TBase TUInt64, Pub);
  ("b", TBuffer TUInt128, Sec)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["b"],
  Return Unit)

let gctr_bytes_extra = ("gctr_bytes_extra_stdcall", [
  ("plain_b", TBuffer TUInt128, Sec); ("num_bytes", TBase TUInt64, Pub);
  ("iv_old", TGhost "quad32", Pub); ("iv_b", TBuffer TUInt128, Sec);
  ("key", TGhost "aes_key_LE AES_128", Pub); ("keys_b", TBuffer TUInt128, Sec);
  ("cipher_b", TBuffer TUInt128, Sec)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["cipher_b"],
  Return Unit)


let quad32_xor = ("quad32_xor_stdcall", [("src1", TBuffer TUInt128, Sec);
  ("src2", TBuffer TUInt128, Sec); ("dst", TBuffer TUInt128, Sec)], 
  SaveRegsStk false,
  AddStk (Prims.parse_int "0"),
  Modifies ["dst"],
  Return Unit)

let sha_update_bytes =
   ("sha_update_bytes_stdcall",  
  [("ctx_b", TBuffer TUInt128, Sec);  ("in_b", TBuffer TUInt128, Sec); 
    ("num_val", TBase TUInt64, Sec); ("k_b", TBuffer TUInt128, Sec)], 
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"),
  Modifies ["ctx_b"],
  Return Unit)

let memcpy = ("memcpy", [("dst", TBuffer TUInt64, Sec); ("src", TBuffer TUInt64, Sec)], SaveRegsStk false, AddStk (Prims.parse_int "0"), Modifies ["dst"], Return Unit)

let gctr_bytes128 =
  ("gctr_bytes_stdcall128",
  [("in_b", TBuffer TUInt128, Sec); ("out_b", TBuffer TUInt128, Sec);
   ("key", TGhost "seq nat32", Sec); ("round_keys", TGhost "seq quad32", Sec);
   ("keys_b", TBuffer TUInt128, Sec); ("num_val", TBase TUInt64, Sec);
   ("iv_b", TBuffer TUInt128, Sec)],
  SaveRegsStk true,
  AddStk (Prims.parse_int "0"),
  Modifies ["out_b"],
  Return Unit)

let check_aesni = ("check_aesni_stdcall", [], SaveRegsStk false, AddStk (Prims.parse_int "0"), Modifies [], Return Int64)

let check_sha = ("check_sha_stdcall", [], SaveRegsStk false, AddStk (Prims.parse_int "0"), Modifies [], Return Int64)

let name = sha_update_bytes 

let _ = print_string (translate_vale X86 name)
let _ = print_newline()
let _ = print_string (translate_lowstar X86 name)
