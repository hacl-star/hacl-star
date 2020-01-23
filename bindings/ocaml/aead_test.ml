type aead_test =
  { alg: EverCrypt.AEAD.alg;
    key_len: int; msg_len: int; iv_len: int ; ad_len: int; tag_len: int;
    test_key: Bigstring.t; test_iv: Bigstring.t; test_ad: Bigstring.t;
    test_pt: Bigstring.t; test_ct: Bigstring.t; test_tag: Bigstring.t
  }

let chacha20poly1305_test: aead_test =
  { alg = CHACHA20_POLY1305; key_len = 32; msg_len = 114; iv_len = 12; ad_len = 12; tag_len = 16;
    test_key = Bigstring.of_string "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f";
    test_iv = Bigstring.of_string "\x07\x00\x00\x00\x40\x41\x42\x43\x44\x45\x46\x47";
    test_ad = Bigstring.of_string "\x50\x51\x52\x53\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7";
    test_pt = Bigstring.of_string "\x4c\x61\x64\x69\x65\x73\x20\x61\x6e\x64\x20\x47\x65\x6e\x74\x6c\x65\x6d\x65\x6e\x20\x6f\x66\x20\x74\x68\x65\x20\x63\x6c\x61\x73\x73\x20\x6f\x66\x20\x27\x39\x39\x3a\x20\x49\x66\x20\x49\x20\x63\x6f\x75\x6c\x64\x20\x6f\x66\x66\x65\x72\x20\x79\x6f\x75\x20\x6f\x6e\x6c\x79\x20\x6f\x6e\x65\x20\x74\x69\x70\x20\x66\x6f\x72\x20\x74\x68\x65\x20\x66\x75\x74\x75\x72\x65\x2c\x20\x73\x75\x6e\x73\x63\x72\x65\x65\x6e\x20\x77\x6f\x75\x6c\x64\x20\x62\x65\x20\x69\x74\x2e";
    test_ct = Bigstring.of_string "\xd3\x1a\x8d\x34\x64\x8e\x60\xdb\x7b\x86\xaf\xbc\x53\xef\x7e\xc2\xa4\xad\xed\x51\x29\x6e\x08\xfe\xa9\xe2\xb5\xa7\x36\xee\x62\xd6\x3d\xbe\xa4\x5e\x8c\xa9\x67\x12\x82\xfa\xfb\x69\xda\x92\x72\x8b\x1a\x71\xde\x0a\x9e\x06\x0b\x29\x05\xd6\xa5\xb6\x7e\xcd\x3b\x36\x92\xdd\xbd\x7f\x2d\x77\x8b\x8c\x98\x03\xae\xe3\x28\x09\x1b\x58\xfa\xb3\x24\xe4\xfa\xd6\x75\x94\x55\x85\x80\x8b\x48\x31\xd7\xbc\x3f\xf4\xde\xf0\x8e\x4b\x7a\x9d\xe5\x76\xd2\x65\x86\xce\xc6\x4b\x61\x16";
    test_tag = Bigstring.of_string "\x1a\xe1\x0b\x59\x4f\x09\xe2\x6a\x7e\x90\x2e\xcb\xd0\x60\x06\x91"
  }


let validate_test (v: aead_test) =
  assert (Bigstring.size v.test_key = v.key_len);
  assert (Bigstring.size v.test_iv = v.iv_len);
  assert (Bigstring.size v.test_ad = v.ad_len);
  assert (Bigstring.size v.test_pt = v.msg_len);
  assert (Bigstring.size v.test_ct = v.msg_len);
  assert (Bigstring.size v.test_tag = v.tag_len)


let test (v: aead_test) =
  let open EverCrypt.AEAD in

  validate_test v;
  let st = alloc_t () in
  let ct = Bigstring.create v.msg_len in
  let tag = Bigstring.create v.tag_len in
  Bigstring.fill ct '\x00';
  Bigstring.fill tag '\x00';

  match create_in v.alg st v.test_key with
  | Success -> begin
      match encrypt st v.test_iv v.iv_len v.test_ad v.ad_len v.test_pt v.msg_len ct tag with
      | Success -> begin
          if Bigstring.compare tag v.test_tag = 0 && Bigstring.compare ct v.test_ct = 0 then
            Printf.printf "Encryption success\n"
          else
            Printf.printf "Failure: wrong ciphertext/mac\n";
          let dt = Bigstring.create v.msg_len in
          Bigstring.fill dt '\x00';
          match decrypt st v.test_iv v.iv_len v.test_ad v.ad_len ct v.msg_len v.test_tag dt with
          | Success ->
            if Bigstring.compare v.test_pt dt = 0 then
              Printf.printf "Decryption success\n"
            else
              Printf.printf "Failure: decrypted and plaintext do not match\n"
          | Error n -> Printf.printf "Decryption error %d\n" n
        end
      | Error n -> Printf.printf "Encryption error %d\n" n
    end
  | Error n -> Printf.printf "Init error %d\n" n


let _ =
  EverCrypt.AutoConfig2.init ();
  Printf.printf "has_shaext: %b\n" (EverCrypt.AutoConfig2.has_shaext ());
  Printf.printf "has_aesni %b\n" (EverCrypt.AutoConfig2.has_aesni ());
  Printf.printf "has_pclmulqdq %b\n" (EverCrypt.AutoConfig2.has_pclmulqdq ());
  Printf.printf "has_avx2 %b\n" (EverCrypt.AutoConfig2.has_avx2 ());
  Printf.printf "has_avx %b\n" (EverCrypt.AutoConfig2.has_avx ());
  Printf.printf "has_bmi2 %b\n" (EverCrypt.AutoConfig2.has_bmi2 ());
  Printf.printf "has_adx %b\n" (EverCrypt.AutoConfig2.has_adx ());
  Printf.printf "has_sse %b\n" (EverCrypt.AutoConfig2.has_sse ());
  Printf.printf "has_movbe %b\n" (EverCrypt.AutoConfig2.has_movbe ());
  Printf.printf "has_rdrand %b\n" (EverCrypt.AutoConfig2.has_rdrand ());
  Printf.printf "wants_vale %b\n" (EverCrypt.AutoConfig2.wants_vale ());
  Printf.printf "wants_hacl %b\n" (EverCrypt.AutoConfig2.wants_hacl ());
  Printf.printf "wants_openssl %b\n" (EverCrypt.AutoConfig2.wants_openssl ());
  Printf.printf "wants_bcrypt %b\n" (EverCrypt.AutoConfig2.wants_bcrypt ());
  test chacha20poly1305_test
