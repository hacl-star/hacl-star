open Test_utils

type 'a box_test =
  { name: string ; pk: 'a ; sk: 'a ; n: 'a ; pt: 'a ; expected_ct: 'a }

type 'a secretbox_test =
  { name: string; key: 'a ; n: 'a ; pt: 'a; expected_ct: 'a }

let box_tests = [
  { name = "Test 1";
    pk = Bytes.of_string "\xfe\x38\x04\x02\x70\x14\xcf\x0c\x89\x68\x11\xd5\x23\x40\x32\xe5\xeb\x6c\xa1\x78\x6f\x64\x8c\x64\x86\xf3\xfa\xdd\x26\x4d\x17\x41";
    sk = Bytes.of_string "\xd5\x7d\xff\xb8\x10\xeb\x32\xff\xaa\x87\x93\x24\x46\xa0\xc6\xe3\x6e\xb9\x54\xa7\x37\xe9\xcc\x3a\xc0\xd9\x80\x34\x41\xe2\xbe\xac";
    n = init_bytes 24;
    pt = Bytes.of_string "\x17\x8c\xb3\x11\xd2\x0f\x0a";
    expected_ct = Bytes.of_string "\x06\x2f\x0c\x61\x1b\x5a\xd3\x2d\xf8\xd4\x2f\xea\x32\x6e\xb9\xc5\xb9\x2a\xda\x4d\x98\xea\x08"
  };
  { name = "Test 2";
    pk = Bytes.of_string "\xc7\x99\xe1\xb6\xa1\x0c\x60\x9e\x44\x9b\xa3\x48\x38\xec\xc7\x94\x04\x98\x9c\x69\xac\xb3\x63\xd9\x52\x7f\x78\x66\xe5\x7b\xa6\x4a";
    sk = Bytes.of_string "\x07\xbb\x38\xf5\xb2\xdb\x98\xae\xe6\x02\x1b\x5e\xb1\xe8\x08\xe3\xe4\x67\x70\x20\xa2\x60\x9f\xa7\xd0\x89\xb5\x23\xc1\x35\xf5\xdf";
    n = init_bytes 24;
    pt = Bytes.of_string "\x93\xc6\x9d\x5b\xce\xea\xd5\x24\x03\x4e\x5c\x50";
    expected_ct = Bytes.of_string "\x77\x87\x8b\x2b\xce\x5a\xbf\x2f\xac\x5a\x14\xec\xd9\x58\x09\x68\xa6\x97\x6a\x8a\xf3\x41\x15\xce\x02\x3c\x95\x0e"
  }
]

let secretbox_tests = [
  { name = "Test 1";
    key = Bytes.of_string "\x82\x2b\xca\x3c\x7e\x05\xfd\xe0\xdc\x20\x45\x19\x73\x0b\x35\xf8\x12\x16\xa9\xc9\xf1\xdf\x95\x25\xe2\xa9\x00\xec\x89\x71\x8f\x57";
    n = Bytes.of_string "\x72\xb9\x02\x08\xd2\x80\x0e\x36\xad\x16\xc7\x30\x94\x1a\x03\x8d\x7c\x3a\xd9\xd8\x70\x30\xd3\x29";
    pt = Bytes.of_string "";
    expected_ct =Bytes.of_string "\x79\xb3\x45\x51\xed\x22\x4f\xa1\x7c\xb6\x46\x0c\xcb\x90\xa0\xd9"
  };
  { name = "Test 2";
    key = Bytes.of_string "\x49\xd1\x3a\x96\x6a\x76\x1a\x6a\xcf\xfe\xd8\x92\x3b\x5e\xe5\x0c\x29\x71\xba\x7e\x12\xc0\x1f\xd9\x9e\x0d\x70\xde\x91\x32\xf6\xd7";
    n = Bytes.of_string "\x66\x1d\x42\xc4\x8f\x71\xb3\x1c\x30\xd5\xc2\x65\xb1\x68\x51\x1a\xfd\x58\xb8\x70\xbf\x35\x4f\x4f";
    pt = Bytes.of_string "\xa9\x4d\x36\x5d\x0f\x3a\x0a\x50\x4c\x8c\x12\x76\x25\x31";
    expected_ct = Bytes.of_string "\x00\x21\xf4\x17\x24\xbe\x3a\xc9\xa4\x6b\xd5\x6c\x19\x64\x4d\x32\x0e\xb9\xcb\x66\x30\x3b\x98\xed\xa2\x9e\x22\x81\xed\x5e"
  }
]


let test_box (v: Bytes.t box_test) =
  let ct = Test_utils.init_bytes (Bytes.length v.pt + 16) in
  let pt = Test_utils.init_bytes (Bytes.length v.pt) in

  let test_result = Test_utils.test_result ("Hacl.NaCl.Easy box " ^ v.name) in
  if Hacl.NaCl.Easy.box ct v.pt v.n v.pk v.sk then
    if Bytes.compare ct v.expected_ct <> 0 then
      test_result Failure "ciphertext mismatch"
    else
    if Hacl.NaCl.Easy.box_open pt ct v.n v.pk v.sk then
      if Bytes.compare pt v.pt <> 0 then
        test_result Failure "decrypted plaintext mismatch"
      else
        test_result Success ""
    else
      test_result Failure "Decryption failed"
  else
    test_result Failure "Encryption failed";

  let ct_detached = Test_utils.init_bytes (Bytes.length v.pt) in
  let tag = Test_utils.init_bytes 16 in
  Bytes.fill pt 0 (Bytes.length pt) '\x00';

  let test_result = Test_utils.test_result ("Hacl.NaCl.Detached box " ^ v.name) in
  if Hacl.NaCl.Detached.box ct_detached tag v.pt v.n v.pk v.sk then
    let combined_ct = Bytes.of_string @@ (Bytes.to_string tag) ^ (Bytes.to_string ct_detached) in
    if Bytes.compare combined_ct v.expected_ct <> 0 then
      test_result Failure "ciphertext mismatch"
    else
    if Hacl.NaCl.Detached.box_open pt ct_detached tag v.n v.pk v.sk then
      if Bytes.compare pt v.pt <> 0 then
        test_result Failure "decrypted plaintext mismatch"
      else
        test_result Success ""
    else
      test_result Failure "Decryption failed"
  else
    test_result Failure "Encryption failed";

  let k = Test_utils.init_bytes 32 in

  let test_result = Test_utils.test_result ("Hacl.NaCl.box_beforenm " ^ v.name) in
  if Hacl.NaCl.box_beforenm k v.pk v.sk then
    test_result Success ""
  else
    test_result Failure "";

  Bytes.fill ct 0 (Bytes.length ct) '\x00';
  Bytes.fill pt 0 (Bytes.length pt) '\x00';

  let test_result = Test_utils.test_result ("Hacl.NaCl.Easy box_afternm " ^ v.name) in
  if Hacl.NaCl.Easy.box_afternm ct v.pt v.n k then
    if Bytes.compare ct v.expected_ct <> 0 then
      test_result Failure "ciphertext mismatch"
    else
    if Hacl.NaCl.Easy.box_open_afternm pt ct v.n k then
      if Bytes.compare pt v.pt <> 0 then
        test_result Failure "decrypted plaintext mismatch"
      else
        test_result Success ""
    else
      test_result Failure "Decryption failed"
  else
    test_result Failure "Encryption failed";

  Bytes.fill ct_detached 0 (Bytes.length ct_detached) '\x00';
  Bytes.fill tag 0 (Bytes.length tag) '\x00';
  Bytes.fill pt 0 (Bytes.length pt) '\x00';

  let test_result = Test_utils.test_result ("Hacl.NaCl.Detached box_afternm " ^ v.name) in
  if Hacl.NaCl.Detached.box_afternm ct_detached tag v.pt v.n k then
    let combined_ct = Bytes.of_string @@ (Bytes.to_string tag) ^ (Bytes.to_string ct_detached) in
    if Bytes.compare combined_ct v.expected_ct <> 0 then
      test_result Failure "ciphertext mismatch"
    else
    if Hacl.NaCl.Detached.box_open_afternm pt ct_detached tag v.n k then
      if Bytes.compare pt v.pt <> 0 then
        test_result Failure "decrypted plaintext mismatch"
      else
        test_result Success ""
    else
      test_result Failure "Decryption failed"
  else
    test_result Failure "Encryption failed"

let test_secretbox (v: Bytes.t secretbox_test) =
  let ct = Test_utils.init_bytes (Bytes.length v.pt + 16) in
  let pt = Test_utils.init_bytes (Bytes.length v.pt) in

  let test_result = Test_utils.test_result ("Hacl.NaCl.Easy secretbox " ^ v.name) in
  if Hacl.NaCl.Easy.secretbox ct v.pt v.n v.key then
    if Bytes.compare ct v.expected_ct <> 0 then
      test_result Failure "ciphertext mismatch"
    else
    if Hacl.NaCl.Easy.secretbox_open pt ct v.n v.key then
      if Bytes.compare pt v.pt <> 0 then
        test_result Failure "decrypted plaintext mismatch"
      else
        test_result Success ""
    else
      test_result Failure "Decryption failed"
  else
    test_result Failure "Encryption failed";

  let ct_detached = Test_utils.init_bytes (Bytes.length v.pt) in
  let tag = Test_utils.init_bytes 16 in
  Bytes.fill pt 0 (Bytes.length pt) '\x00';

  let test_result = Test_utils.test_result ("Hacl.NaCl.Detached secretbox " ^ v.name) in
  if Hacl.NaCl.Detached.secretbox ct_detached tag v.pt v.n v.key then
    let combined_ct = Bytes.of_string @@ (Bytes.to_string tag) ^ (Bytes.to_string ct_detached) in
    if Bytes.compare combined_ct v.expected_ct <> 0 then
      test_result Failure "ciphertext mismatch"
    else
    if Hacl.NaCl.Detached.secretbox_open pt ct_detached tag v.n v.key then
      if Bytes.compare pt v.pt <> 0 then
        test_result Failure "decrypted plaintext mismatch"
      else
        test_result Success ""
    else
      test_result Failure "Decryption failed"
  else
    test_result Failure "Encryption failed"


let _ =
  List.iter test_box box_tests;
  List.iter test_secretbox secretbox_tests
