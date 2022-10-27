open Test_utils

let tag_len = 16
let key_len = 32

type 'a box_test =
  { pk: 'a ; sk: 'a ; n: 'a ; pt: 'a ; expected_ct: 'a }

type 'a secretbox_test =
  { key: 'a ; n: 'a ; pt: 'a; expected_ct: 'a }

let box_tests =
  [
    { pk = Bytes.of_string "\xfe\x38\x04\x02\x70\x14\xcf\x0c\x89\x68\x11\xd5\x23\x40\x32\xe5\xeb\x6c\xa1\x78\x6f\x64\x8c\x64\x86\xf3\xfa\xdd\x26\x4d\x17\x41";
      sk = Bytes.of_string "\xd5\x7d\xff\xb8\x10\xeb\x32\xff\xaa\x87\x93\x24\x46\xa0\xc6\xe3\x6e\xb9\x54\xa7\x37\xe9\xcc\x3a\xc0\xd9\x80\x34\x41\xe2\xbe\xac";
      n = init_bytes 24;
      pt = Bytes.of_string "\x17\x8c\xb3\x11\xd2\x0f\x0a";
      expected_ct = Bytes.of_string "\x06\x2f\x0c\x61\x1b\x5a\xd3\x2d\xf8\xd4\x2f\xea\x32\x6e\xb9\xc5\xb9\x2a\xda\x4d\x98\xea\x08"
    };
    { pk = Bytes.of_string "\xc7\x99\xe1\xb6\xa1\x0c\x60\x9e\x44\x9b\xa3\x48\x38\xec\xc7\x94\x04\x98\x9c\x69\xac\xb3\x63\xd9\x52\x7f\x78\x66\xe5\x7b\xa6\x4a";
      sk = Bytes.of_string "\x07\xbb\x38\xf5\xb2\xdb\x98\xae\xe6\x02\x1b\x5e\xb1\xe8\x08\xe3\xe4\x67\x70\x20\xa2\x60\x9f\xa7\xd0\x89\xb5\x23\xc1\x35\xf5\xdf";
      n = init_bytes 24;
      pt = Bytes.of_string "\x93\xc6\x9d\x5b\xce\xea\xd5\x24\x03\x4e\x5c\x50";
      expected_ct = Bytes.of_string "\x77\x87\x8b\x2b\xce\x5a\xbf\x2f\xac\x5a\x14\xec\xd9\x58\x09\x68\xa6\x97\x6a\x8a\xf3\x41\x15\xce\x02\x3c\x95\x0e"
    }
  ]

let secretbox_tests =
  [
    { key = Bytes.of_string "\x82\x2b\xca\x3c\x7e\x05\xfd\xe0\xdc\x20\x45\x19\x73\x0b\x35\xf8\x12\x16\xa9\xc9\xf1\xdf\x95\x25\xe2\xa9\x00\xec\x89\x71\x8f\x57";
      n = Bytes.of_string "\x72\xb9\x02\x08\xd2\x80\x0e\x36\xad\x16\xc7\x30\x94\x1a\x03\x8d\x7c\x3a\xd9\xd8\x70\x30\xd3\x29";
      pt = Bytes.of_string "";
      expected_ct =Bytes.of_string "\x79\xb3\x45\x51\xed\x22\x4f\xa1\x7c\xb6\x46\x0c\xcb\x90\xa0\xd9"
    };
    { key = Bytes.of_string "\x49\xd1\x3a\x96\x6a\x76\x1a\x6a\xcf\xfe\xd8\x92\x3b\x5e\xe5\x0c\x29\x71\xba\x7e\x12\xc0\x1f\xd9\x9e\x0d\x70\xde\x91\x32\xf6\xd7";
      n = Bytes.of_string "\x66\x1d\x42\xc4\x8f\x71\xb3\x1c\x30\xd5\xc2\x65\xb1\x68\x51\x1a\xfd\x58\xb8\x70\xbf\x35\x4f\x4f";
      pt = Bytes.of_string "\xa9\x4d\x36\x5d\x0f\x3a\x0a\x50\x4c\x8c\x12\x76\x25\x31";
      expected_ct = Bytes.of_string "\x00\x21\xf4\x17\x24\xbe\x3a\xc9\xa4\x6b\xd5\x6c\x19\x64\x4d\x32\x0e\xb9\xcb\x66\x30\x3b\x98\xed\xa2\x9e\x22\x81\xed\x5e"
    }
  ]

let box =
  let test_box () =
    List.iter (fun (v: Bytes.t box_test) ->
        match Hacl.NaCl.box ~pt:v.pt ~n:v.n ~pk:v.pk ~sk:v.sk with
        | Some ct -> (
            Alcotest.(check bytes "Ciphertext" ct v.expected_ct);
            match Hacl.NaCl.box_open ~ct ~n:v.n ~pk:v.pk ~sk:v.sk with
            | Some pt ->
              Alcotest.(check bytes "Decrypted plaintext" pt v.pt);
            | None ->
              Alcotest.fail "Decryption")
        | None ->
          Alcotest.fail "Encryption") box_tests
  in

  let test_box_afternm () =
    List.iter (fun (v: Bytes.t box_test) ->
        match Hacl.NaCl.box_beforenm ~pk:v.pk ~sk:v.sk with
        | Some ck -> (
            match Hacl.NaCl.box_afternm ~pt:v.pt ~n:v.n ~ck with
            | Some ct -> (
                Alcotest.(check bytes "Ciphertext" ct v.expected_ct);
                match Hacl.NaCl.box_open_afternm ~ct ~n:v.n ~ck with
                | Some pt ->
                  Alcotest.(check bytes "Decrypted plaintext" pt v.pt);
                | None ->
                  Alcotest.fail "Decryption"
              )
            | None ->
              Alcotest.fail "Encryption"
          )
        | None ->
          Alcotest.fail "Generating combined key") box_tests
  in
  [
    ("Box (one-shot)", `Quick, test_box);
    ("Box (precomputation)", `Quick, test_box_afternm);
  ]

let box_noalloc =
  let test_box_noalloc_easy ~pt_offset ~ct_offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let pt_len = Bytes.length v.pt in
        let pt = Bytes.(cat (make pt_offset '\x00')) v.pt in
        let ct = init_bytes (ct_offset + tag_len + pt_len) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Easy.box ~pt ~pt_offset ~n:v.n ~pk:v.pk ~sk:v.sk ~ct ~ct_offset ()) true);
        Alcotest.(check bytes "Ciphertext" (Bytes.sub ct ct_offset (pt_len + tag_len)) v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Easy.box_open ~ct ~ct_offset ~n:v.n ~pk:v.pk ~sk:v.sk ~pt ~pt_offset ()) true);
        Alcotest.(check bytes "Decrypted plaintext" (Bytes.sub pt pt_offset pt_len) v.pt)
      ) box_tests
  in
  let test_box_noalloc_easy_with_len ~pt_offset ~ct_offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let pt_len = Bytes.length v.pt in
        let pt = Bytes.(concat empty [make pt_offset '\x00'; v.pt; v.pt]) in
        let ct = init_bytes (ct_offset + tag_len + 2 * pt_len) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Easy.box ~pt ~pt_offset ~pt_len ~n:v.n ~pk:v.pk ~sk:v.sk ~ct ~ct_offset ()) true);
        Alcotest.(check bytes "Ciphertext" (Bytes.sub ct ct_offset (pt_len + tag_len)) v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Easy.box_open ~ct ~ct_offset ~ct_len:(pt_len + tag_len) ~n:v.n ~pk:v.pk ~sk:v.sk ~pt ~pt_offset ()) true);
        Alcotest.(check bytes "Decrypted plaintext" (Bytes.sub pt pt_offset pt_len) v.pt)
      ) box_tests
  in
  let test_box_noalloc_detached ~offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let tag = init_bytes tag_len in
        let buf = Bytes.(cat (make offset '\x00') v.pt) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Detached.box ~buf ~tag ~offset ~n:v.n ~pk:v.pk ~sk:v.sk ()) true);
        let combined_ct = Bytes.(cat tag (sub buf offset (length v.pt))) in
        Alcotest.(check bytes "Ciphertext" combined_ct v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Detached.box_open ~buf ~tag ~offset ~n:v.n ~pk:v.pk ~sk:v.sk ()) true);
        Alcotest.(check bytes "Decrypted plaintext" Bytes.(sub buf offset (length v.pt)) v.pt)
      ) box_tests
  in
  let test_box_noalloc_detached_with_len ~offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let tag = init_bytes tag_len in
        let buf = Bytes.(concat empty [make offset '\x00'; v.pt; v.pt]) in
        let len = Bytes.length v.pt in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Detached.box ~buf ~tag ~offset ~len ~n:v.n ~pk:v.pk ~sk:v.sk ()) true);
        let combined_ct = Bytes.(cat tag (sub buf offset (length v.pt))) in
        Alcotest.(check bytes "Ciphertext" combined_ct v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Detached.box_open ~buf ~tag ~offset ~len ~n:v.n ~pk:v.pk ~sk:v.sk ()) true);
        Alcotest.(check bytes "Decrypted plaintext" Bytes.(sub buf offset (length v.pt)) v.pt)
      ) box_tests
  in
  let test_box_noalloc_easy_afternm ~pt_offset ~ct_offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let ck = init_bytes key_len in
        Alcotest.(check bool "Generating combined key" (Hacl.NaCl.Noalloc.box_beforenm ~pk:v.pk ~sk:v.sk ~ck) true);
        let pt_len = Bytes.length v.pt in
        let pt = Bytes.(cat (make pt_offset '\x00') v.pt) in
        let ct = init_bytes (ct_offset + tag_len + pt_len) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Easy.box_afternm ~pt:pt ~pt_offset ~n:v.n ~ck ~ct ~ct_offset ()) true);
        Alcotest.(check bytes "Ciphertext" (Bytes.sub ct ct_offset (pt_len + tag_len)) v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Easy.box_open_afternm ~ct ~ct_offset ~n:v.n ~ck ~pt ~pt_offset ()) true);
        Alcotest.(check bytes "Decrypted plaintext" (Bytes.sub pt pt_offset pt_len) v.pt)
      ) box_tests
  in
  let test_box_noalloc_easy_afternm_with_len ~pt_offset ~ct_offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let ck = init_bytes key_len in
        Alcotest.(check bool "Generating combined key" (Hacl.NaCl.Noalloc.box_beforenm ~pk:v.pk ~sk:v.sk ~ck) true);
        let pt_len = Bytes.length v.pt in
        let pt = Bytes.(concat empty [make pt_offset '\x00'; v.pt; v.pt]) in
        let ct = init_bytes (ct_offset + tag_len + 2 * pt_len) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Easy.box_afternm ~pt:pt ~pt_offset ~pt_len ~n:v.n ~ck ~ct ~ct_offset ()) true);
        Alcotest.(check bytes "Ciphertext" (Bytes.sub ct ct_offset (pt_len + tag_len)) v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Easy.box_open_afternm ~ct ~ct_len:(pt_len + tag_len) ~ct_offset ~n:v.n ~ck ~pt ~pt_offset ()) true);
        Alcotest.(check bytes "Decrypted plaintext" (Bytes.sub pt pt_offset pt_len) v.pt)
      ) box_tests
  in
  let test_box_noalloc_detached_afternm ~offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let ck = init_bytes key_len in
        Alcotest.(check bool "Generating combined key" (Hacl.NaCl.Noalloc.box_beforenm ~pk:v.pk ~sk:v.sk ~ck) true);
        let tag = init_bytes tag_len in
        let buf = Bytes.(cat (make offset '\x00') v.pt) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Detached.box_afternm ~buf ~tag ~offset ~n:v.n ~ck ()) true);
        let combined_ct = Bytes.(cat tag (sub buf offset (length v.pt))) in
        Alcotest.(check bytes "Ciphertext" combined_ct v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Detached.box_open_afternm ~buf ~tag ~offset ~n:v.n ~ck ()) true);
        Alcotest.(check bytes "Decrypted plaintext" Bytes.(sub buf offset (length v.pt)) v.pt)
      ) box_tests
  in
  let test_box_noalloc_detached_afternm_with_len ~offset () =
    List.iter (fun (v: Bytes.t box_test) ->
        let ck = init_bytes key_len in
        Alcotest.(check bool "Generating combined key" (Hacl.NaCl.Noalloc.box_beforenm ~pk:v.pk ~sk:v.sk ~ck) true);
        let tag = init_bytes tag_len in
        let buf = Bytes.(concat empty [make offset '\x00'; v.pt; v.pt]) in
        let len = Bytes.length v.pt in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Detached.box_afternm ~buf ~tag ~offset ~len ~n:v.n ~ck ()) true);
        let combined_ct = Bytes.(cat tag (sub buf offset (length v.pt))) in
        Alcotest.(check bytes "Ciphertext" combined_ct v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Detached.box_open_afternm ~buf ~tag ~offset ~len ~n:v.n ~ck ()) true);
        Alcotest.(check bytes "Decrypted plaintext" Bytes.(sub buf offset (length v.pt)) v.pt)
      ) box_tests
  in
  [
    ("Easy (one-shot)", `Quick, test_box_noalloc_easy ~pt_offset:0 ~ct_offset:0);
    ("Easy (one-shot) w/ offset", `Quick, test_box_noalloc_easy ~pt_offset:7 ~ct_offset:2);
    ("Easy (one-shot) truncated", `Quick, test_box_noalloc_easy_with_len ~pt_offset:0 ~ct_offset:0);
    ("Easy (one-shot) w/ offset, truncated", `Quick, test_box_noalloc_easy_with_len ~pt_offset:0 ~ct_offset:10);
    ("Detached (one-shot)", `Quick, test_box_noalloc_detached ~offset:0);
    ("Detached (one-shot) w/ offset", `Quick, test_box_noalloc_detached ~offset:2);
    ("Detached (one-shot) truncated", `Quick, test_box_noalloc_detached_with_len ~offset:0);
    ("Detached (one-shot) w/ offset, truncated", `Quick, test_box_noalloc_detached_with_len ~offset:8);
    ("Easy (precomputed)", `Quick, test_box_noalloc_easy_afternm ~pt_offset:0 ~ct_offset:0);
    ("Easy (precomputed) w/ offset", `Quick, test_box_noalloc_easy_afternm ~pt_offset:27 ~ct_offset:9);
    ("Easy (precomputed) truncated", `Quick, test_box_noalloc_easy_afternm_with_len ~pt_offset:0 ~ct_offset:0);
    ("Easy (precomputed) w/ offset, truncated", `Quick, test_box_noalloc_easy_afternm_with_len ~pt_offset:1 ~ct_offset:7);
    ("Detached (precomputed)", `Quick, test_box_noalloc_detached_afternm ~offset:0);
    ("Detached (precomputed) w/ offset", `Quick, test_box_noalloc_detached_afternm ~offset:5);
    ("Detached (precomputed) truncated", `Quick, test_box_noalloc_detached_afternm_with_len ~offset:0);
    ("Detached (precomputed) w/ offset, truncated", `Quick, test_box_noalloc_detached_afternm_with_len ~offset:14);
  ]

let secretbox =
  let test_secretbox () =
    List.iter (fun (v: Bytes.t secretbox_test) ->
        match Hacl.NaCl.secretbox ~pt:v.pt ~n:v.n ~key:v.key with
        | Some ct -> (
            Alcotest.(check bytes "Ciphertext" ct v.expected_ct);
            match Hacl.NaCl.secretbox_open ~ct ~n:v.n ~key:v.key with
            | Some pt ->
              Alcotest.(check bytes "Decrypted plaintext" pt v.pt)
            | None ->
              Alcotest.fail "Decryption")
        | None ->
          Alcotest.fail "Encryption") secretbox_tests
  in
  [ ("Secretbox", `Quick, test_secretbox); ]

let secretbox_noalloc =
  let test_secretbox_noalloc_easy ~pt_offset ~ct_offset () =
    List.iter (fun (v: Bytes.t secretbox_test) ->
        let pt_len = Bytes.length v.pt in
        let pt = Bytes.(cat (make pt_offset '\x00') v.pt) in
        let ct = init_bytes (ct_offset + tag_len + pt_len) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Easy.secretbox ~pt ~pt_offset ~n:v.n ~key:v.key ~ct ~ct_offset ()) true);
        Alcotest.(check bytes "Ciphertext" (Bytes.sub ct ct_offset (pt_len + tag_len)) v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Easy.secretbox_open ~ct ~ct_offset ~n:v.n ~key:v.key ~pt ~pt_offset ()) true);
        Alcotest.(check bytes "Decrypted plaintext" (Bytes.sub pt pt_offset pt_len) v.pt)
      ) secretbox_tests
  in
  let test_secretbox_noalloc_easy_with_len ~pt_offset ~ct_offset () =
    List.iter (fun (v: Bytes.t secretbox_test) ->
        let pt_len = Bytes.length v.pt in
        let pt = Bytes.(concat empty [make pt_offset '\x00'; v.pt; v.pt]) in
        let ct = init_bytes (ct_offset + tag_len + 2 * pt_len) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Easy.secretbox ~pt ~pt_offset ~pt_len ~n:v.n ~key:v.key ~ct ~ct_offset ()) true);
        Alcotest.(check bytes "Ciphertext" (Bytes.sub ct ct_offset (pt_len + tag_len)) v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Easy.secretbox_open ~ct ~ct_offset ~ct_len:(pt_len + tag_len) ~n:v.n ~key:v.key ~pt ~pt_offset ()) true);
        Alcotest.(check bytes "Decrypted plaintext" (Bytes.sub pt pt_offset pt_len) v.pt)
      ) secretbox_tests
  in
  let test_secretbox_noalloc_detached ~offset () =
    List.iter (fun (v: Bytes.t secretbox_test) ->
        let tag = init_bytes tag_len in
        let buf = Bytes.(cat (make offset '\x00') v.pt) in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Detached.secretbox ~buf ~tag ~offset ~n:v.n ~key:v.key ()) true);
        let combined_ct = Bytes.(cat tag (sub buf offset (length v.pt))) in
        Alcotest.(check bytes "Ciphertext" combined_ct v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Detached.secretbox_open ~buf ~tag ~offset ~n:v.n ~key:v.key ()) true);
        Alcotest.(check bytes "Decrypted plaintext" Bytes.(sub buf offset (length v.pt)) v.pt)
      ) secretbox_tests
  in
  let test_secretbox_noalloc_detached_with_len ~offset () =
    List.iter (fun (v: Bytes.t secretbox_test) ->
        let tag = init_bytes tag_len in
        let buf = Bytes.(concat empty [make offset '\x00'; v.pt; v.pt]) in
        let len = Bytes.length v.pt in
        Alcotest.(check bool "Encryption" (Hacl.NaCl.Noalloc.Detached.secretbox ~buf ~tag ~offset ~len ~n:v.n ~key:v.key ()) true);
        let combined_ct = Bytes.(cat tag (sub buf offset (length v.pt))) in
        Alcotest.(check bytes "Ciphertext" combined_ct v.expected_ct);
        Alcotest.(check bool "Decryption" (Hacl.NaCl.Noalloc.Detached.secretbox_open ~buf ~tag ~offset ~len ~n:v.n ~key:v.key ()) true);
        Alcotest.(check bytes "Decrypted plaintext" Bytes.(sub buf offset (length v.pt)) v.pt)
      ) secretbox_tests
  in
  [
    ("Easy", `Quick, test_secretbox_noalloc_easy ~pt_offset:0 ~ct_offset:0);
    ("Easy w/ offset", `Quick, test_secretbox_noalloc_easy ~pt_offset:7 ~ct_offset:130);
    ("Easy truncated", `Quick, test_secretbox_noalloc_easy_with_len ~pt_offset:0 ~ct_offset:0);
    ("Easy w/ offset, truncated", `Quick, test_secretbox_noalloc_easy_with_len ~pt_offset:34 ~ct_offset:5);
    ("Detached", `Quick, test_secretbox_noalloc_detached ~offset:0);
    ("Detached w/ offset", `Quick, test_secretbox_noalloc_detached ~offset:10);
    ("Detached truncated", `Quick, test_secretbox_noalloc_detached_with_len ~offset:0);
    ("Detached w/ offset, truncated", `Quick, test_secretbox_noalloc_detached_with_len ~offset:17);

  ]

let tests =
  [
    ("Box", box);
    ("Box Noalloc", box_noalloc);
    ("Secretbox", secretbox);
    ("Secretbox Noalloc", secretbox_noalloc);
  ]

let () = Alcotest.run "NaCl" tests
