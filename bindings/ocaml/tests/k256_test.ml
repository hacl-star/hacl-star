open Hacl
open Test_utils

let size_signature = 64
let size_pk = 64
let size_pk_uncompressed = 65
let size_pk_compressed = 33
let size_sk = 32
let size_hashed_msg = 32

type 'a k256_test =
  { msg : 'a; sk : 'a; k : 'a; pk : 'a; signature : 'a }

type 'a libsecp256k1_test =
  { pk : 'a; msg : 'a; signature : 'a; valid : bool }

let k256_tests =
  [
    (* Test vector from Hacl.Test.K256.fst *)
    { msg = Bytes.of_string "\x4b\x68\x8d\xf4\x0b\xce\xdb\xe6\x41\xdd\xb1\x6f\xf0\xa1\x84\x2d\x9c\x67\xea\x1c\x3b\xf6\x3f\x3e\x04\x71\xba\xa6\x64\x53\x1d\x1a";
      sk = Bytes.of_string "\xeb\xb2\xc0\x82\xfd\x77\x27\x89\x0a\x28\xac\x82\xf6\xbd\xf9\x7b\xad\x8d\xe9\xf5\xd7\xc9\x02\x86\x92\xde\x1a\x25\x5c\xad\x3e\x0f";
      k = Bytes.of_string "\x49\xa0\xd7\xb7\x86\xec\x9c\xde\x0d\x07\x21\xd7\x28\x04\xbe\xfd\x06\x57\x1c\x97\x4b\x19\x1e\xfb\x42\xec\xf3\x22\xba\x9d\xdd\x9a";
      pk = Bytes.of_string "\x77\x9d\xd1\x97\xa5\xdf\x97\x7e\xd2\xcf\x6c\xb3\x1d\x82\xd4\x33\x28\xb7\x90\xdc\x6b\x3b\x7d\x44\x37\xa4\x27\xbd\x58\x47\xdf\xcd\xe9\x4b\x72\x4a\x55\x5b\x6d\x01\x7b\xb7\x60\x7c\x3e\x32\x81\xda\xf5\xb1\x69\x9d\x6e\xf4\x12\x49\x75\xc9\x23\x7b\x91\x7d\x42\x6f";
      signature = Bytes.of_string "\x24\x10\x97\xef\xbf\x8b\x63\xbf\x14\x5c\x89\x61\xdb\xdf\x10\xc3\x10\xef\xbb\x3b\x26\x76\xbb\xc0\xf8\xb0\x85\x05\xc9\xe2\xf7\x95\x02\x10\x06\xb7\x83\x86\x09\x33\x9e\x8b\x41\x5a\x7f\x9a\xcb\x1b\x66\x18\x28\x13\x1a\xef\x1e\xcb\xc7\x95\x5d\xfb\x01\xf3\xca\x0e";
    };
  ]

(* Test vectors adapted from Wycheproof, as used in tests/k256-ecdsa_vectors.h
 * https://github.com/google/wycheproof/blob/master/testvectors/ecdsa_secp256k1_sha256_test.json
 *)
let libsecp256k1_tests =
  [
    { (* Test case id 1 *)
      pk = bytes_of_hex "04b838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6ff0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9";
      msg = bytes_of_hex "313233343030";
      signature = bytes_of_hex "813ef79ccefa9a56f7ba805f0e478584fe5f0dd5f567bc09b5123ccbc9832365900e75ad233fcc908509dbff5922647db37c21f4afd3203ae8dc4ae7794b0f87";
      valid = true;
    };
    { (* Test case id 3 *)
      pk = bytes_of_hex "04b838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6ff0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9";
      msg = bytes_of_hex "313233343030";
      signature = bytes_of_hex "813ef79ccefa9a56f7ba805f0e478584fe5f0dd5f567bc09b5123ccbc98323656ff18a52dcc0336f7af62400a6dd9b810732baf1ff758000d6f613a556eb31ba";
      valid = true;
    };
    { (* Test case id 119 *)
      pk = bytes_of_hex "04b838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6ff0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9";
      msg = bytes_of_hex "313233343030";
      signature = bytes_of_hex "813ef79ccefa9a56f7ba805f0e478584fe5f0dd5f567bc09b5123ccbc98323656df18a52dcc0336f7af62400a6dd9b810732baf1ff758000d6f613a556eb31ba";
      valid = false;
    };
    { (* Test case id 129 *)
      pk = bytes_of_hex "04b838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6ff0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9";
      msg = bytes_of_hex "313233343030";
      signature = bytes_of_hex "00000000000000000000000000000000000000000000000000000000000000006ff18a52dcc0336f7af62400a6dd9b810732baf1ff758000d6f613a556eb31ba";
      valid = false;
    };
    { (* Test case id 285 *)
      pk = bytes_of_hex "0407310f90a9eae149a08402f54194a0f7b4ac427bf8d9bd6c7681071dc47dc36226a6d37ac46d61fd600c0bf1bff87689ed117dda6b0e59318ae010a197a26ca0";
      msg = bytes_of_hex "313233343030";
      signature = bytes_of_hex "000000000000000000000000000000014551231950b75fc4402da1722fc9baebfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd036413e";
      valid = true;
    };
    { (* Test case id 286 *)
      pk = bytes_of_hex "0407310f90a9eae149a08402f54194a0f7b4ac427bf8d9bd6c7681071dc47dc36226a6d37ac46d61fd600c0bf1bff87689ed117dda6b0e59318ae010a197a26ca0";
      msg = bytes_of_hex "313233343030";
      signature = bytes_of_hex "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2cfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd036413e";
      valid = false;
    };
  ]

let tests_wycheproof =
  let test_verify () =
    List.iter (fun (v: Bytes.t libsecp256k1_test) ->
        let msg = SHA2_256.hash v.msg in
        let pk = Option.get (K256.uncompressed_to_raw v.pk) in
        assert (K256.valid_pk ~pk);
        Alcotest.(check bool "verify" v.valid
                    (K256.verify ~pk ~msg ~signature:v.signature));
        match K256.Libsecp256k1.normalize_signature ~signature:v.signature with
        | Some signature ->
          Alcotest.(check bool "verify" v.valid
                      (K256.Libsecp256k1.verify ~pk ~msg ~signature))
        | None -> Alcotest.fail "Low-S normalization error"
      ) libsecp256k1_tests in
  [ ("Verify", `Quick, test_verify) ]

let tests_ecdsa =
  let test_secret_to_public () =
    List.iter (fun (v: Bytes.t k256_test) ->
        assert (K256.valid_sk ~sk:v.sk);
        let pk = Option.get (K256.secret_to_public ~sk:v.sk) in
        assert (K256.valid_pk ~pk);
        Alcotest.(check bytes "secret_to_public" v.pk pk)) k256_tests in

  let test_sign () =
    List.iter (fun (v: Bytes.t k256_test) ->
        match K256.sign ~sk:v.sk ~msg:v.msg ~k:v.k with
        | Some signature -> Alcotest.(check bytes "sign" signature v.signature)
        | None -> Alcotest.fail "Signing error"
      ) k256_tests in

  let test_verify () =
    List.iter (fun (v: Bytes.t k256_test) ->
        Alcotest.(check bool "verify" true
                    (K256.verify ~pk:v.pk ~msg:v.msg ~signature:v.signature)))
      k256_tests in

  let test_sign_libsecp256k1 () =
    List.iter (fun (v: Bytes.t k256_test) ->
        match K256.Libsecp256k1.sign ~sk:v.sk ~msg:v.msg ~k:v.k with
        | Some signature -> (
            assert (K256.Libsecp256k1.is_signature_normalized ~signature);
            match K256.Libsecp256k1.normalize_signature ~signature:v.signature with
            | Some normalized_signature ->
              Alcotest.(check bytes "Libsecp256k1.sign" normalized_signature v.signature)
            | None -> Alcotest.fail "Low-S normalization error")
        | None -> Alcotest.fail "Signing error"
      ) k256_tests in

  let test_verify_libsecp256k1 () =
    List.iter (fun (v: Bytes.t k256_test) ->
        Alcotest.(check bool "verify" true
                    (K256.Libsecp256k1.verify
                       ~pk:v.pk ~msg:v.msg ~signature:v.signature)))
      k256_tests in

  [
    ("Key generation", `Quick, test_secret_to_public);
    ("Sign", `Quick, test_sign);
    ("Verify", `Quick, test_verify);
    ("Sign (libsecp256k1)", `Quick, test_sign_libsecp256k1);
    ("Verify (libsecp256k1)", `Quick, test_verify_libsecp256k1);
  ]

let tests_point_representation =
  let test_compressed () =
    List.iter (fun (v: Bytes.t k256_test) ->
        let pk_compressed = K256.raw_to_compressed v.pk in
        match K256.compressed_to_raw pk_compressed with
        | Some pk -> Alcotest.(check bytes "compression" pk v.pk)
        | None -> Alcotest.fail "Raw <> compressed error"
      ) k256_tests in

  let test_uncompressed () =
    List.iter (fun (v: Bytes.t k256_test) ->
        let pk_compressed = K256.raw_to_uncompressed v.pk in
        match K256.uncompressed_to_raw pk_compressed with
        | Some pk -> Alcotest.(check bytes "compression" pk v.pk)
        | None -> Alcotest.fail "Raw <> compressed error"
      ) k256_tests in

  [
    ("Compressed", `Quick, test_compressed);
    ("Uncompressed", `Quick, test_uncompressed)
  ]

let tests =
  [
    ("ECDSA", tests_ecdsa);
    ("ECDSA Verification", tests_wycheproof);
    ("Point representation", tests_point_representation)
  ]

let () = Alcotest.run "K-256" tests
