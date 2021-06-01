open Test_utils

type 'a ed25519_test =
  { name: string ; sk: 'a ; pk: 'a ; msg: 'a ; expected_sig: 'a }


let tests = [
  {
    name = "Test 1";
    sk = Bytes.of_string "\x9d\x61\xb1\x9d\xef\xfd\x5a\x60\xba\x84\x4a\xf4\x92\xec\x2c\xc4\x44\x49\xc5\x69\x7b\x32\x69\x19\x70\x3b\xac\x03\x1c\xae\x7f\x60";
    pk = Bytes.of_string "\xd7\x5a\x98\x01\x82\xb1\x0a\xb7\xd5\x4b\xfe\xd3\xc9\x64\x07\x3a\x0e\xe1\x72\xf3\xda\xa6\x23\x25\xaf\x02\x1a\x68\xf7\x07\x51\x1a";
    msg = Bytes.of_string "";
    expected_sig = Bytes.of_string "\xe5\x56\x43\x00\xc3\x60\xac\x72\x90\x86\xe2\xcc\x80\x6e\x82\x8a\x84\x87\x7f\x1e\xb8\xe5\xd9\x74\xd8\x73\xe0\x65\x22\x49\x01\x55\x5f\xb8\x82\x15\x90\xa3\x3b\xac\xc6\x1e\x39\x70\x1c\xf9\xb4\x6b\xd2\x5b\xf5\xf0\x59\x5b\xbe\x24\x65\x51\x41\x43\x8e\x7a\x10\x0b"
  };
  {
    name = "Test 2";
    sk = Bytes.of_string "\x4c\xcd\x08\x9b\x28\xff\x96\xda\x9d\xb6\xc3\x46\xec\x11\x4e\x0f\x5b\x8a\x31\x9f\x35\xab\xa6\x24\xda\x8c\xf6\xed\x4f\xb8\xa6\xfb";
    pk = Bytes.of_string "\x3d\x40\x17\xc3\xe8\x43\x89\x5a\x92\xb7\x0a\xa7\x4d\x1b\x7e\xbc\x9c\x98\x2c\xcf\x2e\xc4\x96\x8c\xc0\xcd\x55\xf1\x2a\xf4\x66\x0c";
    msg = Bytes.of_string "\x72";
    expected_sig = Bytes.of_string "\x92\xa0\x09\xa9\xf0\xd4\xca\xb8\x72\x0e\x82\x0b\x5f\x64\x25\x40\xa2\xb2\x7b\x54\x16\x50\x3f\x8f\xb3\x76\x22\x23\xeb\xdb\x69\xda\x08\x5a\xc1\xe4\x3e\x15\x99\x6e\x45\x8f\x36\x13\xd0\xf1\x1d\x8c\x38\x7b\x2e\xae\xb4\x30\x2a\xee\xb0\x0d\x29\x16\x12\xbb\x0c\x00"
  }
]

module MakeTests (M: SharedDefs.EdDSA) = struct
  let test_noalloc (v: Bytes.t ed25519_test) t =
    let test_result = test_result (t ^ ".Noalloc " ^ v.name) in

    let signature = Test_utils.init_bytes 64 in
    let pk = Test_utils.init_bytes 32 in
    M.Noalloc.secret_to_public ~sk:v.sk ~pk;
    if not (Bytes.equal pk v.pk) then
      test_result Failure "secret_to_public failure";

    M.Noalloc.sign ~sk:v.sk ~msg:v.msg ~signature;
    if Bytes.equal signature v.expected_sig then
      begin
        if M.verify ~pk:v.pk ~msg:v.msg ~signature then
          test_result Success ""
        else
          test_result Failure "verification"
      end
    else
      test_result Failure "signing"

  let test (v: Bytes.t ed25519_test) t =
    let test_result = test_result (t ^ " " ^ v.name) in

    let pk = M.secret_to_public ~sk:v.sk in
    if not (Bytes.equal pk v.pk) then
      test_result Failure "secret_to_public failure";

    let signature = M.sign ~sk:v.sk ~msg:v.msg in
    if Bytes.equal signature v.expected_sig then
      begin
        if M.verify ~pk:v.pk ~msg:v.msg ~signature then
          test_result Success ""
        else
          test_result Failure "verification"
      end
    else
      test_result Failure "signing"

  let run_tests name =
    List.iter (fun v -> test_noalloc v name) tests;
    List.iter (fun v -> test v name) tests
end

(* TODO: tests for expand_keys, sign_expanded *)
let _ =
  let module Tests = MakeTests (EverCrypt.Ed25519) in
  Tests.run_tests "EverCrypt.Ed25519";

  let module Tests = MakeTests (Hacl.Ed25519) in
  Tests.run_tests "Hacl.Ed25519"
