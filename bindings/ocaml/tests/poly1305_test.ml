open Test_utils

type 'a poly1305_test =
  { name: string ; msg: 'a ; key: 'a ; expected: 'a }


(* Poly1305: key=32, tag=16 *)
let tests = [
  { name = "Test 1";
    msg = Bytes.of_string "\x43\x72\x79\x70\x74\x6f\x67\x72\x61\x70\x68\x69\x63\x20\x46\x6f\x72\x75\x6d\x20\x52\x65\x73\x65\x61\x72\x63\x68\x20\x47\x72\x6f\x75\x70";
    key = Bytes.of_string "\x85\xd6\xbe\x78\x57\x55\x6d\x33\x7f\x44\x52\xfe\x42\xd5\x06\xa8\x01\x03\x80\x8a\xfb\x0d\xb2\xfd\x4a\xbf\xf6\xaf\x41\x49\xf5\x1b";
    expected = Bytes.of_string "\xa8\x06\x1d\xc1\x30\x51\x36\xc6\xc2\x2b\x8b\xaf\x0c\x01\x27\xa9"
  }
]


let validate_test (v: Bytes.t poly1305_test) =
  assert (Bytes.length v.key = 32);
  assert (Bytes.length v.expected = 16)


module MakeTests (M: SharedDefs.MAC) = struct
  let test_noalloc (v: Bytes.t poly1305_test) name reqs =
      let test_result = test_result (name ^ " (noalloc) " ^ v.name) in
      if supports reqs then begin
        let tag = Test_utils.init_bytes 16 in
        M.Noalloc.mac ~key:v.key ~msg:v.msg ~tag;
        if Bytes.equal tag v.expected then
          test_result Success ""
        else
          test_result Failure "MAC mismatch"
      end else
        test_result Skipped "Required CPU feature not detected"

  let test (v: Bytes.t poly1305_test) name reqs =
      let test_result = test_result (name ^ " " ^ v.name) in
      if supports reqs then begin
        let tag = M.mac ~key:v.key ~msg:v.msg in
        if Bytes.equal tag v.expected then
          test_result Success ""
        else
          test_result Failure "MAC mismatch"
      end else
        test_result Skipped "Required CPU feature not detected"

  let run_tests name reqs =
    List.iter (fun v -> test v name reqs) tests;
    List.iter (fun v -> test_noalloc v name reqs) tests
end


let _ =
  List.iter validate_test tests;

  let module Tests = MakeTests (Hacl.Poly1305_32) in
  Tests.run_tests "Hacl.Poly1305_32" [];

  let module Tests = MakeTests (Hacl.Poly1305_128) in
  Tests.run_tests "Hacl.Poly1305_128" [VEC128];

  let module Tests = MakeTests (Hacl.Poly1305_256) in
  Tests.run_tests "Hacl.Poly1305_256" [VEC256];

  let module Tests = MakeTests (EverCrypt.Poly1305) in
  Tests.run_tests "EverCrypt.Poly1305" []
