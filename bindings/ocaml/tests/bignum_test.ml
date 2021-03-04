open Test_utils


let test_bignum256 () =
  let test_result = test_result "Bignum256" in
  let buf = Bytes.of_string "\x01\x02\x03" in
  let buf_padded = Bytes.cat (Bytes.make 29 '\x00') buf in
  let bn = Bignum.Bignum256.from_bytes buf in
  let res = Bignum.Bignum256.to_bytes bn in
  if res = buf_padded then
    test_result Success ""
  else
    Printf.printf "Res: %s\n" (Hex.show (Hex.of_bytes res));
    Printf.printf "Buf: %s\n" (Hex.show (Hex.of_bytes buf_padded));
    test_result Failure ""

(* let test_bignum4096 () =
 *   let test_result = test_result "Bignum4096" in
 *   let buf = Bytes.of_string "\x01\x02\x03" in
 *   let bn = Bignum.Bignum4096.from_bytes buf in
 *   let res = Bignum.Bignum4096.to_bytes bn in
 *   let buf_padded = Bytes.cat (Bytes.make 509 '\x00') buf in
 *   if res = buf_padded then
 *     test_result Success ""
 *   else
 *     Printf.printf "%s\n" (Hex.show (Hex.of_bytes res));
 *     Printf.printf "%s\n" (Hex.show (Hex.of_bytes buf_padded));
 *     test_result Failure "" *)


let _ =
  test_bignum256 ()
