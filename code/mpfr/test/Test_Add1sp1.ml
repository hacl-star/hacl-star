open Prims
open Printf

type i32 = FStar_Int32.t
type u32 = FStar_UInt32.t
type u64 = FStar_UInt64.t

let (print_u32 : FStar_UInt32.t -> unit) =
  fun x  ->
    FStar_HyperStack_IO.print_string (Prims.string_of_int (FStar_UInt32.v x));
    FStar_HyperStack_IO.print_string " "
  
let (print_i32 : FStar_Int32.t -> unit) =
  fun x  ->
    FStar_HyperStack_IO.print_string (Prims.string_of_int (FStar_Int32.v x));
    FStar_HyperStack_IO.print_string " "
  
let (print_u64 : FStar_UInt64.t -> unit) =
  fun x  ->
    FStar_HyperStack_IO.print_string (Prims.string_of_int (FStar_UInt64.v x));
    FStar_HyperStack_IO.print_string " "

let file = "test/add1sp1_testdata"

let (rnd_mode : MPFR_RoundingMode.mpfr_rnd_t) = MPFR_RoundingMode.MPFR_RNDN

let (test: string -> unit) =
fun str ->
  let ic = open_in str in
  try 
  while true do
    let line = input_line ic in
    let split = Str.split (Str.regexp " ") in
    let tokens = split line in
    if (String.equal (List.nth tokens 5) "MPFR_RNDN" ||
        String.equal (List.nth tokens 5) "MPFR_RNDZ" ||
        String.equal (List.nth tokens 5) "MPFR_RNDU" ||
        String.equal (List.nth tokens 5) "MPFR_RNDD" ||
        String.equal (List.nth tokens 5) "MPFR_RNDA") then begin
    print_string "Testing: \n";
    print_string line;
    print_string "\n";
    let rnd_mode = (if (String.equal (List.nth tokens 5) "MPFR_RNDN") then MPFR_RoundingMode.MPFR_RNDN
	       else if (String.equal (List.nth tokens 5) "MPFR_RNDZ") then MPFR_RoundingMode.MPFR_RNDZ
	       else if (String.equal (List.nth tokens 5) "MPFR_RNDU") then MPFR_RoundingMode.MPFR_RNDU
	       else if (String.equal (List.nth tokens 5) "MPFR_RNDD") then MPFR_RoundingMode.MPFR_RNDD
	       else MPFR_RoundingMode.MPFR_RNDA) in
    let s    = FStar_Int32.int_to_t   (Prims.parse_int (List.nth tokens 0)) in
    let bp   = FStar_UInt64.uint_to_t (Prims.parse_int (List.nth tokens 1)) in
    let bx   = FStar_Int32.int_to_t   (Prims.parse_int (List.nth tokens 2)) in
    let cp   = FStar_UInt64.uint_to_t (Prims.parse_int (List.nth tokens 3)) in
    let cx   = FStar_Int32.int_to_t   (Prims.parse_int (List.nth tokens 4)) in
    let p    = FStar_UInt32.uint_to_t (Prims.parse_int (List.nth tokens 6)) in
    let rp   = FStar_UInt64.uint_to_t (Prims.parse_int (List.nth tokens 7)) in
    let rx   = FStar_Int32.int_to_t   (Prims.parse_int (List.nth tokens 8)) in
    let flag = FStar_Int32.int_to_t   (Prims.parse_int (List.nth tokens 9)) in
    let bm = FStar_Buffer.createL [bp]  in
    let bs = MPFR_Lib.mk_mpfr_struct p s bx bm  in
    let b = FStar_Buffer.createL [bs]  in
    let cm = FStar_Buffer.createL [cp]  in
    let cs = MPFR_Lib.mk_mpfr_struct p s cx cm  in
    let c = FStar_Buffer.createL [cs]  in
    let af = MPFR_Add1sp1.mpfr_add1sp1 c b c rnd_mode p  in
    let asign = MPFR_Lib.mpfr_SIGN c  in
    let am = MPFR_Lib.mpfr_MANT c  in
    let ap =
      FStar_Buffer.op_Array_Access am
        (FStar_UInt32.uint_to_t (Prims.parse_int "0"))
       in
    let ax = MPFR_Lib.mpfr_EXP c  in
    FStar_HyperStack_IO.print_string "Result: \n";
    print_i32 asign;
    print_u64 ap;
    print_i32 ax;
    print_i32 af;
    if ((FStar_UInt64.eq ap rp) && (FStar_Int32.eq ax rx) && (FStar_Int32.eq asign s) && (FStar_Int32.eq af flag)) then
        print_string "YES!!!\n"
    else begin
        raise Exit;
        print_string "no...\n"
    end
    end
  done;
    close_in ic

    with
    | End_of_file -> 
      close_in ic;
      print_string "\n === Congratulations!!! WE MADE IT!!! ===\n"
      
    | Exit ->
      close_in ic;
      print_string "\n I'm so sorry, but the tests failed...\n"

let _ = test file
