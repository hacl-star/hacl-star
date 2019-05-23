module Hacl.Test.HE

open C.Failure
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.HE.GM
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Addition


inline_for_extraction unfold noextract
let print_str x = C.String.print (C.String.of_literal x)

inline_for_extraction unfold noextract
let print_strln x = print_str (x ^ "\n")

inline_for_extraction unfold noextract
val print_bool: b:bool -> St unit
let print_bool b =
  C.String.print (if b then C.String.of_literal "true\n" else C.String.of_literal "false\n")

inline_for_extraction unfold noextract
val toBuffer:
    size:size_t ->
    l:list uint64 ->
    Stack (lbuffer uint64 size) (requires fun h -> true) (ensures fun h0 b h1 -> live h1 b)
let toBuffer size l =
  admit();
  createL (normalize_term l)

val test1: unit -> St unit
let test1 _ =
  let list1 =
    toBuffer 16ul (normalize_term (List.Tot.map u64
      [0xa5; 0x6e; 0x4a; 0x0e; 0x70; 0x10; 0x17; 0x58; 0x9a; 0x51; 0x87; 0xdc; 0x7e; 0xa8; 0x41; 0xd1]))
      in

  let list2 =
    toBuffer 16ul (normalize_term (List.Tot.map u64
      [0x00; 0x11; 0x22; 0x33; 0x44; 0x55; 0x66; 0x77; 0x9a; 0x51; 0x87; 0xdc; 0x7e; 0xa8; 0x41; 0xd1]))
      in

  let list3 =
    toBuffer 16ul (normalize_term (List.Tot.map u64
      [0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00]))
      in

  let _ = bn_add 16ul list1 16ul list2 list3 in
  let res = bn_is_less 16ul list1 16ul list3 in
  print_bool res

val main: unit -> St C.exit_code
let main () =
  print_strln "\n ====== Sample: ====== \n";
  test1 ();
  print_strln "\n ===================== \n";
  C.EXIT_SUCCESS
