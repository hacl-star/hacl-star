module Hacl.Test.HE

open C.Failure
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.HE.GM
open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Addition

module B = FStar.Bytes


inline_for_extraction unfold noextract
val print_str: string -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_str x = C.String.print (C.String.of_literal x)

inline_for_extraction unfold noextract
val print_strln: string -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_strln x = print_str (x ^ "\n")

inline_for_extraction unfold noextract
val print_bool: b:bool -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_bool b =
  C.String.print (if b then C.String.of_literal "true\n" else C.String.of_literal "false\n")

val test1: unit -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test1 _ =
  push_frame();
  //let nat1:nat = 123456781234567812345678 in
  let list1:lbignum 1ul = nat_to_bignum_exact 100 in
  let list2:lbignum 1ul = nat_to_bignum_exact 200 in
  let list3:lbignum 1ul = nat_to_bignum_exact 0 in
  let list4:lbignum 1ul = nat_to_bignum_exact 299 in
  let list5:lbignum 1ul = nat_to_bignum_exact 300 in

  print_strln "Both should be true:";

  let _ = bn_add list1 list2 list3 in
  let res = bn_is_less list4 list3 in
  print_bool (res = true);

  let _ = bn_add list1 list2 list3 in
  let res = bn_is_less list5 list3 in
  print_bool (res = false);

  pop_frame()

val test2: unit -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test2 _ =
  push_frame();
  //let nat1:nat = 123456781234567812345678 in
  let list1:lbignum 2ul = nat_to_bignum_exact 100000000000000000000 in
  let list2:lbignum 2ul = nat_to_bignum_exact 200000000000000000000 in
  let list3:lbignum 2ul = nat_to_bignum_exact 200000000000000000000 in
  let list4:lbignum 2ul = nat_to_bignum_exact 299000000000000000000 in
  let list5:lbignum 2ul = nat_to_bignum_exact 300000000000000000000 in

  print_strln "Both should be true:";

  let _ = bn_add list1 list2 list3 in
  let res = bn_is_less list4 list3 in
  print_bool (res = true);

  let _ = bn_add list1 list2 list3 in
  let res = bn_is_less list5 list3 in
  print_bool (res = false);

  pop_frame()

val main: unit -> St C.exit_code
let main () =
  print_strln "\n====== Sample: ======";
  test1 ();
  test2 ();
  print_strln "=====================";
  C.EXIT_SUCCESS
