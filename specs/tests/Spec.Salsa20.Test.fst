module Spec.Salsa20.Test

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.Salsa20

(* TESTS: https://cr.yp.to/snuffle/spec.pdf *)

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"


let test_quarter_round () =
  let expected1_l = List.Tot.map u32_from_UInt32 [0ul; 0ul; 0ul; 0ul] in
  let expected2_l = List.Tot.map u32_from_UInt32 [0x08008145ul; 0x80ul; 0x010200ul; 0x20500000ul] in
  assert_norm (List.Tot.length expected1_l = 4);
  assert_norm (List.Tot.length expected2_l = 4);
  let expected1 : lseq uint32 4 = of_list expected1_l in
  let expected2 : lseq uint32 4 = of_list expected2_l in

  let st = create 16 (u32 0) in
  let st1 = quarter_round 0 1 2 3 st in
  let st2 = quarter_round 0 1 2 3 (upd st 0 (u32 1)) in
  let computed1: lseq uint32 4 = slice st1 0 4 in
  let computed2: lseq uint32 4 = slice st2 0 4 in
  let res1 = for_all2 (fun a b -> uint_to_nat #U32 a = uint_to_nat #U32 b) computed1 expected1 in
  let res2 = for_all2 (fun a b -> uint_to_nat #U32 a = uint_to_nat #U32 b) computed2 expected2 in
  res1 && res2


let test_row_round () =
  let expected_l = List.Tot.map u32_from_UInt32 [
    0x08008145ul; 0x00000080ul; 0x00010200ul; 0x20500000ul;
    0x20100001ul; 0x00048044ul; 0x00000080ul; 0x00010000ul;
    0x00000001ul; 0x00002000ul; 0x80040000ul; 0x00000000ul;
    0x00000001ul; 0x00000200ul; 0x00402000ul; 0x88000100ul ] in
  assert_norm (List.Tot.length expected_l = 16);
  let expected : lseq uint32 16 = of_list expected_l in

  let st = create 16 (u32 0) in
  let st = upd st 0 (u32 1) in
  let st = upd st 4 (u32 1) in
  let st = upd st 8 (u32 1) in
  let st = upd st 12 (u32 1) in
  let st = row_round st in
  for_all2 (fun a b -> uint_to_nat #U32 a = uint_to_nat #U32 b) st expected


let test_column_round () =
  let expected_l = List.Tot.map u32_from_UInt32 [
    0x10090288ul; 0x00000000ul; 0x00000000ul; 0x00000000ul;
    0x00000101ul; 0x00000000ul; 0x00000000ul; 0x00000000ul;
    0x00020401ul; 0x00000000ul; 0x00000000ul; 0x00000000ul;
    0x40a04001ul; 0x00000000ul; 0x00000000ul; 0x00000000ul] in
  assert_norm (List.Tot.length expected_l = 16);
  let expected : lseq uint32 16 = of_list expected_l in

  let st = create 16 (u32 0) in
  let st = upd st 0 (u32 1) in
  let st = upd st 4 (u32 1) in
  let st = upd st 8 (u32 1) in
  let st = upd st 12 (u32 1) in
  let st = column_round st in
  for_all2 (fun a b -> uint_to_nat #U32 a = uint_to_nat #U32 b) st expected


let test_column_round2 () =
  let expected_l = List.Tot.map u32_from_UInt32 [
    0x8c9d190aul; 0xce8e4c90ul; 0x1ef8e9d3ul; 0x1326a71aul;
    0x90a20123ul; 0xead3c4f3ul; 0x63a091a0ul; 0xf0708d69ul;
    0x789b010cul; 0xd195a681ul; 0xeb7d5504ul; 0xa774135cul;
    0x481c2027ul; 0x53a8e4b5ul; 0x4c1f89c5ul; 0x3f78c9c8ul] in
  assert_norm (List.Tot.length expected_l = 16);
  let expected : lseq uint32 16 = of_list expected_l in


  let st0_l = List.Tot.map u32_from_UInt32 [
    0x08521bd6ul; 0x1fe88837ul; 0xbb2aa576ul; 0x3aa26365ul;
    0xc54c6a5bul; 0x2fc74c2ful; 0x6dd39cc3ul; 0xda0a64f6ul;
    0x90a2f23dul; 0x067f95a6ul; 0x06b35f61ul; 0x41e4732eul;
    0xe859c100ul; 0xea4d84b7ul; 0x0f619bfful; 0xbc6e965aul] in
  assert_norm (List.Tot.length st0_l = 16);
  let st0 : lseq uint32 16 = of_list st0_l in

  let st = column_round st0 in
  for_all2 (fun a b -> uint_to_nat #U32 a = uint_to_nat #U32 b) st expected


let test_salsa20_core () =
  let inp_l = List.Tot.map u8_from_UInt8 [
    211uy; 159uy;  13uy; 115uy;  76uy;  55uy;  82uy; 183uy;
      3uy; 117uy; 222uy;  37uy; 191uy; 187uy; 234uy; 136uy;
     49uy; 237uy; 179uy;  48uy;   1uy; 106uy; 178uy; 219uy;
    175uy; 199uy; 166uy;  48uy;  86uy;  16uy; 179uy; 207uy;
     31uy; 240uy;  32uy;  63uy;  15uy;  83uy;  93uy; 161uy;
    116uy; 147uy;  48uy; 113uy; 238uy;  55uy; 204uy;  36uy;
     79uy; 201uy; 235uy;  79uy;   3uy;  81uy; 156uy;  47uy;
    203uy;  26uy; 244uy; 243uy;  88uy; 118uy; 104uy;  54uy ] in
  assert_norm (List.Tot.length inp_l = 64);
  let inp : lseq uint8 64 = of_list inp_l in

  let expected_l = List.Tot.map u8_from_UInt8 [
    109uy;  42uy; 178uy; 168uy; 156uy; 240uy; 248uy; 238uy;
    168uy; 196uy; 190uy; 203uy;  26uy; 110uy; 170uy; 154uy;
     29uy;  29uy; 150uy;  26uy; 150uy;  30uy; 235uy; 249uy;
    190uy; 163uy; 251uy;  48uy;  69uy; 144uy;  51uy;  57uy;
    118uy;  40uy; 152uy; 157uy; 180uy;  57uy;  27uy;  94uy;
    107uy;  42uy; 236uy;  35uy;  27uy; 111uy; 114uy; 114uy;
    219uy; 236uy; 232uy; 135uy; 111uy; 155uy; 110uy;  18uy;
     24uy; 232uy;  95uy; 158uy; 179uy;  19uy;  48uy; 202uy ] in
  assert_norm (List.Tot.length expected_l = 64);
  let expected : lseq uint8 64 = of_list expected_l in


  let st = uints_from_bytes_le #U32 #SEC #16 inp in
  let st = salsa20_core 0 st in
  for_all2 (fun a b -> uint_to_nat #U32 a = uint_to_nat #U32 b) st (uints_from_bytes_le #U32 #SEC #16 expected)


let test () =
  let result = test_quarter_round () &&
  test_row_round () &&
  test_column_round () &&
  test_column_round2 () &&
  test_salsa20_core () in
  if result then begin IO.print_string "\nSuccess!\n"; true end
  else begin IO.print_string "\nFailure :("; false end
