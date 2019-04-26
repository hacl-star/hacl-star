module Hacl.Test.AES_256_CBC

open FStar.HyperStack.All

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Hacl.Impl.AES_256_CBC

#set-options "--max_fuel 0 --max_ifuel 0"


inline_for_extraction noextract let key1_list : l:list uint8{List.Tot.Base.length l == 32} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x60uy; 0x3duy; 0xebuy; 0x10uy; 0x15uy; 0xcauy; 0x71uy; 0xbeuy;
    0x2buy; 0x73uy; 0xaeuy; 0xf0uy; 0x85uy; 0x7duy; 0x77uy; 0x81uy;
    0x1fuy; 0x35uy; 0x2cuy; 0x07uy; 0x3buy; 0x61uy; 0x08uy; 0xd7uy;
    0x2duy; 0x98uy; 0x10uy; 0xa3uy; 0x09uy; 0x14uy; 0xdfuy; 0xf4uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 32);
  normalize_term(l)
noextract let key1_seq : Lib.Sequence.lseq uint8 32 =
  Lib.Sequence.createL key1_list
let key1 : b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b key1_seq
} =
  createL_global key1_list

inline_for_extraction noextract let iv1_list : l:list uint8{List.Tot.Base.length l == 16} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy;
    0x08uy; 0x09uy; 0x0Auy; 0x0Buy; 0x0Cuy; 0x0Duy; 0x0Euy; 0x0Fuy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 16);
  normalize_term(l)
noextract let iv1_seq : Lib.Sequence.lseq uint8 16 =
  Lib.Sequence.createL iv1_list
let iv1 : b:ilbuffer uint8 (size 16){
  recallable b /\ witnessed b iv1_seq
} =
  createL_global iv1_list


inline_for_extraction noextract let input1_list : l:list uint8{List.Tot.Base.length l == 16} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x6buy; 0xc1uy; 0xbeuy; 0xe2uy; 0x2euy; 0x40uy; 0x9fuy; 0x96uy;
    0xe9uy; 0x3duy; 0x7euy; 0x11uy; 0x73uy; 0x93uy; 0x17uy; 0x2auy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 16);
  normalize_term(l)
noextract let input1_seq : Lib.Sequence.lseq uint8 16 =
  Lib.Sequence.createL input1_list
let input1 : b:ilbuffer uint8 (size 16){
  recallable b /\ witnessed b input1_seq
} =
  createL_global input1_list

inline_for_extraction noextract let cip1_list : l:list uint8{List.Tot.Base.length l == 16} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0xf5uy; 0x8cuy; 0x4cuy; 0x04uy; 0xd6uy; 0xe5uy; 0xf1uy; 0xbauy;
    0x77uy; 0x9euy; 0xabuy; 0xfbuy; 0x5fuy; 0x7buy; 0xfbuy; 0xd6uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 16);
  normalize_term(l)
noextract let cip1_seq : Lib.Sequence.lseq uint8 16 =
  Lib.Sequence.createL cip1_list
let cip1 : b:ilbuffer uint8 (size 16){
  recallable b /\ witnessed b cip1_seq
} =
  createL_global cip1_list

inline_for_extraction noextract let key2_list : l:list uint8{List.Tot.Base.length l == 32} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x60uy; 0x3duy; 0xebuy; 0x10uy; 0x15uy; 0xcauy; 0x71uy; 0xbeuy;
    0x2buy; 0x73uy; 0xaeuy; 0xf0uy; 0x85uy; 0x7duy; 0x77uy; 0x81uy;
    0x1fuy; 0x35uy; 0x2cuy; 0x07uy; 0x3buy; 0x61uy; 0x08uy; 0xd7uy;
    0x2duy; 0x98uy; 0x10uy; 0xa3uy; 0x09uy; 0x14uy; 0xdfuy; 0xf4uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 32);
  normalize_term(l)
noextract let key2_seq : Lib.Sequence.lseq uint8 32 =
  Lib.Sequence.createL key2_list
let key2 : b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b key2_seq
} =
  createL_global key2_list


inline_for_extraction noextract let iv2_list : l:list uint8{List.Tot.Base.length l == 16} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy;
    0x08uy; 0x09uy; 0x0Auy; 0x0Buy; 0x0Cuy; 0x0Duy; 0x0Euy; 0x0Fuy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 16);
  normalize_term(l)
noextract let iv2_seq : Lib.Sequence.lseq uint8 16 =
  Lib.Sequence.createL iv2_list
let iv2 : b:ilbuffer uint8 (size 16){
  recallable b /\ witnessed b iv2_seq
} =
  createL_global iv2_list

inline_for_extraction noextract let input2_list : l:list uint8{List.Tot.Base.length l == 64} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x6buy; 0xc1uy; 0xbeuy; 0xe2uy; 0x2euy; 0x40uy; 0x9fuy; 0x96uy;
    0xe9uy; 0x3duy; 0x7euy; 0x11uy; 0x73uy; 0x93uy; 0x17uy; 0x2auy;
    0xaeuy; 0x2duy; 0x8auy; 0x57uy; 0x1euy; 0x03uy; 0xacuy; 0x9cuy;
    0x9euy; 0xb7uy; 0x6fuy; 0xacuy; 0x45uy; 0xafuy; 0x8euy; 0x51uy;
    0x30uy; 0xc8uy; 0x1cuy; 0x46uy; 0xa3uy; 0x5cuy; 0xe4uy; 0x11uy;
    0xe5uy; 0xfbuy; 0xc1uy; 0x19uy; 0x1auy; 0x0auy; 0x52uy; 0xefuy;
    0xf6uy; 0x9fuy; 0x24uy; 0x45uy; 0xdfuy; 0x4fuy; 0x9buy; 0x17uy;
    0xaduy; 0x2buy; 0x41uy; 0x7buy; 0xe6uy; 0x6cuy; 0x37uy; 0x10uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 64);
  normalize_term(l)
noextract let input2_seq : Lib.Sequence.lseq uint8 64 =
  Lib.Sequence.createL input2_list
let input2 : b:ilbuffer uint8 (size 64){
  recallable b /\ witnessed b input2_seq
} =
  createL_global input2_list


inline_for_extraction noextract let cip2_list : l:list uint8{List.Tot.Base.length l == 80} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0xf5uy; 0x8cuy; 0x4cuy; 0x04uy; 0xd6uy; 0xe5uy; 0xf1uy; 0xbauy;
    0x77uy; 0x9euy; 0xabuy; 0xfbuy; 0x5fuy; 0x7buy; 0xfbuy; 0xd6uy;
    0x9cuy; 0xfcuy; 0x4euy; 0x96uy; 0x7euy; 0xdbuy; 0x80uy; 0x8duy;
    0x67uy; 0x9fuy; 0x77uy; 0x7buy; 0xc6uy; 0x70uy; 0x2cuy; 0x7duy;
    0x39uy; 0xf2uy; 0x33uy; 0x69uy; 0xa9uy; 0xd9uy; 0xbauy; 0xcfuy;
    0xa5uy; 0x30uy; 0xe2uy; 0x63uy; 0x04uy; 0x23uy; 0x14uy; 0x61uy;
    0xb2uy; 0xebuy; 0x05uy; 0xe2uy; 0xc3uy; 0x9buy; 0xe9uy; 0xfcuy;
    0xdauy; 0x6cuy; 0x19uy; 0x07uy; 0x8cuy; 0x6auy; 0x9duy; 0x1buy;
    0x3fuy; 0x46uy; 0x17uy; 0x96uy; 0xd6uy; 0xb0uy; 0xd6uy; 0xb2uy;
    0xe0uy; 0xc2uy; 0xa7uy; 0x2buy; 0x4duy; 0x80uy; 0xe6uy; 0x44uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 80);
  normalize_term(l)
noextract let cip2_seq : Lib.Sequence.lseq uint8 80 =
  Lib.Sequence.createL cip2_list
let cip2 : b:ilbuffer uint8 (size 80){
  recallable b /\ witnessed b cip2_seq
} =
  createL_global cip2_list


inline_for_extraction noextract let key3_list : l:list uint8{List.Tot.Base.length l == 32} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x67uy; 0x2duy; 0x38uy; 0xdduy; 0x4buy; 0x90uy; 0xaauy; 0xdeuy;
    0x77uy; 0x68uy; 0x79uy; 0xebuy; 0x9euy; 0x2auy; 0xdauy; 0xc0uy;
    0x56uy; 0x61uy; 0xb5uy; 0x24uy; 0xe0uy; 0x68uy; 0x21uy; 0xc4uy;
    0x34uy; 0xe3uy; 0xecuy; 0x53uy; 0x58uy; 0xd0uy; 0xc8uy; 0xceuy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 32);
  normalize_term(l)
noextract let key3_seq : Lib.Sequence.lseq uint8 32 =
  Lib.Sequence.createL key3_list
let key3 : b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b key3_seq
} =
  createL_global key3_list


inline_for_extraction noextract let iv3_list : l:list uint8{List.Tot.Base.length l == 16} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0xfbuy; 0xffuy; 0xa2uy; 0xa3uy; 0x4euy; 0xe5uy; 0x08uy; 0x38uy;
    0xcbuy; 0xeeuy; 0x1buy; 0x3auy; 0x3cuy; 0xf1uy; 0x3fuy; 0xfcuy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 16);
  normalize_term(l)
noextract let iv3_seq : Lib.Sequence.lseq uint8 16 =
  Lib.Sequence.createL iv3_list
let iv3 : b:ilbuffer uint8 (size 16){
  recallable b /\ witnessed b iv3_seq
} =
  createL_global iv3_list


inline_for_extraction noextract let input3_list : l:list uint8{List.Tot.Base.length l == 159} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x0auy; 0x01uy; 0x41uy; 0x80uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 159);
  normalize_term(l)
noextract let input3_seq : Lib.Sequence.lseq uint8 159 =
  Lib.Sequence.createL input3_list
let input3 : b:ilbuffer uint8 (size 159){
  recallable b /\ witnessed b input3_seq
} =
  createL_global input3_list


inline_for_extraction noextract let cip3_list : l:list uint8{List.Tot.Base.length l == 160} =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x3cuy; 0x5duy; 0x07uy; 0x0duy; 0x1buy; 0x75uy; 0xc4uy; 0x18uy;
    0xceuy; 0xf7uy; 0x69uy; 0xbduy; 0x73uy; 0x78uy; 0xa5uy; 0x89uy;
    0x69uy; 0x53uy; 0x7auy; 0x00uy; 0xe0uy; 0xffuy; 0x60uy; 0xcbuy;
    0xb9uy; 0x9duy; 0xefuy; 0xb4uy; 0x86uy; 0xfcuy; 0xfbuy; 0x43uy;
    0x38uy; 0x42uy; 0x64uy; 0xdauy; 0x4euy; 0xa9uy; 0x82uy; 0x1cuy;
    0x13uy; 0x36uy; 0xf0uy; 0x2duy; 0x98uy; 0x8duy; 0xa3uy; 0x89uy;
    0x44uy; 0x45uy; 0x33uy; 0x31uy; 0xc4uy; 0xb3uy; 0x01uy; 0x81uy;
    0x70uy; 0x4cuy; 0xbcuy; 0xecuy; 0x5auy; 0x79uy; 0x2auy; 0xb8uy;
    0x7cuy; 0x5cuy; 0xcfuy; 0xf2uy; 0x56uy; 0xe0uy; 0xb4uy; 0xd6uy;
    0x1buy; 0xa6uy; 0xa3uy; 0x0auy; 0x69uy; 0x64uy; 0x78uy; 0x38uy;
    0x75uy; 0x01uy; 0x88uy; 0x82uy; 0xe6uy; 0x6buy; 0xfbuy; 0xd9uy;
    0x44uy; 0x5auy; 0xc4uy; 0x4fuy; 0xeeuy; 0x9duy; 0xc6uy; 0x7euy;
    0xdcuy; 0x2auy; 0xd9uy; 0xdeuy; 0x78uy; 0xaduy; 0xbeuy; 0x0euy;
    0xb7uy; 0xe9uy; 0xcbuy; 0x99uy; 0x02uy; 0x72uy; 0x18uy; 0x3cuy;
    0xe5uy; 0xfauy; 0xc6uy; 0x82uy; 0xeeuy; 0x51uy; 0x06uy; 0xf6uy;
    0x7duy; 0x73uy; 0x2cuy; 0xd1uy; 0x6duy; 0xfbuy; 0x73uy; 0x12uy;
    0x39uy; 0x59uy; 0x0buy; 0xa6uy; 0x7duy; 0xc8uy; 0x27uy; 0xe8uy;
    0x49uy; 0xc4uy; 0x9auy; 0x9fuy; 0xb5uy; 0xeduy; 0x8euy; 0xeduy;
    0x41uy; 0xd8uy; 0x5duy; 0x5euy; 0x6duy; 0xe3uy; 0x29uy; 0x4euy;
    0x74uy; 0xf3uy; 0x52uy; 0x4cuy; 0x64uy; 0x89uy; 0xc2uy; 0xf2uy
  ] in
  [@inline_let]
  let l : list uint8 = List.Tot.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.Base.length l == 160);
  normalize_term(l)
noextract let cip3_seq : Lib.Sequence.lseq uint8 160 =
  Lib.Sequence.createL cip3_list
let cip3 : b:ilbuffer uint8 (size 160){
  recallable b /\ witnessed b cip3_seq
} =
  createL_global cip3_list

#set-options "--lax"

val main: unit -> Stack C.exit_code
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  push_frame();
  let comp1 = create (size 32) (u8 0) in
  let _ = Hacl.Impl.AES_256_CBC.aes256_cbc_encrypt
    comp1 key1 iv1 input1 (size 16) in
  TestLib.compare_and_print (C.String.of_literal "AES-CBC encryption 1") cip1 comp1 16ul;
  let dec1 = create (size 32) (u8 0) in
  let len1 = Hacl.Impl.AES_256_CBC.aes256_cbc_decrypt dec1 key1 iv1 comp1 32ul in
  if len1 <> 16ul then C.String.print (C.String.of_literal "incorrect length from decryption\n") else ();
  TestLib.compare_and_print (C.String.of_literal "AES-CBC decryption 1") input1 dec1 16ul;

  let comp2 = create (size 80) (u8 0) in
  let _ = Hacl.Impl.AES_256_CBC.aes256_cbc_encrypt comp2 key2 iv2 input2 64ul in
  TestLib.compare_and_print (C.String.of_literal "AES-CBC encryption 2") cip2 comp2 80ul;
  let dec2 = create (size 80) (u8 0) in
  let len2 = Hacl.Impl.AES_256_CBC.aes256_cbc_decrypt dec2 key2 iv2 comp2 80ul in
  if len2 <> 64ul then C.String.print (C.String.of_literal "incorrect length from decryption\n") else ();
  TestLib.compare_and_print (C.String.of_literal "AES-CBC decryption 2") input2 dec2 64ul;

  let comp3 = create (size 160) (u8 0) in
  let _ = Hacl.Impl.AES_256_CBC.aes256_cbc_encrypt comp3 key3 iv3 input3 159ul in
  TestLib.compare_and_print (C.String.of_literal "AES-CBC encryption 3") cip3 comp3 160ul;
  let dec3 = create (size 160) (u8 0) in
  let len3 = Hacl.Impl.AES_256_CBC.aes256_cbc_decrypt dec3 key3 iv3 comp3 160ul in
  if len3 <> 159ul then C.String.print (C.String.of_literal "incorrect length from decryption\n") else ();
  TestLib.compare_and_print (C.String.of_literal "AES-CBC decryption 3") input3 dec3 159ul;
    pop_frame();
  C.EXIT_SUCCESS
