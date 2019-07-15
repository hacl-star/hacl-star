module Test.Vectors.Aes128

module B = LowStar.Buffer

#set-options "--max_fuel 0 --max_ifuel 0"

let input0: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x53uy; 0x69uy; 0x6Euy; 0x67uy; 0x6Cuy; 0x65uy; 0x20uy; 0x62uy; 0x6Cuy; 0x6Fuy; 0x63uy; 0x6Buy; 0x20uy; 0x6Duy; 0x73uy; 0x67uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input0_len: (x:UInt32.t { UInt32.v x = B.length input0 }) =
  16ul

let key0: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xAEuy; 0x68uy; 0x52uy; 0xF8uy; 0x12uy; 0x10uy; 0x67uy; 0xCCuy; 0x4Buy; 0xF7uy; 0xA5uy; 0x76uy; 0x55uy; 0x77uy; 0xF3uy; 0x9Euy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key0_len: (x:UInt32.t { UInt32.v x = B.length key0 }) =
  16ul

let nonce0: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x30uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce0_len: (x:UInt32.t { UInt32.v x = B.length nonce0 }) =
  16ul

let counter0: (b: B.buffer UInt8.t { B.length b = 4 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x01uy; ] in
  assert_norm (List.Tot.length l = 4);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let counter0_len: (x:UInt32.t { UInt32.v x = B.length counter0 }) =
  4ul

let output0: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xE4uy; 0x09uy; 0x5Duy; 0x4Fuy; 0xB7uy; 0xA7uy; 0xB3uy; 0x79uy; 0x2Duy; 0x61uy; 0x75uy; 0xA3uy; 0x26uy; 0x13uy; 0x11uy; 0xB8uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output0_len: (x:UInt32.t { UInt32.v x = B.length output0 }) =
  16ul

let input1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x6buy; 0xc1uy; 0xbeuy; 0xe2uy; 0x2euy; 0x40uy; 0x9fuy; 0x96uy; 0xe9uy; 0x3duy; 0x7euy; 0x11uy; 0x73uy; 0x93uy; 0x17uy; 0x2auy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input1_len: (x:UInt32.t { UInt32.v x = B.length input1 }) =
  16ul

let key1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x2buy; 0x7euy; 0x15uy; 0x16uy; 0x28uy; 0xaeuy; 0xd2uy; 0xa6uy; 0xabuy; 0xf7uy; 0x15uy; 0x88uy; 0x09uy; 0xcfuy; 0x4fuy; 0x3cuy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key1_len: (x:UInt32.t { UInt32.v x = B.length key1 }) =
  16ul

let nonce1: (b: B.buffer UInt8.t { B.length b = 12 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xf0uy; 0xf1uy; 0xf2uy; 0xf3uy; 0xf4uy; 0xf5uy; 0xf6uy; 0xf7uy; 0xf8uy; 0xf9uy; 0xfauy; 0xfbuy; ] in
  assert_norm (List.Tot.length l = 12);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce1_len: (x:UInt32.t { UInt32.v x = B.length nonce1 }) =
  12ul

let counter1: (b: B.buffer UInt8.t { B.length b = 4 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xfcuy; 0xfduy; 0xfeuy; 0xffuy; ] in
  assert_norm (List.Tot.length l = 4);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let counter1_len: (x:UInt32.t { UInt32.v x = B.length counter1 }) =
  4ul

let output1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x87uy; 0x4duy; 0x61uy; 0x91uy; 0xb6uy; 0x20uy; 0xe3uy; 0x26uy; 0x1buy; 0xefuy; 0x68uy; 0x64uy; 0x99uy; 0x0duy; 0xb6uy; 0xceuy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output1_len: (x:UInt32.t { UInt32.v x = B.length output1 }) =
  16ul

let input2: (b: B.buffer UInt8.t { B.length b = 32 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy; 0x09uy; 0x0Auy; 0x0Buy; 0x0Cuy; 0x0Duy; 0x0Euy; 0x0Fuy; 0x10uy; 0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy; 0x18uy; 0x19uy; 0x1Auy; 0x1Buy; 0x1Cuy; 0x1Duy; 0x1Euy; 0x1Fuy; ] in
  assert_norm (List.Tot.length l = 32);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input2_len: (x:UInt32.t { UInt32.v x = B.length input2 }) =
  32ul

let key2: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x7Euy; 0x24uy; 0x06uy; 0x78uy; 0x17uy; 0xFAuy; 0xE0uy; 0xD7uy; 0x43uy; 0xD6uy; 0xCEuy; 0x1Fuy; 0x32uy; 0x53uy; 0x91uy; 0x63uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key2_len: (x:UInt32.t { UInt32.v x = B.length key2 }) =
  16ul

let nonce2: (b: B.buffer UInt8.t { B.length b = 12 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x6Cuy; 0xB6uy; 0xDBuy; 0xC0uy; 0x54uy; 0x3Buy; 0x59uy; 0xDAuy; 0x48uy; 0xD9uy; 0x0Buy; ] in
  assert_norm (List.Tot.length l = 12);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce2_len: (x:UInt32.t { UInt32.v x = B.length nonce2 }) =
  12ul

let counter2: (b: B.buffer UInt8.t { B.length b = 4 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x01uy; ] in
  assert_norm (List.Tot.length l = 4);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let counter2_len: (x:UInt32.t { UInt32.v x = B.length counter2 }) =
  4ul

let output2: (b: B.buffer UInt8.t { B.length b = 32 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x51uy; 0x04uy; 0xA1uy; 0x06uy; 0x16uy; 0x8Auy; 0x72uy; 0xD9uy; 0x79uy; 0x0Duy; 0x41uy; 0xEEuy; 0x8Euy; 0xDAuy; 0xD3uy; 0x88uy; 0xEBuy; 0x2Euy; 0x1Euy; 0xFCuy; 0x46uy; 0xDAuy; 0x57uy; 0xC8uy; 0xFCuy; 0xE6uy; 0x30uy; 0xDFuy; 0x91uy; 0x41uy; 0xBEuy; 0x28uy; ] in
  assert_norm (List.Tot.length l = 32);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output2_len: (x:UInt32.t { UInt32.v x = B.length output2 }) =
  32ul

noeq
type vector = | Vector:
  output: B.buffer UInt8.t { B.recallable output } ->
  output_len: UInt32.t { B.length output = UInt32.v output_len } ->
  counter: B.buffer UInt8.t { B.recallable counter } ->
  counter_len: UInt32.t { B.length counter = UInt32.v counter_len } ->
  nonce: B.buffer UInt8.t { B.recallable nonce } ->
  nonce_len: UInt32.t { B.length nonce = UInt32.v nonce_len } ->
  key: B.buffer UInt8.t { B.recallable key } ->
  key_len: UInt32.t { B.length key = UInt32.v key_len } ->
  input: B.buffer UInt8.t { B.recallable input } ->
  input_len: UInt32.t { B.length input = UInt32.v input_len } ->
  vector

let vectors: (b: B.buffer vector { B.length b = 3 /\ B.recallable b }) =
  [@inline_let] let l = [ 
    Vector output0 output0_len counter0 counter0_len nonce0 nonce0_len key0 key0_len input0 input0_len ;
    Vector output1 output1_len counter1 counter1_len nonce1 nonce1_len key1 key1_len input1 input1_len ;
    Vector output2 output2_len counter2 counter2_len nonce2 nonce2_len key2 key2_len input2 input2_len ;
  ] in
  assert_norm (List.Tot.length l = 3);
  B.gcmalloc_of_list HyperStack.root l

let vectors_len: (x:UInt32.t { UInt32.v x = B.length vectors }) =
  3ul
