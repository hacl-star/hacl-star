module Test.Vectors.Aes128Gcm

module B = LowStar.Buffer

#set-options "--max_fuel 0 --max_ifuel 0"

let key0: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key0_len: (x:UInt32.t { UInt32.v x = B.length key0 }) =
  16ul

let nonce0: (b: B.buffer UInt8.t { B.length b = 12 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; ] in
  assert_norm (List.Tot.length l = 12);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce0_len: (x:UInt32.t { UInt32.v x = B.length nonce0 }) =
  12ul

let aad0: (b: B.buffer UInt8.t { B.length b = 0 /\ B.recallable b }) =
  [@inline_let] let l = [ ] in
  assert_norm (List.Tot.length l = 0);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let aad0_len: (x:UInt32.t { UInt32.v x = B.length aad0 }) =
  0ul

let input0: (b: B.buffer UInt8.t { B.length b = 0 /\ B.recallable b }) =
  [@inline_let] let l = [ ] in
  assert_norm (List.Tot.length l = 0);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input0_len: (x:UInt32.t { UInt32.v x = B.length input0 }) =
  0ul

let tag0: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x58uy; 0xe2uy; 0xfcuy; 0xceuy; 0xfauy; 0x7euy; 0x30uy; 0x61uy; 0x36uy; 0x7fuy; 0x1duy; 0x57uy; 0xa4uy; 0xe7uy; 0x45uy; 0x5auy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let tag0_len: (x:UInt32.t { UInt32.v x = B.length tag0 }) =
  16ul

let output0: (b: B.buffer UInt8.t { B.length b = 0 /\ B.recallable b }) =
  [@inline_let] let l = [ ] in
  assert_norm (List.Tot.length l = 0);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output0_len: (x:UInt32.t { UInt32.v x = B.length output0 }) =
  0ul

let key1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key1_len: (x:UInt32.t { UInt32.v x = B.length key1 }) =
  16ul

let nonce1: (b: B.buffer UInt8.t { B.length b = 12 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; ] in
  assert_norm (List.Tot.length l = 12);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce1_len: (x:UInt32.t { UInt32.v x = B.length nonce1 }) =
  12ul

let aad1: (b: B.buffer UInt8.t { B.length b = 0 /\ B.recallable b }) =
  [@inline_let] let l = [ ] in
  assert_norm (List.Tot.length l = 0);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let aad1_len: (x:UInt32.t { UInt32.v x = B.length aad1 }) =
  0ul

let input1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input1_len: (x:UInt32.t { UInt32.v x = B.length input1 }) =
  16ul

let tag1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xabuy; 0x6euy; 0x47uy; 0xd4uy; 0x2cuy; 0xecuy; 0x13uy; 0xbduy; 0xf5uy; 0x3auy; 0x67uy; 0xb2uy; 0x12uy; 0x57uy; 0xbduy; 0xdfuy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let tag1_len: (x:UInt32.t { UInt32.v x = B.length tag1 }) =
  16ul

let output1: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x03uy; 0x88uy; 0xdauy; 0xceuy; 0x60uy; 0xb6uy; 0xa3uy; 0x92uy; 0xf3uy; 0x28uy; 0xc2uy; 0xb9uy; 0x71uy; 0xb2uy; 0xfeuy; 0x78uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output1_len: (x:UInt32.t { UInt32.v x = B.length output1 }) =
  16ul

let key2: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key2_len: (x:UInt32.t { UInt32.v x = B.length key2 }) =
  16ul

let nonce2: (b: B.buffer UInt8.t { B.length b = 12 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy; 0xdeuy; 0xcauy; 0xf8uy; 0x88uy; ] in
  assert_norm (List.Tot.length l = 12);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce2_len: (x:UInt32.t { UInt32.v x = B.length nonce2 }) =
  12ul

let aad2: (b: B.buffer UInt8.t { B.length b = 0 /\ B.recallable b }) =
  [@inline_let] let l = [ ] in
  assert_norm (List.Tot.length l = 0);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let aad2_len: (x:UInt32.t { UInt32.v x = B.length aad2 }) =
  0ul

let input2: (b: B.buffer UInt8.t { B.length b = 64 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy; 0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy; 0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy; 0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy; 0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy; 0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy; 0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy; 0xbauy; 0x63uy; 0x7buy; 0x39uy; 0x1auy; 0xafuy; 0xd2uy; 0x55uy; ] in
  assert_norm (List.Tot.length l = 64);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input2_len: (x:UInt32.t { UInt32.v x = B.length input2 }) =
  64ul

let tag2: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x4duy; 0x5cuy; 0x2auy; 0xf3uy; 0x27uy; 0xcduy; 0x64uy; 0xa6uy; 0x2cuy; 0xf3uy; 0x5auy; 0xbduy; 0x2buy; 0xa6uy; 0xfauy; 0xb4uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let tag2_len: (x:UInt32.t { UInt32.v x = B.length tag2 }) =
  16ul

let output2: (b: B.buffer UInt8.t { B.length b = 64 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x42uy; 0x83uy; 0x1euy; 0xc2uy; 0x21uy; 0x77uy; 0x74uy; 0x24uy; 0x4buy; 0x72uy; 0x21uy; 0xb7uy; 0x84uy; 0xd0uy; 0xd4uy; 0x9cuy; 0xe3uy; 0xaauy; 0x21uy; 0x2fuy; 0x2cuy; 0x02uy; 0xa4uy; 0xe0uy; 0x35uy; 0xc1uy; 0x7euy; 0x23uy; 0x29uy; 0xacuy; 0xa1uy; 0x2euy; 0x21uy; 0xd5uy; 0x14uy; 0xb2uy; 0x54uy; 0x66uy; 0x93uy; 0x1cuy; 0x7duy; 0x8fuy; 0x6auy; 0x5auy; 0xacuy; 0x84uy; 0xaauy; 0x05uy; 0x1buy; 0xa3uy; 0x0buy; 0x39uy; 0x6auy; 0x0auy; 0xacuy; 0x97uy; 0x3duy; 0x58uy; 0xe0uy; 0x91uy; 0x47uy; 0x3fuy; 0x59uy; 0x85uy; ] in
  assert_norm (List.Tot.length l = 64);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output2_len: (x:UInt32.t { UInt32.v x = B.length output2 }) =
  64ul

let key3: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let key3_len: (x:UInt32.t { UInt32.v x = B.length key3 }) =
  16ul

let nonce3: (b: B.buffer UInt8.t { B.length b = 12 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy; 0xdeuy; 0xcauy; 0xf8uy; 0x88uy; ] in
  assert_norm (List.Tot.length l = 12);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let nonce3_len: (x:UInt32.t { UInt32.v x = B.length nonce3 }) =
  12ul

let aad3: (b: B.buffer UInt8.t { B.length b = 20 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 0xabuy; 0xaduy; 0xdauy; 0xd2uy; ] in
  assert_norm (List.Tot.length l = 20);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let aad3_len: (x:UInt32.t { UInt32.v x = B.length aad3 }) =
  20ul

let input3: (b: B.buffer UInt8.t { B.length b = 60 /\ B.recallable b }) =
  [@inline_let] let l = [ 0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy; 0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy; 0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy; 0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy; 0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy; 0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy; 0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy; 0xbauy; 0x63uy; 0x7buy; 0x39uy; ] in
  assert_norm (List.Tot.length l = 60);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let input3_len: (x:UInt32.t { UInt32.v x = B.length input3 }) =
  60ul

let tag3: (b: B.buffer UInt8.t { B.length b = 16 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x5buy; 0xc9uy; 0x4fuy; 0xbcuy; 0x32uy; 0x21uy; 0xa5uy; 0xdbuy; 0x94uy; 0xfauy; 0xe9uy; 0x5auy; 0xe7uy; 0x12uy; 0x1auy; 0x47uy; ] in
  assert_norm (List.Tot.length l = 16);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let tag3_len: (x:UInt32.t { UInt32.v x = B.length tag3 }) =
  16ul

let output3: (b: B.buffer UInt8.t { B.length b = 60 /\ B.recallable b }) =
  [@inline_let] let l = [ 0x42uy; 0x83uy; 0x1euy; 0xc2uy; 0x21uy; 0x77uy; 0x74uy; 0x24uy; 0x4buy; 0x72uy; 0x21uy; 0xb7uy; 0x84uy; 0xd0uy; 0xd4uy; 0x9cuy; 0xe3uy; 0xaauy; 0x21uy; 0x2fuy; 0x2cuy; 0x02uy; 0xa4uy; 0xe0uy; 0x35uy; 0xc1uy; 0x7euy; 0x23uy; 0x29uy; 0xacuy; 0xa1uy; 0x2euy; 0x21uy; 0xd5uy; 0x14uy; 0xb2uy; 0x54uy; 0x66uy; 0x93uy; 0x1cuy; 0x7duy; 0x8fuy; 0x6auy; 0x5auy; 0xacuy; 0x84uy; 0xaauy; 0x05uy; 0x1buy; 0xa3uy; 0x0buy; 0x39uy; 0x6auy; 0x0auy; 0xacuy; 0x97uy; 0x3duy; 0x58uy; 0xe0uy; 0x91uy; ] in
  assert_norm (List.Tot.length l = 60);
  B.gcmalloc_of_list HyperStack.root l

inline_for_extraction let output3_len: (x:UInt32.t { UInt32.v x = B.length output3 }) =
  60ul

noeq
type vector = | Vector:
  output: B.buffer UInt8.t { B.recallable output } ->
  output_len: UInt32.t { B.length output = UInt32.v output_len } ->
  tag: B.buffer UInt8.t { B.recallable tag } ->
  tag_len: UInt32.t { B.length tag = UInt32.v tag_len } ->
  input: B.buffer UInt8.t { B.recallable input } ->
  input_len: UInt32.t { B.length input = UInt32.v input_len } ->
  aad: B.buffer UInt8.t { B.recallable aad } ->
  aad_len: UInt32.t { B.length aad = UInt32.v aad_len } ->
  nonce: B.buffer UInt8.t { B.recallable nonce } ->
  nonce_len: UInt32.t { B.length nonce = UInt32.v nonce_len } ->
  key: B.buffer UInt8.t { B.recallable key } ->
  key_len: UInt32.t { B.length key = UInt32.v key_len } ->
  vector

let vectors: (b: B.buffer vector { B.length b = 4 /\ B.recallable b }) =
  [@inline_let] let l = [ 
    Vector output0 output0_len tag0 tag0_len input0 input0_len aad0 aad0_len nonce0 nonce0_len key0 key0_len ;
    Vector output1 output1_len tag1 tag1_len input1 input1_len aad1 aad1_len nonce1 nonce1_len key1 key1_len ;
    Vector output2 output2_len tag2 tag2_len input2 input2_len aad2 aad2_len nonce2 nonce2_len key2 key2_len ;
    Vector output3 output3_len tag3 tag3_len input3 input3_len aad3 aad3_len nonce3 nonce3_len key3 key3_len ;
  ] in
  assert_norm (List.Tot.length l = 4);
  B.gcmalloc_of_list HyperStack.root l

let vectors_len: (x:UInt32.t { UInt32.v x = B.length vectors }) =
  4ul
