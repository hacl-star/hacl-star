module Spec.SHA2

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

#set-options "--z3rlimit  25"

(* Aliasing for operators *)
let op_String_Access = index
let op_String_Assignment = upd

(* Definition: Hash algorithm parameters *)
noeq type parameters =
  | MkParameters:
    wt:       inttype{wt = U32 \/ wt = U64} ->
	 opTable:  lseq (rotval wt) 12 ->
	 kSize:    size_nat{kSize > 16} ->
	 kTable:   intseq wt kSize ->
	 h0:       intseq wt 8 ->
	 size_hash: nat {0 < size_hash /\ size_hash <= 8 * numbytes wt} ->
	 parameters

(* Definition: Base types *)
type lbytes (s:size_nat) = intseq U8 s
type rotval (t:inttype) = r:uint32{uint_v #U32 r > 0 /\ uint_v #U32 r < bits t}

(* Definition: Type for the total length encoded in the padding *)
let lenType p = match p.wt with
| U32 -> U64
| U64 -> U128

(* Definition: Number of bytes required to store the total length *)
let lenSize p = numbytes (lenType p)

(* Definition of permutation functions *)
let _Ch p x y z = ((x &. y) ^. ((~. x) &. z))
let _Maj p x y z = (x &. y) ^. ((x &. z) ^. (y &. z))
let _Sigma0 p (x:uint_t p.wt) = (x >>>. p.opTable.[0]) ^. ((x >>>. p.opTable.[1]) ^. (x >>>. p.opTable.[2]))
let _Sigma1 p (x:uint_t p.wt) = (x >>>. p.opTable.[3]) ^. ((x >>>. p.opTable.[4]) ^. (x >>>. p.opTable.[5]))
let _sigma0 p (x:uint_t p.wt) = (x >>>. p.opTable.[6]) ^. ((x >>>. p.opTable.[7]) ^. (x >>. p.opTable.[8]))
let _sigma1 p (x:uint_t p.wt) = (x >>>. p.opTable.[9]) ^. ((x >>>. p.opTable.[10]) ^. (x >>. p.opTable.[11]))

(* Definition: Algorithm constants *)
let size_block_w = 16
let size_hash_w = 8
let size_block p :size_nat = size_block_w * numbytes p.wt

(* Definition: Maximum input size in bytes *)
let max_input p : n:nat = (maxint (lenType p) + 1) / 8

(* Definition: Types for block and hash as sequences of words *)
type block_w p = b:intseq p.wt 16
type hash_w p = b:intseq p.wt size_hash_w

(* Definition of the scheduling function (part 1) *)
let step_ws0 p (b:block_w p) (i:size_nat{i >= 0 /\ i < 16}) (s:intseq p.wt p.kSize) : (t:intseq p.wt p.kSize) =
  s.[i] <- b.[i]

(* Definition of the scheduling function (part 2) *)
let step_ws1 p (i:size_nat{i >= 16 /\ i < p.kSize}) (s:intseq p.wt p.kSize) : (t:intseq p.wt p.kSize) =
  let t16 = s.[i - 16] in
  let t15 = s.[i - 15] in
  let t7  = s.[i - 7] in
  let t2  = s.[i - 2] in
  let s1 = _sigma1 p t2 in
  let s0 = _sigma0 p t15 in
  s.[i] <- s1 +. (t7 +. (s0 +. t16))

(* Definition of the core scheduling function *)
let ws p (b:block_w p) =
  let s = create p.kSize (nat_to_uint #p.wt 0) in
  let s = repeati 16 (step_ws0 p b) s in
  let s = repeati (p.kSize - 16) (fun i -> step_ws1 p (i + 16)) s in
  s

(* Definition of the core shuffling function *)
let shuffle_core p (wsTable:intseq p.wt p.kSize) (t:size_nat{t < p.kSize}) (hash:hash_w p) : Tot (hash_w p) =
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  let t1 = h0 +. (_Sigma1 p e0) +. ((_Ch p e0 f0 g0) +. (p.kTable.[t] +. wsTable.[t])) in
  let t2 = (_Sigma0 p a0) +. (_Maj p a0 b0 c0) in

  let hash = hash.[0] <- (t1 +. t2) in
  let hash = hash.[1] <- a0 in
  let hash = hash.[2] <- b0 in
  let hash = hash.[3] <- c0 in
  let hash = hash.[4] <- (d0 +. t1) in
  let hash = hash.[5] <- e0 in
  let hash = hash.[6] <- f0 in
  let hash = hash.[7] <- g0 in
  hash

(* Definition of the full shuffling function *)
let shuffle (p:parameters) (wsTable:intseq p.wt p.kSize) (hash:hash_w p) : Tot (hash_w p) =
  repeati p.kSize (shuffle_core p wsTable) hash

(* Definition of the initialization function for convenience *)
let init (p:parameters) = p.h0

(* Definition of the core compression function *)
let update_block (p:parameters) (block:lbytes (size_block p)) (hash:hash_w p) : Tot (hash_w p) =
  let wsTable = ws p (uints_from_bytes_be block) in
  let hash1 = shuffle p wsTable hash in
  map2 (fun x y -> x +. y) hash hash1

(* Definition of the compression function iterated over multiple blocks *)
let update_multi (p:parameters) (n:size_nat{n * size_block p <= max_size_t}) (blocks:lbytes (n * size_block p)) (hash:hash_w p) : Tot (hash_w p) =
  let bl = size_block p in
  repeati n (fun i -> update_block p (sub blocks (bl * i) bl)) hash

(* Definition of the function returning the number of padding blocks for a single input block *)
let number_blocks_padding_single p (len:size_nat{len < size_block p}) : size_nat =
  if len < size_block p - numbytes (lenType p) then 1 else 2

(* Definition of the function returning the number of padding blocks *)
let number_blocks_padding p (len:size_nat{len < max_input p}) : size_nat =
  let n = len / size_block p in
  let r = len % size_block p in
  let nr = number_blocks_padding_single p r in
  n + nr

(* Definition of the padding function for a single input block *)
let pad_single p (n:size_nat) (len:size_nat{len < size_block p /\ len + n * size_block p <= max_input p}) (last:lbytes len)
: Tot (block:lbytes (size_block p * number_blocks_padding_single p len)) =
  let nr = number_blocks_padding_single p len in
  let plen : size_nat = nr * size_block p in
  // Create the padding and copy the partial block inside
  let padding : lbytes plen = create plen (u8 0) in
  let padding = repeati len (fun i s -> s.[i] <- last.[i]) padding in
  // Write the 0x80 byte and the zeros in the padding
  let padding = padding.[len] <- u8 0x80 in
  // Encode and write the total length in bits at the end of the padding
  let tlen = n * size_block p + len in
  let tlenbits = tlen * 8 in
  let x = nat_to_uint #(lenType p) tlenbits in
  let encodedlen = uint_to_bytes_be x in
  let padding = update_slice padding (plen - numbytes (lenType p)) plen encodedlen in
  padding

(* Definition of the padding function *)
let pad p (n:size_nat) (len:size_nat{len < max_input p /\ (size_block p * number_blocks_padding p len) <= max_size_t /\ n + (len / size_block p) <= max_size_t}) (last:lbytes len)
: Tot (block:lbytes (size_block p * number_blocks_padding p len)) =
  let nb = len / size_block p in
  let nr = len % size_block p in
  let plen : size_nat = size_block p * number_blocks_padding p len in
  // Separate the full blocks from the remainder of the data
  // then apply the padding function to the remainder
  let pos_fb = nb * size_block p in
  let rem = slice last pos_fb len in
  let rem_blocks = pad_single p (n + nb) nr rem in
  // Creating the padding and write the last data in the padding
  let padding : lbytes plen = create plen  (u8 0) in
  let padding = update_slice padding 0 pos_fb (slice last 0 pos_fb) in
  let padding = update_slice padding pos_fb plen rem_blocks in
  padding

(* Definition of the function for the partial block compression *)
let update_last p (n:size_nat) (len:size_nat{len < size_block p /\ len + n * size_block p <= max_input p}) (last:lbytes len) (hash:hash_w p)
: Tot (hash_w p) =
  let blocks = pad_single p n len last in
  update_multi p (number_blocks_padding_single p len) blocks hash

(* Definition of the finalization function *)
let finish p (hash:hash_w p) : lbytes p.size_hash =
  let hash_final = uints_to_bytes_be hash in
  let h = slice hash_final 0 p.size_hash in
  h

(* Definition of the SHA2 ontime function based on incremental calls *)
let hash' p (len:size_nat{len < max_input p}) (input:lbytes len) : lbytes p.size_hash =
  let nb = len / size_block p in
  let nr = len % size_block p in
  let nblocks8 = nb * size_block p in
  let l0 = slice input 0 nblocks8 in
  let l1 = slice input nblocks8 len in
  let hash = update_multi p nb l0 p.h0 in
  let hash = update_last p nb nr l1 hash in
  finish p hash

(* Definition of the original SHA2 onetime function *)
let hash p (len:size_nat{len < max_input p /\ (size_block p * number_blocks_padding p len) <= max_size_t}) (input:lbytes len) : lbytes p.size_hash =
  let n = number_blocks_padding p len in
  let blocks = pad p 0 len input in
  finish p (update_multi p n blocks p.h0)




///
/// Parameters for all instances of SHA2
///

let rotval32 (n:nat{n > 0 /\ n < 32}) : rotval U32 = u32 n
let rotval64 (n:nat{n > 0 /\ n < 64}) : rotval U64 = u32 n

let const_224_256_ops = List.Tot.map rotval32 [
    2; 13; 22;
    6; 11; 25;
    7; 18; 3;
    17; 19; 10]

let const_384_512_ops = List.Tot.map rotval64 [
    28; 34; 39;
    14; 18; 41;
    1;   8;  7;
    19; 61;  6]


let const_224_h0 = List.Tot.map u32 [
    0xc1059ed8; 0x367cd507; 0x3070dd17; 0xf70e5939;
    0xffc00b31; 0x68581511; 0x64f98fa7; 0xbefa4fa4]

let const_256_h0 = List.Tot.map u32 [
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a;
    0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19]

let const_384_h0 = List.Tot.map u64 [
    0xcbbb9d5dc1059ed8; 0x629a292a367cd507; 0x9159015a3070dd17; 0x152fecd8f70e5939;
    0x67332667ffc00b31; 0x8eb44a8768581511; 0xdb0c2e0d64f98fa7; 0x47b5481dbefa4fa4]

let const_512_h0 = List.Tot.map u64 [
    0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1;
    0x510e527fade682d1; 0x9b05688c2b3e6c1f; 0x1f83d9abfb41bd6b; 0x5be0cd19137e2179]


let const_224_256_k = List.Tot.map u32 [
    0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
    0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
    0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
    0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
    0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
    0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
    0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
    0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
    0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2]

let const_384_512_k = List.Tot.map u64 [
    0x428a2f98d728ae22; 0x7137449123ef65cd; 0xb5c0fbcfec4d3b2f; 0xe9b5dba58189dbbc;
    0x3956c25bf348b538; 0x59f111f1b605d019; 0x923f82a4af194f9b; 0xab1c5ed5da6d8118;
    0xd807aa98a3030242; 0x12835b0145706fbe; 0x243185be4ee4b28c; 0x550c7dc3d5ffb4e2;
    0x72be5d74f27b896f; 0x80deb1fe3b1696b1; 0x9bdc06a725c71235; 0xc19bf174cf692694;
    0xe49b69c19ef14ad2; 0xefbe4786384f25e3; 0x0fc19dc68b8cd5b5; 0x240ca1cc77ac9c65;
    0x2de92c6f592b0275; 0x4a7484aa6ea6e483; 0x5cb0a9dcbd41fbd4; 0x76f988da831153b5;
    0x983e5152ee66dfab; 0xa831c66d2db43210; 0xb00327c898fb213f; 0xbf597fc7beef0ee4;
    0xc6e00bf33da88fc2; 0xd5a79147930aa725; 0x06ca6351e003826f; 0x142929670a0e6e70;
    0x27b70a8546d22ffc; 0x2e1b21385c26c926; 0x4d2c6dfc5ac42aed; 0x53380d139d95b3df;
    0x650a73548baf63de; 0x766a0abb3c77b2a8; 0x81c2c92e47edaee6; 0x92722c851482353b;
    0xa2bfe8a14cf10364; 0xa81a664bbc423001; 0xc24b8b70d0f89791; 0xc76c51a30654be30;
    0xd192e819d6ef5218; 0xd69906245565a910; 0xf40e35855771202a; 0x106aa07032bbd1b8;
    0x19a4c116b8d2d0c8; 0x1e376c085141ab53; 0x2748774cdf8eeb99; 0x34b0bcb5e19b48a8;
    0x391c0cb3c5c95a63; 0x4ed8aa4ae3418acb; 0x5b9cca4f7763e373; 0x682e6ff3d6b2b8a3;
    0x748f82ee5defb2fc; 0x78a5636f43172f60; 0x84c87814a1f0ab72; 0x8cc702081a6439ec;
    0x90befffa23631e28; 0xa4506cebde82bde9; 0xbef9a3f7b2c67915; 0xc67178f2e372532b;
    0xca273eceea26619c; 0xd186b8c721c0c207; 0xeada7dd6cde0eb1e; 0xf57d4f7fee6ed178;
    0x06f067aa72176fba; 0x0a637dc5a2c898a6; 0x113f9804bef90dae; 0x1b710b35131c471b;
    0x28db77f523047d84; 0x32caab7b40c72493; 0x3c9ebe0a15c9bebc; 0x431d67c49c100d4c;
    0x4cc5d4becb3e42b6; 0x597f299cfc657e2a; 0x5fcb6fab3ad6faec; 0x6c44198c4a475817]


let parameters224 : parameters =
  assert_norm(List.Tot.length const_224_h0 = 8);
  assert_norm(List.Tot.length const_224_256_ops = 12);
  assert_norm(List.Tot.length const_224_256_k = 64);
  MkParameters
    U32
    (createL const_224_256_ops)
    64
    (createL const_224_256_k)
    (createL const_224_h0)
    28

let parameters256 : parameters =
  assert_norm(List.Tot.length const_256_h0 = 8);
  assert_norm(List.Tot.length const_224_256_ops = 12);
  assert_norm(List.Tot.length const_224_256_k = 64);
  MkParameters
    U32
    (createL const_224_256_ops)
    64
    (createL const_224_256_k)
    (createL const_256_h0)
    32

let parameters384 : parameters =
  assert_norm(List.Tot.length const_384_h0 = 8);
  assert_norm(List.Tot.length const_384_512_ops = 12);
  assert_norm(List.Tot.length const_384_512_k = 80);
  MkParameters
    U64
    (createL const_384_512_ops)
    80
    (createL const_384_512_k)
    (createL const_384_h0)
    48

let parameters512 : parameters =
  assert_norm(List.Tot.length const_512_h0 = 8);
  assert_norm(List.Tot.length const_384_512_ops = 12);
  assert_norm(List.Tot.length const_384_512_k = 80);
  MkParameters
    U64
    (createL const_384_512_ops)
    80
    (createL const_384_512_k)
    (createL const_512_h0)
    64

///
/// Instances of SHA2
///

let hash_w224 = hash_w parameters224
let hash_w256 = hash_w parameters256
let hash_w384 = hash_w parameters384
let hash_w512 = hash_w parameters512

let size_block224 = size_block parameters224
let size_block256 = size_block parameters256
let size_block384 = size_block parameters384
let size_block512 = size_block parameters512

let size_hash224 = parameters224.size_hash
let size_hash256 = parameters256.size_hash
let size_hash384 = parameters384.size_hash
let size_hash512 = parameters512.size_hash

let max_input224 = max_input parameters224
let max_input256 = max_input parameters256
let max_input384 = max_input parameters384
let max_input512 = max_input parameters512

let init224 = init parameters224
let init256 = init parameters256
let init384 = init parameters384
let init512 = init parameters512

let update_block224 = update_block parameters224
let update_block256 = update_block parameters256
let update_block384 = update_block parameters384
let update_block512 = update_block parameters512

let update_multi224 = update_multi parameters224
let update_multi256 = update_multi parameters256
let update_multi384 = update_multi parameters384
let update_multi512 = update_multi parameters512

let update_last224 = update_last parameters224
let update_last256 = update_last parameters256
let update_last384 = update_last parameters384
let update_last512 = update_last parameters512

let finish224 = finish parameters224
let finish256 = finish parameters256
let finish384 = finish parameters384
let finish512 = finish parameters512

let hash224 = hash' parameters224
let hash256 = hash' parameters256
let hash384 = hash' parameters384
let hash512 = hash' parameters512
