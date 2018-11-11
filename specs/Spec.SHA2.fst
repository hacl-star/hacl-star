module Spec.SHA2

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


#set-options "--z3rlimit  25"

type alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512

inline_for_extraction
unfold let wt (a:alg) =
  match a with
  | SHA2_224 -> U32
  | SHA2_256 -> U32
  | SHA2_384 -> U64
  | SHA2_512 -> U64

inline_for_extraction
unfold let limb_inttype (a:alg) =
  match (wt a) with
  | U32 -> U64
  | U64 -> U128

type word_t (a:alg) = uint_t (wt a) SEC
type pub_word_t (a:alg) = uint_t (wt a) PUB
type limb_t (a:alg) : Type0 = uint_t (limb_inttype a) SEC

inline_for_extraction
let max_limb (a:alg) = maxint (limb_inttype a)

inline_for_extraction
let to_word (a:alg) (x:size_nat) : word_t a =
  match (wt a) with
  | U32 -> u32 x
  | U64 -> u64 x

inline_for_extraction
let to_limb (a:alg) (x:nat{x <= max_limb a}) : limb_t a =
  match (wt a) with
  | U32 -> u64 x
  | U64 -> u128 x

inline_for_extraction
let limb_to_word (a:alg) (x:limb_t a) : word_t a =
  match (wt a) with
  | U32 -> to_u32 x
  | U64 -> to_u64 x


inline_for_extraction let size_opTable: size_nat = 12

[@"opaque_to_smt"]
let opTable_list_224_256: l:List.Tot.llist (rotval U32) 12 =
  [@inline_let]
  let l = [
    size  2; size 13; size 22;
    size  6; size 11; size 25;
    size  7; size 18; size  3;
    size 17; size 19; size 10] in
  assert_norm(List.Tot.length l == 12);
  l

[@"opaque_to_smt"]
let opTable_list_384_512: l:List.Tot.llist (rotval U64) 12 =
  [@inline_let]
  let l = [
    size 28; size 34; size 39;
    size 14; size 18; size 41;
    size  1; size  8; size  7;
    size 19; size 61; size  6] in
  assert_norm(List.Tot.length l == 12);
  l

unfold let opTable_t (a:alg) = lseq (rotval (wt a)) size_opTable

let opTable (a:alg) : opTable_t a =
  match a with
  | SHA2_224 | SHA2_256 -> (of_list opTable_list_224_256)
  | SHA2_384 | SHA2_512 -> (of_list opTable_list_384_512)


inline_for_extraction
let size_kTable (p:alg): size_nat =
  match p with
  | SHA2_224 | SHA2_256 -> 64
  | SHA2_384 | SHA2_512 -> 80

[@"opaque_to_smt"]
let kTable_list_224_256: l:List.Tot.llist uint32 64 =
  [@inline_let]
  let l = [
    u32 0x428a2f98; u32 0x71374491; u32 0xb5c0fbcf; u32 0xe9b5dba5;
    u32 0x3956c25b; u32 0x59f111f1; u32 0x923f82a4; u32 0xab1c5ed5;
    u32 0xd807aa98; u32 0x12835b01; u32 0x243185be; u32 0x550c7dc3;
    u32 0x72be5d74; u32 0x80deb1fe; u32 0x9bdc06a7; u32 0xc19bf174;
    u32 0xe49b69c1; u32 0xefbe4786; u32 0x0fc19dc6; u32 0x240ca1cc;
    u32 0x2de92c6f; u32 0x4a7484aa; u32 0x5cb0a9dc; u32 0x76f988da;
    u32 0x983e5152; u32 0xa831c66d; u32 0xb00327c8; u32 0xbf597fc7;
    u32 0xc6e00bf3; u32 0xd5a79147; u32 0x06ca6351; u32 0x14292967;
    u32 0x27b70a85; u32 0x2e1b2138; u32 0x4d2c6dfc; u32 0x53380d13;
    u32 0x650a7354; u32 0x766a0abb; u32 0x81c2c92e; u32 0x92722c85;
    u32 0xa2bfe8a1; u32 0xa81a664b; u32 0xc24b8b70; u32 0xc76c51a3;
    u32 0xd192e819; u32 0xd6990624; u32 0xf40e3585; u32 0x106aa070;
    u32 0x19a4c116; u32 0x1e376c08; u32 0x2748774c; u32 0x34b0bcb5;
    u32 0x391c0cb3; u32 0x4ed8aa4a; u32 0x5b9cca4f; u32 0x682e6ff3;
    u32 0x748f82ee; u32 0x78a5636f; u32 0x84c87814; u32 0x8cc70208;
    u32 0x90befffa; u32 0xa4506ceb; u32 0xbef9a3f7; u32 0xc67178f2] in
  assert_norm(List.Tot.length l == 64);
  l

[@"opaque_to_smt"]
let kTable_list_384_512 : l:List.Tot.llist uint64 80 =
  [@inline_let]
  let l = [
    u64 0x428a2f98d728ae22; u64 0x7137449123ef65cd; u64 0xb5c0fbcfec4d3b2f; u64 0xe9b5dba58189dbbc;
    u64 0x3956c25bf348b538; u64 0x59f111f1b605d019; u64 0x923f82a4af194f9b; u64 0xab1c5ed5da6d8118;
    u64 0xd807aa98a3030242; u64 0x12835b0145706fbe; u64 0x243185be4ee4b28c; u64 0x550c7dc3d5ffb4e2;
    u64 0x72be5d74f27b896f; u64 0x80deb1fe3b1696b1; u64 0x9bdc06a725c71235; u64 0xc19bf174cf692694;
    u64 0xe49b69c19ef14ad2; u64 0xefbe4786384f25e3; u64 0x0fc19dc68b8cd5b5; u64 0x240ca1cc77ac9c65;
    u64 0x2de92c6f592b0275; u64 0x4a7484aa6ea6e483; u64 0x5cb0a9dcbd41fbd4; u64 0x76f988da831153b5;
    u64 0x983e5152ee66dfab; u64 0xa831c66d2db43210; u64 0xb00327c898fb213f; u64 0xbf597fc7beef0ee4;
    u64 0xc6e00bf33da88fc2; u64 0xd5a79147930aa725; u64 0x06ca6351e003826f; u64 0x142929670a0e6e70;
    u64 0x27b70a8546d22ffc; u64 0x2e1b21385c26c926; u64 0x4d2c6dfc5ac42aed; u64 0x53380d139d95b3df;
    u64 0x650a73548baf63de; u64 0x766a0abb3c77b2a8; u64 0x81c2c92e47edaee6; u64 0x92722c851482353b;
    u64 0xa2bfe8a14cf10364; u64 0xa81a664bbc423001; u64 0xc24b8b70d0f89791; u64 0xc76c51a30654be30;
    u64 0xd192e819d6ef5218; u64 0xd69906245565a910; u64 0xf40e35855771202a; u64 0x106aa07032bbd1b8;
    u64 0x19a4c116b8d2d0c8; u64 0x1e376c085141ab53; u64 0x2748774cdf8eeb99; u64 0x34b0bcb5e19b48a8;
    u64 0x391c0cb3c5c95a63; u64 0x4ed8aa4ae3418acb; u64 0x5b9cca4f7763e373; u64 0x682e6ff3d6b2b8a3;
    u64 0x748f82ee5defb2fc; u64 0x78a5636f43172f60; u64 0x84c87814a1f0ab72; u64 0x8cc702081a6439ec;
    u64 0x90befffa23631e28; u64 0xa4506cebde82bde9; u64 0xbef9a3f7b2c67915; u64 0xc67178f2e372532b;
    u64 0xca273eceea26619c; u64 0xd186b8c721c0c207; u64 0xeada7dd6cde0eb1e; u64 0xf57d4f7fee6ed178;
    u64 0x06f067aa72176fba; u64 0x0a637dc5a2c898a6; u64 0x113f9804bef90dae; u64 0x1b710b35131c471b;
    u64 0x28db77f523047d84; u64 0x32caab7b40c72493; u64 0x3c9ebe0a15c9bebc; u64 0x431d67c49c100d4c;
    u64 0x4cc5d4becb3e42b6; u64 0x597f299cfc657e2a; u64 0x5fcb6fab3ad6faec; u64 0x6c44198c4a475817] in
  assert_norm(List.Tot.length l == 80);
  l

unfold let kTable_t (a:alg) = lseq (uint_t (wt a) SEC) (size_kTable a)

let kTable (a:alg) : kTable_t a =
  match a with
  | SHA2_224 | SHA2_256 -> (of_list kTable_list_224_256)
  | SHA2_384 | SHA2_512 -> (of_list kTable_list_384_512)


inline_for_extraction let size_h0Table: size_nat = 8

[@"opaque_to_smt"]
let h0Table_list_224: l:List.Tot.llist uint32 size_h0Table =
  [@inline_let]
  let l = [
    u32 0xc1059ed8; u32 0x367cd507; u32 0x3070dd17; u32 0xf70e5939;
    u32 0xffc00b31; u32 0x68581511; u32 0x64f98fa7; u32 0xbefa4fa4] in
  assert_norm(List.Tot.length l == 8);
  l

[@"opaque_to_smt"]
let h0Table_list_256: l:List.Tot.llist uint32 size_h0Table =
  [@inline_let]
  let l = [
    u32 0x6a09e667; u32 0xbb67ae85; u32 0x3c6ef372; u32 0xa54ff53a;
    u32 0x510e527f; u32 0x9b05688c; u32 0x1f83d9ab; u32 0x5be0cd19] in
  assert_norm(List.Tot.length l == 8);
  l

[@"opaque_to_smt"]
let h0Table_list_384: l:List.Tot.llist uint64 size_h0Table =
  [@inline_let]
  let l = [
    u64 0xcbbb9d5dc1059ed8; u64 0x629a292a367cd507; u64 0x9159015a3070dd17; u64 0x152fecd8f70e5939;
    u64 0x67332667ffc00b31; u64 0x8eb44a8768581511; u64 0xdb0c2e0d64f98fa7; u64 0x47b5481dbefa4fa4] in
  assert_norm(List.Tot.length l == 8);
  l

[@"opaque_to_smt"]
let h0Table_list_512: l:List.Tot.llist uint64 size_h0Table =
  [@inline_let]
  let l = [
    u64 0x6a09e667f3bcc908; u64 0xbb67ae8584caa73b; u64 0x3c6ef372fe94f82b; u64 0xa54ff53a5f1d36f1;
    u64 0x510e527fade682d1; u64 0x9b05688c2b3e6c1f; u64 0x1f83d9abfb41bd6b; u64 0x5be0cd19137e2179] in
  assert_norm(List.Tot.length l == 8);
  l

unfold let h0Table_t (a:alg) = lseq (uint_t (wt a) SEC) size_h0Table

let h0Table (a:alg) : h0Table_t a =
  match a with
  | SHA2_224 -> (of_list h0Table_list_224)
  | SHA2_256 -> (of_list h0Table_list_256)
  | SHA2_384 -> (of_list h0Table_list_384)
  | SHA2_512 -> (of_list h0Table_list_512)


(* Definition: Algorithm constants *)
inline_for_extraction let size_word (p:alg): size_nat = numbytes (wt p)
inline_for_extraction let size_block_w: size_nat = 16
inline_for_extraction let size_hash_w: size_nat = 8
inline_for_extraction let size_block (p:alg): size_nat = size_block_w * numbytes (wt p)

inline_for_extraction
let size_hash (p:alg): size_nat =
  match p with
  | SHA2_224 -> 28
  | SHA2_256 -> 32
  | SHA2_384 -> 48
  | SHA2_512 -> 64

(* Definition: Number of bytes required to store the total length *)
inline_for_extraction let lenSize (p:alg): size_nat = numbytes (limb_inttype p)

(* Definition: Maximum input size in bytes *)
let max_input (p:alg): nat =
  (* (maxint (limb_inttype p) + 1) / 8 *)
  match p with
  | SHA2_224 | SHA2_256 -> pow2 61 - 1
  | SHA2_384 | SHA2_512 -> pow2 125 - 1

(* Definition: Types for block and hash as sequences of words *)
type block_w (p:alg) = lseq (uint_t (wt p) SEC) size_block_w
type hash_w (p:alg) = lseq (uint_t (wt p) SEC) size_hash_w
type ws_w (p:alg) = lseq (uint_t (wt p) SEC) (size_kTable p)


(* Definition of permutation functions *)
let _Ch p (x:uint_t (wt p) SEC) (y:uint_t (wt p) SEC) (z:uint_t (wt p) SEC) : uint_t (wt p) SEC = ((x &. y) ^. ((~. x) &. z))
let _Maj p (x:uint_t (wt p) SEC) (y:uint_t (wt p) SEC) (z:uint_t (wt p) SEC) = (x &. y) ^. ((x &. z) ^. (y &. z))
let _Sigma0 p (x:uint_t (wt p) SEC) = (x >>>. (opTable p).[0]) ^. ((x >>>. (opTable p).[1]) ^. (x >>>. (opTable p).[2]))
let _Sigma1 p (x:uint_t (wt p) SEC) = (x >>>. (opTable p).[3]) ^. ((x >>>. (opTable p).[4]) ^. (x >>>. (opTable p).[5]))
let _sigma0 p (x:uint_t (wt p) SEC) = (x >>>. (opTable p).[6]) ^. ((x >>>. (opTable p).[7]) ^. (x >>. (opTable p).[8]))
let _sigma1 p (x:uint_t (wt p) SEC) = (x >>>. (opTable p).[9]) ^. ((x >>>. (opTable p).[10]) ^. (x >>. (opTable p).[11]))

(* Definition of the scheduling function (part 1) *)
let step_ws0 (p:alg) (b:block_w p) (i:size_nat{i < 16}) (s:ws_w p) : Tot (ws_w p) =
  s.[i] <- b.[i]

(* Definition of the scheduling function (part 2) *)
let step_ws1 (p:alg) (i:size_nat{i >= 16 /\ i < size_kTable p}) (s:ws_w p) : Tot (ws_w p) =
  let t16 = s.[i - 16] in
  let t15 = s.[i - 15] in
  let t7  = s.[i - 7] in
  let t2  = s.[i - 2] in
  let s1 = _sigma1 p t2 in
  let s0 = _sigma0 p t15 in
  s.[i] <- s1 +. (t7 +. (s0 +. t16))

(* Definition of the loop over the scheduling function (part 1) *)
let loop_ws0 p b s = repeati 16 (step_ws0 p b) s

(* Definition of the loop over the scheduling function (part 2) *)
let loop_ws1 p s = repeati (size_kTable p - 16) (fun i -> step_ws1 p (i + 16)) s

(* Definition of the core scheduling function *)
let ws (p:alg) (b:block_w p) : Tot (ws_w p) =
  let s = create (size_kTable p) (nat_to_uint #(wt p) #SEC 0) in
  let s = loop_ws0 p b s in
  let s = loop_ws1 p s in
  s

(* Definition of the core shuffling function *)
let shuffle_core (p:alg) (wsTable:ws_w p) (t:size_nat{t < size_kTable p}) (hash:hash_w p) : Tot (hash_w p) =
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  let t1 = h0 +. (_Sigma1 p e0) +. ((_Ch p e0 f0 g0) +. ((kTable p).[t] +. wsTable.[t])) in
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
let shuffle (p:alg) (wsTable:ws_w p) (hash:hash_w p) : Tot (hash_w p) =
  repeati (size_kTable p) (shuffle_core p wsTable) hash

(* Definition of the core compression function *)
let compress (p:alg) (block:block_w p) (hash0:hash_w p) : Tot (hash_w p) =
  let wsTable: ws_w p = ws p block in
  let hash1: hash_w p = shuffle p wsTable hash0 in
  map2 (fun x y -> x +. y) hash0 hash1

(* Definition of the truncation function *)
let truncate (p:alg) (hash:hash_w p) : Tot (lbytes (size_hash p)) =
  let hash_final = uints_to_bytes_be hash in
  let h = sub hash_final 0 (size_hash p) in
  h

(* Definition of the function returning the number of padding blocks for a single input block *)
let number_blocks_padding (p:alg) (len:size_nat{len <= size_block p}) : Tot size_nat =
  if len < size_block p - numbytes (limb_inttype p) then 1 else 2

(* Definition of the padding function for a single input block *)
let pad
  (p:alg)
  (prev:nat)
  (len:nat{len <= size_block p /\ len + prev <= max_input p})
  (last:lbytes len) :
  Tot (block:lbytes (size_block p * number_blocks_padding p len)) =

  let nr = number_blocks_padding p len in
  let plen : size_nat = nr * size_block p in
  // Create the padding and copy the partial block inside
  let padding : lbytes plen = create plen (u8 0) in
  let padding = repeati #(lbytes plen) len (fun i s -> s.[i] <- last.[i]) padding in
  // Write the 0x80 byte and the zeros in the padding
  let padding = padding.[len] <- u8 0x80 in
  // Encode and write the total length in bits at the end of the padding
  let tlen = prev + len in
  let tlenbits = tlen * 8 in
  let x = nat_to_uint #(limb_inttype p) #SEC tlenbits in
  let encodedlen = uint_to_bytes_be x in
  let padding = update_slice padding (plen - numbytes (limb_inttype p)) plen encodedlen in
  padding

(* Definition of the single block update function *)
let update_block (p:alg) (block:lbytes (size_block p)) (hash:hash_w p) : Tot (hash_w p) =
  let bw = uints_from_bytes_be block in
  compress p bw hash

(* Definition of the init function *)
let init (p:alg): Tot (hash_w p) = h0Table p

(* Definition of the function for the partial block compression *)
let update_last
  (p:alg)
  (prev:nat)
  (len:nat{len <= size_block p /\ len + prev <= max_input p})
  (last:lbytes len)
  (hash:hash_w p):
  Tot (hash_w p) =

  let blocks = pad p prev len last in
  if number_blocks_padding p len = 1 then
    update_block p blocks hash
  else (
    let block1 = sub blocks 0 (size_block p) in
    let block2 = sub blocks (size_block p) (size_block p) in
    let hash = update_block p block1 hash in
    update_block p block2 hash)

(* Definition of the update function *)
let update (p:alg) (input:bytes{length input <= max_input p}) (hash:hash_w p): Tot (hash_w p) =
  repeati_blocks (size_block p) input
    (fun i -> update_block p)
    (fun i -> update_last p (i * (size_block p))) hash

(* Definition of the finalization function *)
let finish p (hash:hash_w p) : lbytes (size_hash p) =
  truncate p hash

(* Definition of the SHA2 ontime function *)
let hash (p:alg) (input:bytes{length input <= max_input p}) : Tot (lbytes (size_hash p)) =
  let len = length input in
  let s = init p in
  let s = update p input s in
  finish p s

///
/// Instances of SHA2
///

let size_block224 = size_block SHA2_224
let size_block256 = size_block SHA2_256
let size_block384 = size_block SHA2_384
let size_block512 = size_block SHA2_512

let size_hash224 = size_hash SHA2_224
let size_hash256 = size_hash SHA2_256
let size_hash384 = size_hash SHA2_384
let size_hash512 = size_hash SHA2_512

let max_input224 = max_input SHA2_224
let max_input256 = max_input SHA2_256
let max_input384 = max_input SHA2_384
let max_input512 = max_input SHA2_512

let init224 = init SHA2_224
let init256 = init SHA2_256
let init384 = init SHA2_384
let init512 = init SHA2_512

let update_block224 block hash = update_block SHA2_224 block hash
let update_block256 block hash = update_block SHA2_256 block hash
let update_block384 block hash = update_block SHA2_384 block hash
let update_block512 block hash = update_block SHA2_512 block hash

let update224 input hash = update SHA2_224 input hash
let update256 input hash = update SHA2_256 input hash
let update384 input hash = update SHA2_384 input hash
let update512 input hash = update SHA2_512 input hash

let update_last224 prev len last hash = update_last SHA2_224 prev len last hash
let update_last256 prev len last hash = update_last SHA2_256 prev len last hash
let update_last384 prev len last hash = update_last SHA2_384 prev len last hash
let update_last512 prev len last hash = update_last SHA2_512 prev len last hash

let finish224 hash = finish SHA2_224 hash
let finish256 hash = finish SHA2_256 hash
let finish384 hash = finish SHA2_384 hash
let finish512 hash = finish SHA2_512 hash

let hash224 input = hash SHA2_224 input
let hash256 input = hash SHA2_256 input
let hash384 input = hash SHA2_384 input
let hash512 input = hash SHA2_512 input
