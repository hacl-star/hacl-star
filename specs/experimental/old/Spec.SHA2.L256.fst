module Spec.SHA2.L256

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib


assume val inflate: (x:seq UInt8.t) -> Tot (seq UInt32.t)
assume val finish: (x:seq UInt32.t) -> Tot (seq UInt8.t)
assume val as_list: (x:seq UInt32.t) -> Tot (list UInt32.t)


(* Define algorithm parameters *)
let hashsize = 32
let hashsize_32 = 8
let blocksize_8 = 64
let blocksize_32 = 16


(* Define base types *)
type data   = d:seq UInt8.t {length d * 8 < pow2 64}
type hash_8  = h:seq UInt32.t {length h = hashsize}
type hash_32  = h:seq UInt32.t {length h = hashsize_32}
type block_32 = b:seq UInt32.t {length b = blocksize_32}
unfold type blocks_32 = b:seq block_32
unfold type const_64 = b:seq UInt32.t {length b = 64}


private let _Ch (x:UInt32.t) (y:UInt32.t) (z:UInt32.t) : Tot UInt32.t =
  UInt32.logxor (UInt32.logand x y) (UInt32.logand (UInt32.lognot x) z)

private let _Maj (x:UInt32.t) (y:UInt32.t) (z:UInt32.t) : Tot UInt32.t =
  UInt32.logxor (UInt32.logand x y) (UInt32.logxor (UInt32.logand x z) (UInt32.logand y z))

private let _Sigma0 (x:UInt32.t) : Tot UInt32.t =
  UInt32.logxor (rotate_right x 2ul) (UInt32.logxor (rotate_right x 13ul) (rotate_right x 22ul))

private let _Sigma1 (x:UInt32.t) : Tot UInt32.t =
  UInt32.logxor (rotate_right x 6ul) (UInt32.logxor (rotate_right x 11ul) (rotate_right x 25ul))

private let _sigma0 (x:UInt32.t) : Tot UInt32.t =
  UInt32.logxor (rotate_right x 7ul) (UInt32.logxor (rotate_right x 18ul) (UInt32.shift_right x 3ul))

private let _sigma1 (x:UInt32.t) : Tot UInt32.t =
  UInt32.logxor (rotate_right x 17ul) (UInt32.logxor (rotate_right x 19ul) (UInt32.shift_right x 10ul))


(* Definition of constants *)
private unfold let k = createL [
  0x428a2f98ul; 0x71374491ul; 0xb5c0fbcful; 0xe9b5dba5ul;
  0x3956c25bul; 0x59f111f1ul; 0x923f82a4ul; 0xab1c5ed5ul;
  0xd807aa98ul; 0x12835b01ul; 0x243185beul; 0x550c7dc3ul;
  0x72be5d74ul; 0x80deb1feul; 0x9bdc06a7ul; 0xc19bf174ul;
  0xe49b69c1ul; 0xefbe4786ul; 0x0fc19dc6ul; 0x240ca1ccul;
  0x2de92c6ful; 0x4a7484aaul; 0x5cb0a9dcul; 0x76f988daul;
  0x983e5152ul; 0xa831c66dul; 0xb00327c8ul; 0xbf597fc7ul;
  0xc6e00bf3ul; 0xd5a79147ul; 0x06ca6351ul; 0x14292967ul;
  0x27b70a85ul; 0x2e1b2138ul; 0x4d2c6dfcul; 0x53380d13ul;
  0x650a7354ul; 0x766a0abbul; 0x81c2c92eul; 0x92722c85ul;
  0xa2bfe8a1ul; 0xa81a664bul; 0xc24b8b70ul; 0xc76c51a3ul;
  0xd192e819ul; 0xd6990624ul; 0xf40e3585ul; 0x106aa070ul;
  0x19a4c116ul; 0x1e376c08ul; 0x2748774cul; 0x34b0bcb5ul;
  0x391c0cb3ul; 0x4ed8aa4aul; 0x5b9cca4ful; 0x682e6ff3ul;
  0x748f82eeul; 0x78a5636ful; 0x84c87814ul; 0x8cc70208ul;
  0x90befffaul; 0xa4506cebul; 0xbef9a3f7ul; 0xc67178f2ul
]

private unfold let h_0 = createL [
  0x6a09e667ul; 0xbb67ae85ul; 0x3c6ef372ul; 0xa54ff53aul;
  0x510e527ful; 0x9b05688cul; 0x1f83d9abul; 0x5be0cd19ul
]


(* Updating multiple elements of a sequence *)
private let upd_4 (h:hash_32) (i:nat{i+3 < length h}) (h0 h1 h2 h3:UInt32.t) : Tot hash_32 =
  let h = upd h (i + 0) h0 in
  let h = upd h (i + 1) h1 in
  let h = upd h (i + 2) h2 in
  let h = upd h (i + 3) h3 in
  h


(* Updating multiple elements of a sequence *)
private let upd_8 (h:hash_32) (h0 h1 h2 h3 h4 h5 h6 h7:UInt32.t) : Tot hash_32 =
  let h = upd_4 h 0 h0 h1 h2 h3 in
  let h = upd_4 h 4 h4 h5 h6 h7 in
  h


(* Transforming bytes into a sequence of block_8 *)
private let rec store_blocks (input:bytes{length input % blocksize_8 = 0}) : Tot (blocks_32) (decreases (Seq.length input)) =
  let l = (Seq.length input / blocksize_8) in
  if l = 0 then
    Seq.createEmpty
  else
    let w,input = Seq.split input blocksize_8 in
    Seq.snoc (store_blocks input) (inflate w)


(* Section 5.1.1 *)
(* Compute the pad length (without the last 8 bytes) *)
private let pad_length (len:nat) : Tot (n:nat{n <= 64}) =
  if (len % 64) < 56 then 56 - (len % 64)
  else 64 + 56 - (len % 64)


(* Pad the data up to the block length and encode the total length *)
let pad (input:data) : Tot (output:blocks_32) =

  (* Compute the padding length *)
  let padlen = pad_length (Seq.length input) in

  (* Generate the padding (without the last 8 bytes) *)
  let padding = Seq.create padlen 0uy in

  (* Set the first bit of the padding to be a '1' *)
  let padding = Seq.upd padding 0 0x80uy in

  (* Encode the data length (in bits) as a 64bit big endian integer*)
  let encodedlen = big_bytes 8ul ((Seq.length input) * 8) in

  (* Concatenate the data, padding and encoded length *)
  let output = Seq.append input padding in
  let output = Seq.append output encodedlen in
  store_blocks output


(* Section 6.2.2 *)
(* Step 1: Scheduling for sixty-four 32bit words *)
private let rec ws (b:block_32) (t:nat{t < 64}) : Tot UInt32.t =

  (* Perform computations *)
  if t < 16 then index b t
  else
    let t16 = ws b (t - 16) in
    let t15 = ws b (t - 15) in
    let t7  = ws b (t - 7) in
    let t2  = ws b (t - 2) in
    ((_sigma1 t2) +%^ (t7 +%^ ((_sigma0 t15) +%^ t16)))


(* Section 6.2.2 *)
(* Step 3: Perform logical operations on the working variables *)
private let rec shuffle (h:hash_32) (b:block_32) (k:const_64) (t:nat{t <= 64}) : Tot hash_32 =
  if t < 64 then
    let l = as_list h in
     // assert_norm(List.Tot.length l = 8);
     match l with
     | [a_0; b_0; c_0; d_0; e_0; f_0; g_0; h_0] ->
     begin
       let t1 = (((h_0 +%^ _Sigma1 e_0) +%^ (_Ch e_0 f_0 g_0)) +%^ (index k t) +%^ (ws b t)) in
       let t2 = (_Sigma0 a_0) +%^ (_Maj a_0 b_0 c_0) in

       (* Update the working hash *)
       let h = upd_8 h (t1 +%^ t2) a_0 b_0 c_0 (d_0 +%^ t1) d_0 e_0 f_0 in
       shuffle h b k (t + 1)
    end
  else h


(* Section 6.2.2 *)
(* Step 1-4: Hash computation of the current block *)
let update (h:hash_32) (b:block_32) : Tot hash_32 = map2 (UInt32.add_mod) h (shuffle h b k 0)


(* Process multiple block_32 through the block function *)
let rec update_multi (h:hash_32) (b:blocks_32) : Tot hash_32 =
  let l = Seq.length b in
  if l = 0 then h
  else
    let bhd,btl = Seq.split b 1 in
    let b = Seq.head bhd in
    update_multi (update h b) btl


(* Definition of the hash function *)
let hash (input:bytes) : Tot (hash:bytes) = finish (update_multi h_0 (pad input))







let test () =

  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 3ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  let expected = FStar.Buffer.createL [
      0xbauy; 0x78uy; 0x16uy; 0xbfuy; 0x8fuy; 0x01uy; 0xcfuy; 0xeauy;
      0x41uy; 0x41uy; 0x40uy; 0xdeuy; 0x5duy; 0xaeuy; 0x22uy; 0x23uy;
      0xb0uy; 0x03uy; 0x61uy; 0xa3uy; 0x96uy; 0x17uy; 0x7auy; 0x9cuy;
      0xb4uy; 0x10uy; 0xffuy; 0x61uy; 0xf2uy; 0x00uy; 0x15uy; 0xaduy
    ] in

  (* Call the hash function *)
  let output = hash plaintext plaintext_len in

  (* Display the result *)
  TestLib.compare_and_print (C.string_of_literal "Test 1b") expected output 32ul
