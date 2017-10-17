module Spec.SHA2.Generic

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open Spec.Loops
open Spec.Lib

type lseq a n = s:seq a{Seq.length s = n}
type byte = UInt8.t
type u8 = UInt8.t
type u32 = UInt32.t
type u64 = UInt64.t
type rotval (size:nat) = r:u32{v r > 0 /\ v r < 8 * size}

#set-options "--z3rlimit  25"

let rec big_bytes #max (start:nat) (len:nat{start+len <= max}) (n:nat{n < pow2 (8 * len)}) (s:lseq u8 max) : lseq u8 max =
  if len = 0 then
    s
  else
    let len = len - 1 in
    let byte = UInt8.uint_to_t (n % 256) in
    let n' = n / 256 in
    let s = s.[start+len] <- byte in
    big_bytes #max start len n' s

let write #n (s:lseq 'a n) (i:nat{i < n}) (v:'a) : (t:lseq 'a n) =
    upd s i v

noeq
type word (w:Type) (size:nat) = {
     word0: w;
     to_be: len:nat -> lseq w len -> lseq byte (size * len);
     from_be: len:nat -> lseq byte (size * len) -> lseq w len;
     add_mod: w -> w -> w;
     logxor: w -> w -> w;
     logand: w -> w -> w;
     logor: w -> w -> w;
     lognot: w -> w;
     shift_right: w -> s:u32{v s < 8 * size} -> w;
     rotate_right: w -> rotval size -> w
     }

noeq type sha2_params =
  | MkParams: wt:Type -> sz:nat{sz = 4 \/ sz = 8} -> w:word wt sz ->
	      opTable: lseq (rotval sz) 12 ->
	      lenSize: nat{lenSize > 0 /\ lenSize <= 16} ->
	      kSize: nat{kSize > 16} ->
	      kTable: lseq wt kSize ->
	      h0: lseq wt 8 ->
	      hashSize: nat {hashSize <= 8 * sz} ->
	      sha2_params

let _Ch p x y z = p.w.logxor (p.w.logand x y)
                           (p.w.logand (p.w.lognot x) z)

let _Maj p x y z = p.w.logxor (p.w.logand x y)
                            (p.w.logxor (p.w.logand x z)
                                         (p.w.logand y z))

let _Sigma0 p x = p.w.logxor (p.w.rotate_right x p.opTable.[0])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[1])
                                               (p.w.rotate_right x p.opTable.[2]))

let _Sigma1 p x = p.w.logxor (p.w.rotate_right x p.opTable.[3])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[4])
                                               (p.w.rotate_right x p.opTable.[5]))

let _sigma0 p x = p.w.logxor (p.w.rotate_right x p.opTable.[6])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[7])
                                               (p.w.shift_right x p.opTable.[8]))

let _sigma1 p x = p.w.logxor (p.w.rotate_right x p.opTable.[9])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[10])
                                               (p.w.shift_right x p.opTable.[11]))


type block_w p = b:lseq p.wt 16
type hash_w p = b:lseq p.wt 8
let size_block p = 16 * p.sz
let size_hash p = 8 * p.sz

let op_String_Access = Seq.index
let op_String_Assignment = Seq.upd

let step_ws0 p (b:block_w p) (s:lseq p.wt p.kSize) (i:nat{i >= 0 /\ i < 16}) : (t:lseq p.wt p.kSize) =
    s.[i] <- b.[i]

let step_ws1 p (s:lseq p.wt p.kSize) (i:nat{i >= 16 /\ i < p.kSize}) : (t:lseq p.wt p.kSize) =
      let t16 = s.[i - 16] in
      let t15 = s.[i - 15] in
      let t7  = s.[i - 7] in
      let t2  = s.[i - 2] in
      let s1 = _sigma1 p t2 in
      let s0 = _sigma0 p t15 in
      s.[i] <- p.w.add_mod s1 (p.w.add_mod t7 (p.w.add_mod s0 t16))

let ws p (b:block_w p) =
  let s = Seq.create p.kSize p.w.word0 in
  let s = Spec.Loops.repeat_range_spec 0 16 (step_ws0 p b) s in
  let s = Spec.Loops.repeat_range_spec 16 p.kSize (step_ws1 p) s in
  s

(* Core shuffling function *)
let shuffle_core p (wsTable:lseq p.wt p.kSize) (hash:hash_w p) (t:nat{t >= 0 /\ t < p.kSize}) : Tot (hash_w p) =
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  let t1 = p.w.add_mod h0 (p.w.add_mod (_Sigma1 p e0) (p.w.add_mod (_Ch p e0 f0 g0) (p.w.add_mod p.kTable.[t] (wsTable.[t])))) in
  let t2 = p.w.add_mod (_Sigma0 p a0) (_Maj p a0 b0 c0) in

  let hash = hash.[0] <- p.w.add_mod t1 t2 in
  let hash = hash.[1] <- a0 in
  let hash = hash.[2] <- b0 in
  let hash = hash.[3] <- c0 in
  let hash = hash.[4] <- (p.w.add_mod d0 t1) in
  let hash = hash.[5] <- e0 in
  let hash = hash.[6] <- f0 in
  let hash = hash.[7] <- g0 in
  hash


(* Full shuffling function *)
let shuffle (p:sha2_params) (wsTable:lseq p.wt p.kSize) (hash:hash_w p) : Tot (hash_w p) =
  Spec.Loops.repeat_range_spec 0 p.kSize (shuffle_core p wsTable) hash


(* Compression function *)
let update_block (p:sha2_params) (block:bytes{length block = size_block p}) (hash:hash_w p) : Tot (hash_w p) =
  let block_w = p.w.from_be 16 block in
  let wsTable = ws p block_w in
  let hash_1 = shuffle p wsTable hash in
  Spec.Lib.map2 (fun x y -> p.w.add_mod x y) hash hash_1

let update_multi (p:sha2_params) (n:nat) (blocks:bytes{length blocks = n * size_block p}) (hash:hash_w p) : Tot (hash_w p) =
  let bl = size_block p in
  Spec.Loops.repeat_range_spec 0 n
    (fun h i -> update_block p (Seq.slice blocks (bl * i) (bl * (i+1))) h)
    hash

let padding_blocks p (len:nat) : nat =
  if (len < size_block p - p.lenSize) then 1 else 2

let padding_size p (len:nat) = size_block p * padding_blocks p len

let pad p (n:nat) (last:seq u8{length last < size_block p /\
			     8 * (n * size_block p + length last) < pow2 (8 * p.lenSize)}) :
				    lseq u8 (padding_size p (length last)) =
  let lastlen = length last in
  let blocks = padding_blocks p lastlen in
  let plen = blocks * size_block p in
  let padding : lseq byte plen = Seq.create plen 0uy in
  let tlen = n * size_block p + lastlen in
  let padding = Spec.Loops.repeat_range_spec 0 lastlen
			(fun s i -> write #byte #plen s i last.[i]) padding in
  let padding = Spec.Loops.repeat_range_spec (lastlen + 1) (plen - p.lenSize)
			(fun s i -> write #byte #plen s i 0uy) padding in
  let tlenbits = FStar.Mul.(tlen * 8) in
  let padding = big_bytes #plen (plen - p.lenSize) p.lenSize tlenbits padding in
  padding

let update_last p (n:nat) (last:seq u8{
		             length last < size_block p /\
			     8 * (n * size_block p + length last) < pow2 (8 * p.lenSize)})
		        (hash:hash_w p) : Tot (hash_w p) =
  let blocks = pad p n last in
  update_multi p (padding_blocks p (length last)) blocks hash

let finish p (hash:hash_w p) : lseq byte p.hashSize =
  let hash_final = p.w.to_be 8 hash in
  let h,_ = Seq.split hash_final p.hashSize in
  h

#reset-options "--z3rlimit 10"

let hash p (input:bytes{8 * length input < pow2 (8 * p.lenSize)}) : lseq byte p.hashSize =
  let n = Seq.length input / (size_block p) in
  let prevlen = n * (size_block p) in
  let (bs,l) = Seq.split input prevlen in
  let hash = update_multi p n bs p.h0 in
  let hash = update_last p n l hash in
  finish p hash

let hash' p (input:bytes{8 * length input < pow2 (8 * p.lenSize)}) : lseq byte p.hashSize =
  let n = Seq.length input / (size_block p) in
  let prevlen = n * (size_block p) in
  let (blocks,last) = Seq.split input prevlen in
  let padding = pad p n last in
  let lastlen = length last in
  let padn = padding_blocks p lastlen in
  finish p (update_multi p (n + padn) (blocks @| padding) p.h0)


let rotate_right32 (x:UInt32.t) (s:UInt32.t{0 < v s /\ v s < 32}) : Tot UInt32.t =
  ((x >>^ s) |^ (x <<^ (32ul -^ s)))

let rotate_right64 (a:UInt64.t) (s:UInt32.t{0 < v s /\ v s < 64}) : Tot UInt64.t =
  FStar.UInt64.((a >>^ s) |^ (a <<^ (UInt32.sub 64ul s)))

val u32s_from_be: len:nat -> lseq byte (4 * len) -> lseq u32 len
let u32s_from_be l s = Spec.Lib.uint32s_from_be l s

val shift_right32: n:u32 -> s:u32{v s < 32} -> u32
let shift_right32 n s = UInt32.shift_right n s

val u64s_from_be: len:nat -> lseq byte (8 * len) -> lseq u64 len
let u64s_from_be l s = Spec.Lib.uint64s_from_be l s

val shift_right64: n:u64 -> s:u32{v s < 64} -> u64
let shift_right64 n s = UInt64.shift_right n s

let word32 : word u32 4 = {
  word0 = 0ul;
  to_be = Spec.Lib.uint32s_to_be;
  from_be = u32s_from_be;
  add_mod = UInt32.add_mod;
  logxor = UInt32.logxor;
  logand = UInt32.logand;
  logor = UInt32.logor;
  lognot = UInt32.lognot;
  shift_right = shift_right32;
  rotate_right = rotate_right32;
}

let word64 : word u64 8 = {
  word0 = 0uL;
  to_be = Spec.Lib.uint64s_to_be;
  from_be = u64s_from_be;
  add_mod = UInt64.add_mod;
  logxor = UInt64.logxor;
  logand = UInt64.logand;
  logor = UInt64.logor;
  lognot = UInt64.lognot;
  shift_right = shift_right64;
  rotate_right = rotate_right64;
}


let params_sha2_224 : sha2_params =
  MkParams
    u32
    4
    word32
    (Seq.Create.create_12
    2ul  13ul 22ul
    6ul  11ul 25ul
    7ul  18ul  3ul
    17ul 19ul 10ul)
    8
    64
    (Seq.Create.create_64
    0x428a2f98ul 0x71374491ul 0xb5c0fbcful 0xe9b5dba5ul
    0x3956c25bul 0x59f111f1ul 0x923f82a4ul 0xab1c5ed5ul
    0xd807aa98ul 0x12835b01ul 0x243185beul 0x550c7dc3ul
    0x72be5d74ul 0x80deb1feul 0x9bdc06a7ul 0xc19bf174ul
    0xe49b69c1ul 0xefbe4786ul 0x0fc19dc6ul 0x240ca1ccul
    0x2de92c6ful 0x4a7484aaul 0x5cb0a9dcul 0x76f988daul
    0x983e5152ul 0xa831c66dul 0xb00327c8ul 0xbf597fc7ul
    0xc6e00bf3ul 0xd5a79147ul 0x06ca6351ul 0x14292967ul
    0x27b70a85ul 0x2e1b2138ul 0x4d2c6dfcul 0x53380d13ul
    0x650a7354ul 0x766a0abbul 0x81c2c92eul 0x92722c85ul
    0xa2bfe8a1ul 0xa81a664bul 0xc24b8b70ul 0xc76c51a3ul
    0xd192e819ul 0xd6990624ul 0xf40e3585ul 0x106aa070ul
    0x19a4c116ul 0x1e376c08ul 0x2748774cul 0x34b0bcb5ul
    0x391c0cb3ul 0x4ed8aa4aul 0x5b9cca4ful 0x682e6ff3ul
    0x748f82eeul 0x78a5636ful 0x84c87814ul 0x8cc70208ul
    0x90befffaul 0xa4506cebul 0xbef9a3f7ul 0xc67178f2ul)
    (Seq.Create.create_8
    0xc1059ed8ul 0x367cd507ul 0x3070dd17ul 0xf70e5939ul
    0xffc00b31ul 0x68581511ul 0x64f98fa7ul 0xbefa4fa4ul)
    28

let params_sha2_256 =
  MkParams
    u32
    4
    word32
    (Seq.Create.create_12
    2ul  13ul 22ul
    6ul  11ul 25ul
    7ul  18ul  3ul
    17ul 19ul 10ul)
    8
    64
    (Seq.Create.create_64
    0x428a2f98ul 0x71374491ul 0xb5c0fbcful 0xe9b5dba5ul
    0x3956c25bul 0x59f111f1ul 0x923f82a4ul 0xab1c5ed5ul
    0xd807aa98ul 0x12835b01ul 0x243185beul 0x550c7dc3ul
    0x72be5d74ul 0x80deb1feul 0x9bdc06a7ul 0xc19bf174ul
    0xe49b69c1ul 0xefbe4786ul 0x0fc19dc6ul 0x240ca1ccul
    0x2de92c6ful 0x4a7484aaul 0x5cb0a9dcul 0x76f988daul
    0x983e5152ul 0xa831c66dul 0xb00327c8ul 0xbf597fc7ul
    0xc6e00bf3ul 0xd5a79147ul 0x06ca6351ul 0x14292967ul
    0x27b70a85ul 0x2e1b2138ul 0x4d2c6dfcul 0x53380d13ul
    0x650a7354ul 0x766a0abbul 0x81c2c92eul 0x92722c85ul
    0xa2bfe8a1ul 0xa81a664bul 0xc24b8b70ul 0xc76c51a3ul
    0xd192e819ul 0xd6990624ul 0xf40e3585ul 0x106aa070ul
    0x19a4c116ul 0x1e376c08ul 0x2748774cul 0x34b0bcb5ul
    0x391c0cb3ul 0x4ed8aa4aul 0x5b9cca4ful 0x682e6ff3ul
    0x748f82eeul 0x78a5636ful 0x84c87814ul 0x8cc70208ul
    0x90befffaul 0xa4506cebul 0xbef9a3f7ul 0xc67178f2ul)
    (Seq.Create.create_8
    0x6a09e667ul 0xbb67ae85ul 0x3c6ef372ul 0xa54ff53aul
    0x510e527ful 0x9b05688cul 0x1f83d9abul 0x5be0cd19ul)
    32


let params_sha2_384 =
  MkParams
    u64
    8
    word64
    (Seq.Create.create_12
    28ul 34ul 39ul
    14ul 18ul 41ul
    1ul   8ul  7ul
    19ul 61ul  6ul)
    16
    80
    (Seq.Create.create_80
    0x428a2f98d728ae22uL 0x7137449123ef65cduL 0xb5c0fbcfec4d3b2fuL 0xe9b5dba58189dbbcuL
    0x3956c25bf348b538uL 0x59f111f1b605d019uL 0x923f82a4af194f9buL 0xab1c5ed5da6d8118uL
    0xd807aa98a3030242uL 0x12835b0145706fbeuL 0x243185be4ee4b28cuL 0x550c7dc3d5ffb4e2uL
    0x72be5d74f27b896fuL 0x80deb1fe3b1696b1uL 0x9bdc06a725c71235uL 0xc19bf174cf692694uL
    0xe49b69c19ef14ad2uL 0xefbe4786384f25e3uL 0x0fc19dc68b8cd5b5uL 0x240ca1cc77ac9c65uL
    0x2de92c6f592b0275uL 0x4a7484aa6ea6e483uL 0x5cb0a9dcbd41fbd4uL 0x76f988da831153b5uL
    0x983e5152ee66dfabuL 0xa831c66d2db43210uL 0xb00327c898fb213fuL 0xbf597fc7beef0ee4uL
    0xc6e00bf33da88fc2uL 0xd5a79147930aa725uL 0x06ca6351e003826fuL 0x142929670a0e6e70uL
    0x27b70a8546d22ffcuL 0x2e1b21385c26c926uL 0x4d2c6dfc5ac42aeduL 0x53380d139d95b3dfuL
    0x650a73548baf63deuL 0x766a0abb3c77b2a8uL 0x81c2c92e47edaee6uL 0x92722c851482353buL
    0xa2bfe8a14cf10364uL 0xa81a664bbc423001uL 0xc24b8b70d0f89791uL 0xc76c51a30654be30uL
    0xd192e819d6ef5218uL 0xd69906245565a910uL 0xf40e35855771202auL 0x106aa07032bbd1b8uL
    0x19a4c116b8d2d0c8uL 0x1e376c085141ab53uL 0x2748774cdf8eeb99uL 0x34b0bcb5e19b48a8uL
    0x391c0cb3c5c95a63uL 0x4ed8aa4ae3418acbuL 0x5b9cca4f7763e373uL 0x682e6ff3d6b2b8a3uL
    0x748f82ee5defb2fcuL 0x78a5636f43172f60uL 0x84c87814a1f0ab72uL 0x8cc702081a6439ecuL
    0x90befffa23631e28uL 0xa4506cebde82bde9uL 0xbef9a3f7b2c67915uL 0xc67178f2e372532buL
    0xca273eceea26619cuL 0xd186b8c721c0c207uL 0xeada7dd6cde0eb1euL 0xf57d4f7fee6ed178uL
    0x06f067aa72176fbauL 0x0a637dc5a2c898a6uL 0x113f9804bef90daeuL 0x1b710b35131c471buL
    0x28db77f523047d84uL 0x32caab7b40c72493uL 0x3c9ebe0a15c9bebcuL 0x431d67c49c100d4cuL
    0x4cc5d4becb3e42b6uL 0x597f299cfc657e2auL 0x5fcb6fab3ad6faecuL 0x6c44198c4a475817uL)
    (Seq.Create.create_8
    0xcbbb9d5dc1059ed8uL 0x629a292a367cd507uL 0x9159015a3070dd17uL 0x152fecd8f70e5939uL
    0x67332667ffc00b31uL 0x8eb44a8768581511uL 0xdb0c2e0d64f98fa7uL 0x47b5481dbefa4fa4uL)
    48

let params_sha2_512 =
  MkParams
    u64
    8
    word64
    (Seq.Create.create_12
    28ul 34ul 39ul
    14ul 18ul 41ul
    1ul   8ul  7ul
    19ul 61ul  6ul)
    16
    80
    (Seq.Create.create_80
    0x428a2f98d728ae22uL 0x7137449123ef65cduL 0xb5c0fbcfec4d3b2fuL 0xe9b5dba58189dbbcuL
    0x3956c25bf348b538uL 0x59f111f1b605d019uL 0x923f82a4af194f9buL 0xab1c5ed5da6d8118uL
    0xd807aa98a3030242uL 0x12835b0145706fbeuL 0x243185be4ee4b28cuL 0x550c7dc3d5ffb4e2uL
    0x72be5d74f27b896fuL 0x80deb1fe3b1696b1uL 0x9bdc06a725c71235uL 0xc19bf174cf692694uL
    0xe49b69c19ef14ad2uL 0xefbe4786384f25e3uL 0x0fc19dc68b8cd5b5uL 0x240ca1cc77ac9c65uL
    0x2de92c6f592b0275uL 0x4a7484aa6ea6e483uL 0x5cb0a9dcbd41fbd4uL 0x76f988da831153b5uL
    0x983e5152ee66dfabuL 0xa831c66d2db43210uL 0xb00327c898fb213fuL 0xbf597fc7beef0ee4uL
    0xc6e00bf33da88fc2uL 0xd5a79147930aa725uL 0x06ca6351e003826fuL 0x142929670a0e6e70uL
    0x27b70a8546d22ffcuL 0x2e1b21385c26c926uL 0x4d2c6dfc5ac42aeduL 0x53380d139d95b3dfuL
    0x650a73548baf63deuL 0x766a0abb3c77b2a8uL 0x81c2c92e47edaee6uL 0x92722c851482353buL
    0xa2bfe8a14cf10364uL 0xa81a664bbc423001uL 0xc24b8b70d0f89791uL 0xc76c51a30654be30uL
    0xd192e819d6ef5218uL 0xd69906245565a910uL 0xf40e35855771202auL 0x106aa07032bbd1b8uL
    0x19a4c116b8d2d0c8uL 0x1e376c085141ab53uL 0x2748774cdf8eeb99uL 0x34b0bcb5e19b48a8uL
    0x391c0cb3c5c95a63uL 0x4ed8aa4ae3418acbuL 0x5b9cca4f7763e373uL 0x682e6ff3d6b2b8a3uL
    0x748f82ee5defb2fcuL 0x78a5636f43172f60uL 0x84c87814a1f0ab72uL 0x8cc702081a6439ecuL
    0x90befffa23631e28uL 0xa4506cebde82bde9uL 0xbef9a3f7b2c67915uL 0xc67178f2e372532buL
    0xca273eceea26619cuL 0xd186b8c721c0c207uL 0xeada7dd6cde0eb1euL 0xf57d4f7fee6ed178uL
    0x06f067aa72176fbauL 0x0a637dc5a2c898a6uL 0x113f9804bef90daeuL 0x1b710b35131c471buL
    0x28db77f523047d84uL 0x32caab7b40c72493uL 0x3c9ebe0a15c9bebcuL 0x431d67c49c100d4cuL
    0x4cc5d4becb3e42b6uL 0x597f299cfc657e2auL 0x5fcb6fab3ad6faecuL 0x6c44198c4a475817uL)
    (Seq.Create.create_8
    0x6a09e667f3bcc908uL 0xbb67ae8584caa73buL 0x3c6ef372fe94f82buL 0xa54ff53a5f1d36f1uL
    0x510e527fade682d1uL 0x9b05688c2b3e6c1fuL 0x1f83d9abfb41bd6buL 0x5be0cd19137e2179uL)
    64
