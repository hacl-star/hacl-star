module Hash.SHA2.L256.Pure

open FStar.UInt32

module I8 = FStar.UInt8
module I32 = FStar.UInt32
module I64 = FStar.UInt64
module IB = FStar.Buffer
module IOP = Hacl.Operations.Pure


(* Define operators *)
let op_Array_Assignment = Seq.upd
let op_Array_Access = Seq.index
let op_Star = Prims.op_Multiply

(* Needed Insanity *)
assume MaxI8 : pow2 8 = 256
assume MaxI32: pow2 32 = 4294967296
assume MaxI64: pow2 64 = 9999999999999999999999999999


(* Define base types *)
let i8 = FStar.UInt8.t
let i32 = FStar.UInt32.t
let i64 = FStar.UInt64.t
let seq32 = Seq.seq i32
let bytes = Seq.seq i8

(* Has to be implemented and relocated *)
assume val be_8bytes_of_int: int -> Tot (b:bytes{Seq.length b = 8})
assume val be_bytes_of_seq32: a:seq32 -> Tot (b:bytes{Seq.length b = 4 * Seq.length a})
assume val be_seq32_of_bytes: a:bytes -> Tot (b:seq32{4 * (Seq.length b) = Seq.length a})


(* Define algorithm parameters *)
let hashsize = 32
let blocksize = 64


(* Section 4.1.2: Define permutations *)
let _Ch (x:i32) (y:i32) (z:i32) : Tot i32 =
  I32.logxor (I32.logand x y) (I32.logand (I32.lognot x) z)

let _Maj (x:i32) (y:i32) (z:i32) : Tot i32 =
  I32.logxor (I32.logand x y) (I32.logxor (I32.logand x z) (I32.logand y z))

let _Sigma0 (x:i32) : Tot i32 =
  I32.logxor (IOP.rotate_right x 2ul) (I32.logxor (IOP.rotate_right x 13ul) (IOP.rotate_right x 22ul))

let _Sigma1 (x:i32) : Tot i32 =
  I32.logxor (IOP.rotate_right x 6ul) (I32.logxor (IOP.rotate_right x 11ul) (IOP.rotate_right x 25ul))

let _sigma0 (x:i32) : Tot i32 =
  I32.logxor (IOP.rotate_right x 7ul) (I32.logxor (IOP.rotate_right x 18ul) (I32.shift_right x 3ul))

let _sigma1 (x:i32) : Tot i32 =
  I32.logxor (IOP.rotate_right x 17ul) (I32.logxor (IOP.rotate_right x 19ul) (I32.shift_right x 10ul))


(* Section 4.2.2: Define the constant K *)
let k_init () : Tot seq32 =
  admit(); // Required for verification timeout
  let k = Seq.create 64 0ul in
  let k = k.(0)  <- 0x428a2f98ul in
  let k = k.(1)  <- 0x71374491ul in
  let k = k.(2)  <- 0xb5c0fbcful in
  let k = k.(3)  <- 0xe9b5dba5ul in
  let k = k.(4)  <- 0x3956c25bul in
  let k = k.(5)  <- 0x59f111f1ul in
  let k = k.(6)  <- 0x923f82a4ul in
  let k = k.(7)  <- 0xab1c5ed5ul in
  let k = k.(8)  <- 0xd807aa98ul in
  let k = k.(9)  <- 0x12835b01ul in
  let k = k.(10) <- 0x243185beul in
  let k = k.(11) <- 0x550c7dc3ul in
  let k = k.(12) <- 0x72be5d74ul in
  let k = k.(13) <- 0x80deb1feul in
  let k = k.(14) <- 0x9bdc06a7ul in
  let k = k.(15) <- 0xc19bf174ul in
  let k = k.(16) <- 0xe49b69c1ul in
  let k = k.(17) <- 0xefbe4786ul in
  let k = k.(18) <- 0x0fc19dc6ul in
  let k = k.(19) <- 0x240ca1ccul in
  let k = k.(20) <- 0x2de92c6ful in
  let k = k.(21) <- 0x4a7484aaul in
  let k = k.(22) <- 0x5cb0a9dcul in
  let k = k.(23) <- 0x76f988daul in
  let k = k.(24) <- 0x983e5152ul in
  let k = k.(25) <- 0xa831c66dul in
  let k = k.(26) <- 0xb00327c8ul in
  let k = k.(27) <- 0xbf597fc7ul in
  let k = k.(28) <- 0xc6e00bf3ul in
  let k = k.(29) <- 0xd5a79147ul in
  let k = k.(30) <- 0x06ca6351ul in
  let k = k.(31) <- 0x14292967ul in
  let k = k.(32) <- 0x27b70a85ul in
  let k = k.(33) <- 0x2e1b2138ul in
  let k = k.(34) <- 0x4d2c6dfcul in
  let k = k.(35) <- 0x53380d13ul in
  let k = k.(36) <- 0x650a7354ul in
  let k = k.(37) <- 0x766a0abbul in
  let k = k.(38) <- 0x81c2c92eul in
  let k = k.(39) <- 0x92722c85ul in
  let k = k.(40) <- 0xa2bfe8a1ul in
  let k = k.(41) <- 0xa81a664bul in
  let k = k.(42) <- 0xc24b8b70ul in
  let k = k.(43) <- 0xc76c51a3ul in
  let k = k.(44) <- 0xd192e819ul in
  let k = k.(45) <- 0xd6990624ul in
  let k = k.(46) <- 0xf40e3585ul in
  let k = k.(47) <- 0x106aa070ul in
  let k = k.(48) <- 0x19a4c116ul in
  let k = k.(49) <- 0x1e376c08ul in
  let k = k.(50) <- 0x2748774cul in
  let k = k.(51) <- 0x34b0bcb5ul in
  let k = k.(52) <- 0x391c0cb3ul in
  let k = k.(53) <- 0x4ed8aa4aul in
  let k = k.(54) <- 0x5b9cca4ful in
  let k = k.(55) <- 0x682e6ff3ul in
  let k = k.(56) <- 0x748f82eeul in
  let k = k.(57) <- 0x78a5636ful in
  let k = k.(58) <- 0x84c87814ul in
  let k = k.(59) <- 0x8cc70208ul in
  let k = k.(60) <- 0x90befffaul in
  let k = k.(61) <- 0xa4506cebul in
  let k = k.(62) <- 0xbef9a3f7ul in
  let k = k.(63) <- 0xc67178f2ul in
  k


(*  Section 5.1.1: Compute the pad length (without the last 8 bytes) *)
let pad_length (len:nat) : Tot (n:nat{n <= 64}) =
  if (len % 64) < 56 then 56 - (len % 64)
  else 64 + 56 - (len % 64)


(* Pad the data up to the block length and encode the total length *)
let pad (data:bytes) : Tot (block:bytes) =

  (* Compute the padding length *)
  let padlen = pad_length (Seq.length data) in

  (* Generate the padding (without the last 8 bytes) *)
  let padding = Seq.create padlen 0uy in

  (* Set the first bit of the padding to be a '1' *)
  let padding = Seq.upd padding 0 0x80uy in

  (* Compute the MD length to be encoded as bytes *)
  let encodedlen = be_8bytes_of_int ((Seq.length data) * 8) in

  (* Concatenate the data, padding and encoded length *)
  let block = Seq.append data padding in
  let block = Seq.append block encodedlen in
  block


(* Section 5.3.3: Define the initial hash value *)
let init () : Tot (whash:seq32{Seq.length whash = 8}) =
  admit(); // Required for verification timeout
  let whash = Seq.create 8 0ul in
  let whash = whash.(0) <- 0x6a09e667ul in
  let whash = whash.(1) <- 0xbb67ae85ul in
  let whash = whash.(2) <- 0x3c6ef372ul in
  let whash = whash.(3) <- 0xa54ff53aul in
  let whash = whash.(4) <- 0x510e527ful in
  let whash = whash.(5) <- 0x9b05688cul in
  let whash = whash.(6) <- 0x1f83d9abul in
  let whash = whash.(7) <- 0x5be0cd19ul in
  whash


(* Section 6.2.2 - Step 1: Scheduling for sixty-four 32bit words *)
let rec ws (block:seq32{Seq.length block = 16}) (t:nat{t < Seq.length block}) : Tot i32 =

  (* Perform computations *)
  if t < 16 then block.(t)
  else
    let _t16 = ws block (t - 16) in
    let _t15 = ws block (t - 15) in
    let _t7  = ws block (t - 7) in
    let _t2  = ws block (t - 2) in

    let s1 = _sigma1 _t2 in
    let s0 = _sigma0 _t15 in
    (I32.add_mod s1
                 (I32.add_mod _t7
                             (I32.add_mod s0 _t16)))

#reset-options "--z3timeout 10"


(* Section 6.2.2 - Step 3: Perform logical operations on the working variables *)
let rec update_inner (whash:seq32{Seq.length whash = 8}) (block:seq32{Seq.length block = 16}) (k:seq32{Seq.length k = 64}) (t1:i32) (t2:i32) (t:nat{t <= 64}) : Tot (ohash:seq32{Seq.length ohash = 8}) =

  (* Perform computations *)
  if t < 64 then
    let _h  = whash.(7) in
    let _kt = k.(t) in
    let _wt = ws block t in
    let v0 = _Sigma1 whash.(4) in
    let v1 = _Ch whash.(4) whash.(5) whash.(6) in
    let t1 = I32.add_mod _h (I32.add_mod v0 (I32.add_mod v1 (I32.add_mod _kt _wt))) in
    let z0 = _Sigma0 whash.(0) in
    let z1 = _Maj whash.(0) whash.(1) whash.(2) in
    let t2 = I32.add_mod z0 z1 in
    let _d = whash.(3) in

    (* Update the working hash *)
    let whash = whash.(7) <- whash.(6) in
    let whash = whash.(6) <- whash.(5) in
    let whash = whash.(5) <- whash.(4) in
    let whash = whash.(4) <- (I32.add_mod _d t1) in
    let whash = whash.(3) <- whash.(2) in
    let whash = whash.(2) <- whash.(1) in
    let whash = whash.(1) <- whash.(0) in
    let whash = whash.(0) <- (I32.add_mod t1 t2) in

    (* Recursive call *)
    update_inner whash block k t1 t2 (t + 1)
  else whash


(* Section 6.2.2 - Step 1-4: Hash computation of the current block *)
let update_step (whash:seq32{Seq.length whash = 8}) (block:seq32{Seq.length block = 16}) (k:seq32{Seq.length k = 64}) : Tot (ohash:seq32{Seq.length ohash = 8}) =

  (* Step 2 : Initialize the eight working variables *)
  let iH0 = whash.(0) in
  let iH1 = whash.(1) in
  let iH2 = whash.(2) in
  let iH3 = whash.(3) in
  let iH4 = whash.(4) in
  let iH5 = whash.(5) in
  let iH6 = whash.(6) in
  let iH7 = whash.(7) in

  (* Step 3 : Perform logical operations on the working variables *)
  let oH = update_inner whash block k 0ul 0ul 0 in

  (* Step 4 : Compute the ith intermediate hash value *)
  let oH0 = I32.add_mod oH.(0) iH1 in
  let oH1 = I32.add_mod oH.(1) iH2 in
  let oH2 = I32.add_mod oH.(2) iH3 in
  let oH3 = I32.add_mod oH.(3) iH4 in
  let oH4 = I32.add_mod oH.(4) iH5 in
  let oH5 = I32.add_mod oH.(5) iH6 in
  let oH6 = I32.add_mod oH.(6) iH7 in
  let oH7 = I32.add_mod oH.(7) iH7 in

  admit(); // Required for verification timeout
  let oH = oH.(0) <- oH0 in
  let oH = oH.(1) <- oH1 in
  let oH = oH.(2) <- oH2 in
  let oH = oH.(3) <- oH3 in
  let oH = oH.(4) <- oH4 in
  let oH = oH.(5) <- oH5 in
  let oH = oH.(6) <- oH6 in
  let oH = oH.(7) <- oH7 in
  oH


(* Section 6.2.2: Hash computation for multiple blocks *)
let rec update (whash:seq32{Seq.length whash = 8}) (data:bytes) (k:seq32{Seq.length k = 64}) (max:nat) (i:nat): Tot (ohash:seq32{Seq.length ohash = 8}) =

  (* Proceed with all the block *)
  if i < max then

    (* Get the current block of data *)
    let block = Seq.slice data (i * blocksize) ((i + 1) * blocksize) in
    let wblock = be_seq32_of_bytes block in
    assume(Seq.length wblock = 16);

    (* Update the working hash with the current working block *)
    update_step whash wblock k

  else whash


(* Top level *)
let sha256 (data:bytes) : Tot (hash:bytes{Seq.length hash = hashsize}) =

  (* Preprocessing: Pad the input data *)
  let fdata = pad data in

  (* Initialize the working hash and constants *)
  let k = k_init () in
  let ihash = init () in

  (* Count and process all the message blocks *)
  let n = (Seq.length fdata) / blocksize in
  let hash = update ihash data k n 0 in

  (* Flatten the working hash and return the final value *)
  be_bytes_of_seq32 hash
