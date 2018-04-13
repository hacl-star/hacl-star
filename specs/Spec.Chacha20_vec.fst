module Spec.Chacha20_vec

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

(* This should go elsewhere! *)

#reset-options "--max_fuel 0 --z3rlimit 100"

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type nonce = lbytes noncelen
type counter = size_nat

// using @ as a functional substitute for ;
// internally, blocks are represented as 16 x 4-byte integers
type vec   = lseq uint32 4
type state = lseq vec 4
type idx = n:nat{n < 4}
type shuffle = state -> Tot state

let op_Plus_Percent_Hat (x:vec) (y:vec) : Tot vec =
       map2 (add_mod #U32) x y

let op_Hat_Hat (x:vec) (y:vec) : Tot vec =
       map2 (logxor #U32) x y

let op_Less_Less_Less (x:vec) (n:rotval U32) : Tot vec =
       map (fun x -> rotate_left #U32 x n) x

let shuffle_right (x:vec) (n:idx) : Tot vec =
        let z:nat = n in
        let x0 = index x ((0+z)%4) in
        let x1 = index x ((1+z)%4) in
        let x2 = index x ((2+z)%4) in
        let x3 = index x ((3+z)%4) in
	let x = upd x 0 x0 in
	let x = upd x 1 x1 in
	let x = upd x 2 x2 in
	let x = upd x 3 x3 in
	x

let shuffle_row (i:idx) (n:idx) (s:state) : Tot state =
       upd s i (shuffle_right (index s i) n)

val line: idx -> idx -> idx -> rotval U32 -> st:state -> Tot state
let line a b d s m =
  let ma = index m a in let mb = index m b in let md = index m d in
  let ma = ma +%^ mb in
  let md = (md ^^  ma) <<< s in
  let m = upd m a ma in
  let m = upd m d md in
  m

let round (st:state) : Tot state =
  let st = line 0 1 3 (u32 16) st in
  let st = line 2 3 1 (u32 12) st in
  let st = line 0 1 3 (u32 8)  st in
  let st = line 2 3 1 (u32 7)  st in
  st

let shuffle_rows_0123 (st:state) : Tot state =
  let st = shuffle_row 1 1 st in
  let st = shuffle_row 2 2 st in
  let st = shuffle_row 3 3 st in
  st

let shuffle_rows_0321 (st:state) : Tot state =
  let st = shuffle_row 1 3 st in
  let st = shuffle_row 2 2 st in
  let st = shuffle_row 3 1 st in
  st

let column_round (st:state) : Tot state = round st

let diagonal_round (st:state) : Tot state =
  let st = shuffle_rows_0123 st in
  let st = round           st in
  let st = shuffle_rows_0321 st in
  st

let double_round (st:state) : Tot state =
  let st = column_round st in
  let st = diagonal_round st in
  st

let rounds (st:state) : Tot state =
    repeat 10 double_round st (* 20 rounds *)

let chacha20_core (s:state) : Tot state =
    let s' = rounds s in
    map2 (+%^) s' s

(* state initialization *)
let c0 = u32 0x61707865
let c1 = u32 0x3320646e
let c2 = u32 0x79622d32
let c3 = u32 0x6b206574
let constants : list uint32 = [c0;c1;c2;c3]

#reset-options "--z3rlimit 100"
// JK: I have to add those assertions to typechecks, would be nice to get rid of it
let chacha20_init (k:key) (n:nonce) : Tot state =
  assert_norm(List.Tot.length constants == 4);
  let constants : vec = createL #uint32 constants in
  let key_part_1:vec =  uints_from_bytes_le #U32 (slice k 0 16)  in
  let key_part_2:vec = uints_from_bytes_le #U32 (slice k 16 32) in
  let nonce :vec = create 4 (u32 0) in
  let nonce :vec = update_slice nonce 1 4 (uints_from_bytes_le #U32 n) in
  createL [constants; key_part_1; key_part_2; nonce]


let chacha20_set_counter (st:state) (c:counter) : Tot state =
  let st3 = st.[3] in
  let st3 = st3.[0] <- u32 c in
  st.[3] <- st3

let chacha20_key_block (st:state): Tot block =
    let st' : state  = chacha20_core st in
    let b : block = create 64 (u8 0) in
    let b : block = update_sub b 0 16 (uints_to_bytes_le #U32 st'.[0]) in
    let b : block = update_sub b 16 16 (uints_to_bytes_le #U32 st'.[1]) in
    let b : block = update_sub b 32 16 (uints_to_bytes_le #U32 st'.[2]) in
    let b : block = update_sub b 48 16 (uints_to_bytes_le #U32 st'.[3]) in
    b


let chacha20_block (k:key) (n:nonce) (c:counter): Tot block =
    let st = chacha20_init k n in
    let st = chacha20_set_counter st c in
    chacha20_key_block st

let chacha20_cipher =
  Spec.CTR.Cipher state keylen noncelen max_size_t blocklen chacha20_init chacha20_set_counter chacha20_key_block

let chacha20_encrypt_bytes key nonce counter len m =
  Spec.CTR.counter_mode chacha20_cipher key nonce counter len m

