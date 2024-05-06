module Spec.SHA3

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul
open Lib.LoopCombinators

open Spec.SHA3.Constants

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

unfold
type state = lseq uint64 25

unfold
type index = n:size_nat{n < 5}

let get (s:state) (x:index) (y:index) : Tot uint64 =
  s.[x + 5 * y]

let set (s:state) (x:index) (y:index) (v:uint64) : Tot state =
  s.[x + 5 * y] <- v

let rotl (a:uint64) (b:size_t{0 < uint_v b /\ uint_v b < 64}) : Tot uint64 =
  rotate_left a b

let state_theta_inner_C (s:state) (i:size_nat{i < 5}) (_C:lseq uint64 5) : Tot (lseq uint64 5) =
  _C.[i] <- get s i 0 ^. get s i 1 ^. get s i 2 ^. get s i 3 ^. get s i 4

let state_theta0 (s:state) (_C:lseq uint64 5) =
  repeati 5 (state_theta_inner_C s) _C

let state_theta_inner_s_inner (x:index) (_D:uint64) (y:index) (s:state) : Tot state =
  set s x y (get s x y ^. _D)

let state_theta_inner_s (_C:lseq uint64 5) (x:index) (s:state) : Tot state =
  let _D = _C.[(x + 4) % 5] ^. (rotl _C.[(x + 1) % 5] (size 1)) in
  repeati 5 (state_theta_inner_s_inner x _D) s

let state_theta1 (_C:lseq uint64 5) (s:state) : Tot state =
  repeati 5 (state_theta_inner_s _C) s

let state_theta (s:state) : Tot state =
  let _C = create 5 (u64 0) in
  let _C = state_theta0 s _C in
  state_theta1 _C s

let state_pi_rho_inner (i:size_nat{i < 24}) (current, s) : (uint64 & state) =
  let r = keccak_rotc.[i] in
  let _Y = v keccak_piln.[i] in
  let temp = s.[_Y] in
  let s = s.[_Y] <- rotl current r in
  let current = temp in
  current, s

val state_pi_rho_s: i:size_nat{i <= 24} -> Type0
let state_pi_rho_s i = uint64 & state

let state_pi_rho (s_theta:state) : Tot state =
  let current = get s_theta 1 0 in
  let _, s_pi_rho = repeat_gen 24 state_pi_rho_s
    state_pi_rho_inner (current, s_theta) in
  s_pi_rho


let state_chi_inner0 (s_pi_rho:state) (y:index) (x:index) (s:state) : Tot state =
  set s x y
    (get s_pi_rho x y ^.
     ((lognot (get s_pi_rho ((x + 1) % 5) y)) &.
      get s_pi_rho ((x + 2) % 5) y))

let state_chi_inner1 (s_pi_rho:state) (y:index) (s:state) : Tot state =
  repeati 5 (state_chi_inner0 s_pi_rho y) s

let state_chi (s_pi_rho:state) : Tot state  =
  repeati 5 (state_chi_inner1 s_pi_rho) s_pi_rho

let state_iota (s:state) (round:size_nat{round < 24}) : Tot state =
  set s 0 0 (get s 0 0 ^. secret keccak_rndc.[round])

let state_permute1 (round:size_nat{round < 24}) (s:state) : Tot state =
  let s_theta = state_theta s in
  let s_pi_rho = state_pi_rho s_theta in
  let s_chi = state_chi s_pi_rho in
  let s_iota = state_iota s_chi round in
  s_iota

let state_permute (s:state) : Tot state =
  repeati 24 state_permute1 s

let loadState_inner (block:lbytes 200) (j:size_nat{j < 25}) (s:state) : Tot state =
  s.[j] <- s.[j] ^. uint_from_bytes_le #U64 (sub block (j * 8) 8)

let loadState
  (rateInBytes:size_nat{rateInBytes <= 200})
  (input:lbytes rateInBytes)
  (s:state) :
  Tot state =

  let block = create 200 (u8 0) in
  let block = update_sub block 0 rateInBytes input in
  repeati 25 (loadState_inner block) s

let storeState_inner (s:state) (j:size_nat{j < 25}) (block:lbytes 200) : Tot (lbytes 200) =
  update_sub block (j * 8) 8 (uint_to_bytes_le #U64 s.[j])

let storeState (rateInBytes:size_nat{rateInBytes <= 200}) (s:state) : Tot (lbytes rateInBytes) =
  let block = create 200 (u8 0) in
  let block = repeati 25 (storeState_inner s) block in
  sub block 0 rateInBytes

let absorb_next (s:state) (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200}) : Tot state =
  let nextBlock = create rateInBytes (u8 0) in
  let nextBlock = nextBlock.[rateInBytes - 1] <- u8 0x80 in
  let s = loadState rateInBytes nextBlock s in
  state_permute s

val absorb_last:
    delimitedSuffix:byte_t
  -> rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200}
  -> rem:size_nat{rem < rateInBytes}
  -> input:lbytes rem
  -> s:state ->
  Tot state

let absorb_last delimitedSuffix rateInBytes rem input s =
  let lastBlock = create rateInBytes (u8 0) in
  let lastBlock = update_sub lastBlock 0 rem input in
  let lastBlock = lastBlock.[rem] <- byte_to_uint8 delimitedSuffix in
  let s = loadState rateInBytes lastBlock s in
  let s =
    if not ((delimitedSuffix &. byte 0x80) =. byte 0) &&
       (rem = rateInBytes - 1)
    then state_permute s else s in
  absorb_next s rateInBytes

let absorb_inner
  (rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200})
  (block:lbytes rateInBytes)
  (s:state) :
  Tot state =

  let s = loadState rateInBytes block s in
  state_permute s

let absorb
  (s:state)
  (rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200})
  (inputByteLen:nat)
  (input:bytes{length input == inputByteLen})
  (delimitedSuffix:byte_t) :
  Tot state =

  repeat_blocks rateInBytes input
  (absorb_inner rateInBytes)
  (absorb_last delimitedSuffix rateInBytes) s

let squeeze_inner
  (rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200})
  (outputByteLen:size_nat)
  (i:size_nat{i < outputByteLen / rateInBytes})
  (s:state) :
  Tot (state & lbytes rateInBytes) =

  let block = storeState rateInBytes s in
  let s = state_permute s in
  s, block

let squeeze
  (s:state)
  (rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200})
  (outputByteLen:size_nat):
  Tot (lbytes outputByteLen) =

  let outBlocks = outputByteLen / rateInBytes in
  let a (i:nat{i <= outBlocks}) = state in
  let s, output =
    generate_blocks rateInBytes outBlocks outBlocks a
      (squeeze_inner rateInBytes outputByteLen) s
  in
  let remOut = outputByteLen % rateInBytes in
  let block = storeState remOut s in
  (to_lseq output) @| block


val keccak:
    rate:size_nat{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600}
  -> capacity:size_nat{capacity + rate == 1600}
  -> inputByteLen:nat
  -> input:bytes{length input == inputByteLen}
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_nat ->
  Tot (lbytes outputByteLen)

let keccak rate capacity inputByteLen input delimitedSuffix outputByteLen =
  let rateInBytes = rate / 8 in
  let s = create 25 (u64 0) in
  let s = absorb s rateInBytes inputByteLen input delimitedSuffix in
  squeeze s rateInBytes outputByteLen

let shake128
  (inputByteLen:nat)
  (input:bytes{length input == inputByteLen})
  (outputByteLen:size_nat) :
  Tot (lbytes outputByteLen) =

  keccak 1344 256 inputByteLen input (byte 0x1F) outputByteLen

let shake256
  (inputByteLen:nat)
  (input:bytes{length input == inputByteLen})
  (outputByteLen:size_nat) :
  Tot (lbytes outputByteLen) =

  keccak 1088 512 inputByteLen input (byte 0x1F) outputByteLen

let sha3_224 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 28 =
  keccak 1152 448 inputByteLen input (byte 0x06) 28

let sha3_256 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 32 =
  keccak 1088 512 inputByteLen input (byte 0x06) 32

let sha3_384 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 48 =
  keccak 832 768 inputByteLen input (byte 0x06) 48

let sha3_512 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 64 =
  keccak 576 1024 inputByteLen input (byte 0x06) 64
