module Spec.SHA3

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul

open Spec.SHA3.Constants

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let keccak_rotc:lseq rotc_t 24 =
  assert_norm (List.Tot.length rotc_list == 24);
  createL rotc_list

let pilns_t = x:size_nat{x < 25}

let sizes_v (x:piln_t) : pilns_t = size_v x

let keccak_piln: lseq pilns_t 24 =
  let piln_list = List.Tot.map sizes_v piln_list in
  assert_norm (List.Tot.length piln_list == 24);
  createL piln_list

let keccak_rndc: lseq uint64 24 =
  assert_norm (List.Tot.length rndc_list == 24);
  createL rndc_list

unfold
type state = lseq uint64 25

unfold
type index = n:size_nat{n < 5}

let readLane (s:state) (x:index) (y:index) : uint64 =
  s.[x + 5 * y]

let writeLane (s:state) (x:index) (y:index) (v:uint64) : state =
  s.[x + 5 * y] <- v

let rotl (a:uint64) (b:uint32{0 < uint_v b /\ uint_v b < 64}) : uint64 =
  (a <<. b) |. (a >>. (u32 64 -. b))

let state_theta_inner_C (s:state) (i:size_nat{i < 5}) (_C:lseq uint64 5) : lseq uint64 5 =
  _C.[i] <- readLane s i 0 ^. readLane s i 1 ^. readLane s i 2 ^. readLane s i 3 ^. readLane s i 4

let state_theta0 (s:state) (_C:lseq uint64 5) =
  repeat 5 (fun i -> lseq uint64 5) (state_theta_inner_C s) _C

let state_theta_inner_s_inner (x:index) (_D:uint64) (y:index) (s:state) : state =
  writeLane s x y (readLane s x y ^. _D)

let state_theta_inner_s (_C:lseq uint64 5) (x:index) (s:state) : state =
  let _D = _C.[(x + 4) % 5] ^. (rotl _C.[(x + 1) % 5] (u32 1)) in
  repeat 5 (fun i -> state) (state_theta_inner_s_inner x _D) s

let state_theta1 (s:state) (_C:lseq uint64 5): state =
  repeat 5 (fun i -> state) (state_theta_inner_s _C) s

let state_theta (s:state) : state =
  let _C = create 5 (u64 0) in
  let _C = state_theta0 s _C in
  state_theta1 s _C

let state_pi_rho_inner (i:size_nat{i < 24}) (current, s) : tuple2 uint64 state =
  let r = keccak_rotc.[i] in
  let _Y = keccak_piln.[i] in
  let temp = s.[_Y] in
  let s = s.[_Y] <- rotl current r in
  let current = temp in
  current, s

let state_pi_rho (s_theta:state) : state =
  let current = readLane s_theta 1 0 in
  let _, s_pi_rho = repeat 24 (fun i -> tuple2 uint64 state) 
    state_pi_rho_inner (current, s_theta) in
  s_pi_rho

let state_chi_inner (s_pi_rho:state) (y:index) (x:index) (s:state) : state =
  writeLane s x y
    (readLane s_pi_rho x y ^.
     ((lognot (readLane s_pi_rho ((x + 1) % 5) y)) &.
      readLane s_pi_rho ((x + 2) % 5) y))

let state_chi_inner1 (s_pi_rho:state) (y:index) (s:state) : state =
  repeat 5 (fun i -> state) (state_chi_inner s_pi_rho y) s

let state_chi (s_pi_rho:state) : state  =
  repeat 5 (fun i -> state) (state_chi_inner1 s_pi_rho) s_pi_rho

let state_iota (s:state) (round:size_nat{round < 24}) : state =
  writeLane s 0 0 (readLane s 0 0 ^. keccak_rndc.[round])

let state_permute1 (round:size_nat{round < 24}) (s:state) : state =
  let s_theta = state_theta s in
  let s_pi_rho = state_pi_rho s_theta in
  let s_chi = state_chi s_pi_rho in
  let s_iota = state_iota s_chi round in
  s_iota

let state_permute (s:state) : state =
  repeat 24 (fun i -> state) state_permute1 s

let loadState_inner (block:lbytes 200) (j:size_nat{j < 25}) (s:state) : state =
  let nj = uint_from_bytes_le #U64 (sub block (j * 8) 8) in
  s.[j] <- s.[j] ^. nj

let loadState (rateInBytes:size_nat{rateInBytes <= 200})
	      (input:lbytes rateInBytes)
	      (s:state) : state =
  let block = create 200 (u8 0) in
  let block = update_sub block 0 rateInBytes input in
  repeat 25 (fun i -> state) (loadState_inner block) s

let storeState_inner (s:state) (j:size_nat{j < 25}) (block:lbytes 200) :
  res:lbytes 200{
    sub res 0 (j * 8) == sub block 0 (j * 8) /\
    sub res (j * 8) 8 == uint_to_bytes_le #U64 s.[j] /\
    sub res (j * 8 + 8) (200 - j * 8 - 8) == sub block (j * 8 + 8) (200 - j * 8 - 8)} =
  let res = update_sub block (j * 8) 8 (uint_to_bytes_le #U64 s.[j]) in
  eq_intro (sub res 0 (j * 8)) (sub block 0 (j * 8));
  eq_intro (sub res (j * 8) 8) (uint_to_bytes_le #U64 s.[j]);
  eq_intro (sub res (j * 8 + 8) (200 - j * 8 - 8)) (sub block (j * 8 + 8) (200 - j * 8 - 8));
  res

let storeState (rateInBytes:size_nat{rateInBytes <= 200})
	       (s:state) : lbytes rateInBytes =
  let block = create 200 (u8 0) in
  let block = repeat 25 (fun i -> lbytes 200) (storeState_inner s) block in
  sub block 0 rateInBytes

val absorb_last:
    s:state
  -> rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200}
  -> inputByteLen:size_nat
  -> input:lbytes inputByteLen
  -> delimitedSuffix:uint8
  -> state
let absorb_last s rateInBytes inputByteLen input delimitedSuffix =
  let lastBlock = create rateInBytes (u8 0) in
  let rem = inputByteLen % rateInBytes in
  let last: lseq uint8 rem = sub input (inputByteLen - rem) rem in
  let lastBlock = update_sub lastBlock 0 rem last in
  let lastBlock = lastBlock.[rem] <- delimitedSuffix in
  loadState rateInBytes lastBlock s

let absorb_next (s:state)
                (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200}) : state =
  let nextBlock = create rateInBytes (u8 0) in
  let nextBlock = nextBlock.[rateInBytes - 1] <- u8 0x80 in
  let s = loadState rateInBytes nextBlock s in
  state_permute s

let absorb_inner (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
                 (inputByteLen:size_nat)
                 (input:lbytes inputByteLen)
                 (i:size_nat{i < inputByteLen / rateInBytes})
		 (s:state): state =
  let s = loadState rateInBytes (sub input (i * rateInBytes) rateInBytes) s in
  state_permute s

let absorb (s:state)
           (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
	   (inputByteLen:size_nat)
	   (input:lbytes inputByteLen)
	   (delimitedSuffix:uint8) : state =
  let open Lib.RawIntTypes in
  let n = inputByteLen / rateInBytes in
  let rem = inputByteLen % rateInBytes in
  let s = repeat n (fun i -> state) (absorb_inner rateInBytes inputByteLen input) s in
  let s = absorb_last s rateInBytes inputByteLen input delimitedSuffix in
  let s =
    if (not (u8_to_UInt8 (delimitedSuffix &. u8 0x80) = 0uy) && (rem = rateInBytes - 1))
    then state_permute s else s in
  absorb_next s rateInBytes

val squeeze_inner:
    rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200}
  -> outputByteLen:size_nat
  -> i:size_nat{i < outputByteLen / rateInBytes}
  -> so:tuple2 state (lbytes (i * rateInBytes))
  -> Pure (tuple2 state (lbytes ((i + 1) * rateInBytes)))
    (requires True)
    (ensures fun (s', o') ->
      let s, o = so in
      s' == state_permute s /\
      o' == o @| storeState rateInBytes s)
let squeeze_inner rateInBytes outputByteLen i (s, o) =
  let block = storeState rateInBytes s in
  let s = state_permute s in
  s, o @| block

let squeeze (s:state)
	    (rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200})
	    (outputByteLen:size_nat)
	    : lbytes outputByteLen =
  let outBlocks = outputByteLen / rateInBytes in
  let s, output = 
    repeat outBlocks 
      (fun (i:size_nat{i <= outputByteLen / rateInBytes}) -> 
        tuple2 state (lbytes (i * rateInBytes)))
      (squeeze_inner rateInBytes outputByteLen) 
      (s, create 0 (u8 0)) in
  let remOut = outputByteLen % rateInBytes in
  let block = storeState remOut s in
  output @| block

val lemma_update_squeeze:
    rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200}
  -> outputByteLen:size_nat
  -> i:size_nat{i < outputByteLen / rateInBytes}
  -> s:state
  -> o:lbytes (i * rateInBytes)
  -> o1:lbytes ((i + 1) * rateInBytes)
  -> Lemma
    (requires
      sub o1 0 (i * rateInBytes) == sub o 0 (i * rateInBytes) /\
      sub o1 (i * rateInBytes) rateInBytes == storeState rateInBytes s)
    (ensures o1 == snd (squeeze_inner rateInBytes outputByteLen i (s, o)))
let lemma_update_squeeze rateInBytes outputByteLen i s o o1 =
  Seq.lemma_split (sub o1 0 (i * rateInBytes + rateInBytes)) (i * rateInBytes)

val keccak:
    rate:size_nat{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600}
  -> capacity:size_nat{capacity + rate == 1600}
  -> inputByteLen:size_nat
  -> input:lbytes inputByteLen
  -> delimitedSuffix:uint8
  -> outputByteLen:size_nat
  -> lbytes outputByteLen
let keccak rate capacity inputByteLen input delimitedSuffix outputByteLen =
  let rateInBytes : size_nat = rate / 8 in
  let s : state = create 25 (u64 0) in
  let s = absorb s rateInBytes inputByteLen input delimitedSuffix in
  squeeze s rateInBytes outputByteLen

let shake128 (inputByteLen:size_nat) (input:lbytes inputByteLen)
             (outputByteLen:size_nat) : lbytes outputByteLen =
  keccak 1344 256 inputByteLen input (u8 0x1F) outputByteLen

let shake256 (inputByteLen:size_nat) (input:lbytes inputByteLen)
             (outputByteLen:size_nat) : lbytes outputByteLen =
  keccak 1088 512 inputByteLen input (u8 0x1F) outputByteLen

let sha3_224 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 28 =
  keccak 1152 448 inputByteLen input (u8 0x06) 28

let sha3_256 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 32 =
  keccak 1088 512 inputByteLen input (u8 0x06) 32

let sha3_384 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 48 =
  keccak 832 768 inputByteLen input (u8 0x06) 48

let sha3_512 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 64 =
  keccak 576 1024 inputByteLen input (u8 0x06) 64

val cshake128_frodo:
    input_len:size_nat
  -> input:lbytes input_len
  -> cstm:uint16
  -> output_len:size_nat
  -> lbytes output_len
let cshake128_frodo input_len input cstm output_len =
  let s = Seq.create 25 (u64 0) in
  let s = s.[0] <- (u64 0x10010001a801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 168 input_len input (u8 0x04) in
  squeeze s 168 output_len

val cshake256_frodo:
    input_len: size_nat
  -> input: lbytes input_len
  -> cstm: uint16
  -> output_len: size_nat
  -> lbytes output_len
let cshake256_frodo input_len input cstm output_len =
  let s = Seq.create 25 (u64 0) in
  let s = s.[0] <- (u64 0x100100018801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 136 input_len input (u8 0x04) in
  squeeze s 136 output_len
