module Spec.Keccak

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul

type state = lseq uint64 25
type index = n:size_nat{n < 5}

let lfsr86540 (lfsr:uint8) : tuple2 uint8 bool =
  let lfsr1 = lfsr &. u8 1 in
  let result = u8_to_UInt8 lfsr1 <> 0uy in
  let lfsr' = lfsr <<. u32 1 in
  if u8_to_UInt8 (lfsr &. u8 0x80) <> 0uy then
    lfsr' ^. u8 0x71, result
  else
    lfsr', result

let readLane (s:state) (x:index) (y:index) : uint64 =
  s.[x + 5 * y]

let writeLane (s:state ) (x:index) (y:index) (v:uint64) : state =
  s.[x + 5 * y] <- v

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let state_theta (s:state) : state  =
  let _C = create 5 (u64 0) in
  let _C =
    repeati 5 (fun x _C ->
      _C.[x] <-
	readLane s x 0 ^.
	readLane s x 1 ^.
	readLane s x 2 ^.
	readLane s x 3 ^.
	readLane s x 4
    ) _C in
  repeati 5 (fun x s ->
    let _D = _C.[(x + 4) % 5] ^. (_C.[(x + 1) % 5] <<<. u32 1) in
    repeati 5 (fun y s ->
      writeLane s x y (readLane s x y ^. _D)
    ) s
  ) s

let state_pi_rho (s_theta:state) : state  =
  let x : index = 1 in
  let y : index = 0 in
  let current : uint64 = readLane s_theta x y in
  let _, _, _, s_pi_rho =
    repeati 24 (fun t (tup: tuple4 index index uint64 state) ->
      let x, y, current, s = tup in
      let r : r:uint32{uint_v r < 64} = u32 (((t + 1) * (t + 2) / 2) % 64) in
      let _Y: index = (2 * x + 3 * y) % 5 in
      let x = y in
      let y = _Y in
      let temp = readLane s x y in
      let s = writeLane s x y (current <<<. r) in
      let current = temp in
      x, y, current, s
    ) (x, y, current, s_theta) in
  s_pi_rho

let state_chi (s_pi_rho:state) : state  =
  let temp = s_pi_rho in
  repeati 5 (fun y s ->
    repeati 5 (fun x s ->
      writeLane s x y
	(readLane temp x y ^.
	((lognot (readLane temp ((x + 1) % 5) y)) &. readLane temp ((x + 2) % 5) y))
    ) s
  ) s_pi_rho

let state_iota (s_chi:state) (lfsr:uint8) : tuple2 state uint8 =
  repeati 7 (fun j (s, lfsr) ->
    Math.Lemmas.pow2_le_compat 6 j;
    assert_norm (pow2 6 = 64);
    let bitPosition = u32 (pow2 j - 1) in
    let lfsr, result = lfsr86540 lfsr in
    if result then
      writeLane s 0 0 (readLane s 0 0 ^. (u64 1 <<. bitPosition)), lfsr
    else s, lfsr
  ) (s_chi, lfsr)

let state_permute1 (s:state) (lfsr:uint8) : tuple2 state uint8 =
  let s_theta = state_theta s in
  let s_pi_rho = state_pi_rho s_theta in
  let s_chi = state_chi s_pi_rho in
  let s_iota, lfsr = state_iota s_chi lfsr in
  s_iota, lfsr

let state_permute (s:state) : state =
  let lfsr = u8 0x01 in
  let s, lfsr =
    repeat 24 (fun (s, lfsr) ->
      state_permute1 s lfsr
    ) (s, lfsr) in
  s

let loadState (rateInBytes:size_nat{rateInBytes <= 200})
	      (input:lbytes rateInBytes)
	      (s:state) : state =
  let block = create 200 (u8 0) in
  let block = update_sub block 0 rateInBytes input in
  repeati 25 (fun j s ->
    let nj = uint_from_bytes_le #U64 (sub block (j * 8) 8) in
    s.[j] <- s.[j] ^. nj
  ) s

let storeState (rateInBytes:size_nat{rateInBytes <= 200})
	       (s:state) : lbytes rateInBytes =
  let block = create 200 (u8 0) in
  let block =
    repeati 25 (fun j block ->
      update_sub block (j * 8) 8 (uint_to_bytes_le #U64 s.[j])
    ) block in
  sub block 0 rateInBytes

let absorb (s:state)
           (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
	   (inputByteLen:size_nat)
	   (input:lbytes inputByteLen)
	   (delimitedSuffix:uint8) : state =
  let n = inputByteLen / rateInBytes in
  let s : state =
    repeati n (fun i s ->
      let s = loadState rateInBytes (sub input (i * rateInBytes) rateInBytes) s in
      state_permute s
    ) s in
  let rem = inputByteLen % rateInBytes in
  let last: lseq uint8 rem = sub input (inputByteLen - rem) rem in
  let lastBlock = create rateInBytes (u8 0) in
  let lastBlock = update_sub lastBlock 0 rem last in
  let lastBlock = lastBlock.[rem] <- delimitedSuffix in
  let s = loadState rateInBytes lastBlock s in

  let s =
    if (not (u8_to_UInt8 (delimitedSuffix &. u8 0x80) = 0uy) && (rem = rateInBytes - 1))
    then state_permute s else s in
  let nextBlock = create rateInBytes (u8 0) in
  let nextBlock = nextBlock.[rateInBytes - 1] <- u8 0x80 in
  let s = loadState rateInBytes nextBlock s in
  let s = state_permute s in
  s

let squeeze (s:state)
	    (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
	    (outputByteLen:size_nat)
	    : lbytes outputByteLen =
  let output = create outputByteLen (u8 0) in
  let outBlocks = outputByteLen / rateInBytes in
  let s, output =
    repeati outBlocks (fun i (s, o) ->
      let block = storeState rateInBytes s in
      let o = update_sub o (i * rateInBytes) rateInBytes block in
      let s = state_permute s in
      s, o
    ) (s, output) in
  let remOut = outputByteLen % rateInBytes in
  let outBlock = storeState remOut s in
  update_sub output (outputByteLen - remOut) remOut outBlock

let keccak (rate:size_nat{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600})
	   (capacity:size_nat{capacity + rate == 1600})
	   (inputByteLen:size_nat)
	   (input:lbytes inputByteLen)
	   (delimitedSuffix:uint8)
	   (outputByteLen:size_nat)
	   : lbytes outputByteLen =
  let rateInBytes : size_nat = rate / 8 in
  let s : state = create 25 (u64 0) in
  let s = absorb s rateInBytes inputByteLen input delimitedSuffix in
  squeeze s rateInBytes outputByteLen

let shake128 (inputByteLen:size_nat) (input:lbytes inputByteLen) (outputByteLen:size_nat) : lbytes outputByteLen =
  keccak 1344 256 inputByteLen input (u8 0x1F) outputByteLen

let shake256 (inputByteLen:size_nat) (input:lbytes inputByteLen) (outputByteLen:size_nat) : lbytes outputByteLen =
  keccak 1088 512 inputByteLen input (u8 0x1F) outputByteLen

let sha3_224 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 28 =
  keccak 1152 448 inputByteLen input (u8 0x06) 28

let sha3_256 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 32 =
  keccak 1088 512 inputByteLen input (u8 0x06) 32

let sha3_384 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 48 =
  keccak 832 768 inputByteLen input (u8 0x06) 48

let sha3_512 (inputByteLen:size_nat) (input:lbytes inputByteLen) : lbytes 64 =
  keccak 576 1024 inputByteLen input (u8 0x06) 64
