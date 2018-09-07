module Spec.Keccak

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

type state = lseq uint64 25
type index = n:size_nat{n < 5}

let readLane (s:state) (x:index) (y:index) : uint64 =
  s.[x + 5 * y]

let writeLane (s:state ) (x:index) (y:index) (v:uint64) : state =
  s.[x + 5 * y] <- v

let rotl (a:uint64) (b:uint32{0 < uint_v b /\ uint_v b < 64}) : uint64 =
  (a <<. b) |. (a >>. (u32 64 -. b))

let keccak_rotc: lseq uint32 24 =
  let rotc_list: list uint32 =
    [u32 1; u32 3; u32 6; u32 10; u32 15; u32 21; u32 28; u32 36;
     u32 45; u32 55; u32 2; u32 14; u32 27; u32 41; u32 56; u32 8;
     u32 25; u32 43; u32 62; u32 18; u32 39; u32 61; u32 20; u32 44] in
  assert_norm (List.Tot.length rotc_list == 24);
  createL rotc_list

let keccak_piln: lseq size_nat 24 =
  let piln_list: list size_nat = List.Tot.map size_v
    [size 10; size 7; size 11; size 17; size 18; size 3; size 5; size 16;
     size 8; size 21; size 24; size 4; size 15; size 23; size 19; size 13;
     size 12; size 2; size 20; size 14; size 22; size 9; size 6; size 1] in
  assert_norm (List.Tot.length piln_list == 24);
  createL piln_list

let keccak_rndc: lseq uint64 24 =
  let rndc_list: list uint64 =
    [u64 0x0000000000000001; u64 0x0000000000008082; u64 0x800000000000808a; u64 0x8000000080008000;
     u64 0x000000000000808b; u64 0x0000000080000001; u64 0x8000000080008081; u64 0x8000000000008009;
     u64 0x000000000000008a; u64 0x0000000000000088; u64 0x0000000080008009; u64 0x000000008000000a;
     u64 0x000000008000808b; u64 0x800000000000008b; u64 0x8000000000008089; u64 0x8000000000008003;
     u64 0x8000000000008002; u64 0x8000000000000080; u64 0x000000000000800a; u64 0x800000008000000a;
     u64 0x8000000080008081; u64 0x8000000000008080; u64 0x0000000080000001; u64 0x8000000080008008] in
  assert_norm (List.Tot.length rndc_list == 24);
  createL rndc_list

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
    let _D = _C.[(x + 4) % 5] ^. (rotl _C.[(x + 1) % 5] (u32 1)) in
    repeati 5 (fun y s ->
      writeLane s x y (readLane s x y ^. _D)
    ) s
  ) s

let state_pi_rho (s_theta:state) : state  =
  let current : uint64 = readLane s_theta 1 0 in
  let _, s_pi_rho =
    repeati 24 (fun i (current, s) ->
      let r = keccak_rotc.[i] in
      let _Y = keccak_piln.[i] in
      assume (_Y < 25);
      let temp = s.[_Y] in
      assume (0 < uint_v r /\ uint_v r < 64);
      let s = s.[_Y] <- rotl current r in
      let current = temp in
      current, s
    ) (current, s_theta) in
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

let state_iota (s:state) (round:size_nat{round < 24}) : state =
  writeLane s 0 0 (readLane s 0 0 ^. keccak_rndc.[round])

let state_permute1 (s:state) (round:size_nat{round < 24}) : state =
  let s_theta = state_theta s in
  let s_pi_rho = state_pi_rho s_theta in
  let s_chi = state_chi s_pi_rho in
  let s_iota = state_iota s_chi round in
  s_iota

let state_permute (s:state) : state =
  repeati 24 (fun i s ->
    state_permute1 s i
  ) s

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

let absorb_last (s:state)
                (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
                (inputByteLen:size_nat)
                (input:lbytes inputByteLen)
                (delimitedSuffix:uint8) : state =
  let lastBlock = create rateInBytes (u8 0) in
  let rem = inputByteLen % rateInBytes in
  let last: lseq uint8 rem = sub input (inputByteLen - rem) rem in
  let lastBlock = update_sub lastBlock 0 rem last in
  let lastBlock = lastBlock.[rem] <- delimitedSuffix in
  let s = loadState rateInBytes lastBlock s in
  s

let absorb_next (s:state)
                (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200}) : state =
  let nextBlock = create rateInBytes (u8 0) in
  let nextBlock = nextBlock.[rateInBytes - 1] <- u8 0x80 in
  let s = loadState rateInBytes nextBlock s in
  let s = state_permute s in
  s

let absorb (s:state)
           (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
	   (inputByteLen:size_nat)
	   (input:lbytes inputByteLen)
	   (delimitedSuffix:uint8) : state =
  let n = inputByteLen / rateInBytes in
  let rem = inputByteLen % rateInBytes in
  let s : state =
    repeati n (fun i s ->
      assume (i * rateInBytes + rateInBytes <= inputByteLen);
      let s = loadState rateInBytes (sub input (i * rateInBytes) rateInBytes) s in
      state_permute s
    ) s in
  let s = absorb_last s rateInBytes inputByteLen input delimitedSuffix in
  let s =
    if (not (u8_to_UInt8 (delimitedSuffix &. u8 0x80) = 0uy) && (rem = rateInBytes - 1))
    then state_permute s else s in
  let s = absorb_next s rateInBytes in
  s

let squeeze (s:state)
	    (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
	    (outputByteLen:size_nat)
	    : lbytes outputByteLen =
  let output = create outputByteLen (u8 0) in
  let outBlocks = outputByteLen / rateInBytes in
  let remOut = outputByteLen % rateInBytes in
  let s, output =
    repeati outBlocks (fun i (s, o) ->
      let block = storeState rateInBytes s in
      assume (i * rateInBytes + rateInBytes <= outputByteLen);
      let o = update_sub o (i * rateInBytes) rateInBytes block in
      let s = state_permute s in
      s, o
    ) (s, output) in
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
