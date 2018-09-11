module Spec.SHA3

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul
open Spec.SHA3.Constants

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let keccak_rotc:lseq uint32 24 =
  assert_norm (List.Tot.length rotc_list == 24);
  createL rotc_list

let keccak_piln: lseq size_nat 24 =
  let piln_list = List.Tot.map size_v piln_list in
  assert_norm (List.Tot.length piln_list == 24);
  createL piln_list

let keccak_rndc: lseq uint64 24 =
  assert_norm (List.Tot.length rndc_list == 24);
  createL rndc_list

val lemma_keccak_rotc:
     i:size_nat{i < length keccak_rotc}
  -> Lemma (0 < uint_v keccak_rotc.[i] && uint_v keccak_rotc.[i] < 64)
let lemma_keccak_rotc i = lemma_rotc_list i

val lemma_keccak_piln:
     i:size_nat{i < length keccak_piln}
  -> Lemma (keccak_piln.[i] < 25)
let lemma_keccak_piln i = admit();
  lemma_piln_list i

type state = lseq uint64 25
type index = n:size_nat{n < 5}

let readLane (s:state) (x:index) (y:index) : uint64 =
  s.[x + 5 * y]

let writeLane (s:state ) (x:index) (y:index) (v:uint64) : state =
  s.[x + 5 * y] <- v

let rotl (a:uint64) (b:uint32{0 < uint_v b /\ uint_v b < 64}) : uint64 =
  (a <<. b) |. (a >>. (u32 64 -. b))

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
      lemma_keccak_piln i;
      lemma_keccak_rotc i;
      let temp = s.[_Y] in
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
	((lognot (readLane temp ((x + 1) % 5) y)) &.
	  readLane temp ((x + 2) % 5) y))
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

val lemma_rateInBytes:
     inputByteLen:size_nat
  -> rateInBytes:size_nat{rateInBytes > 0}
  -> i:size_nat{i < inputByteLen / rateInBytes}
  -> Lemma (i * rateInBytes + rateInBytes <= inputByteLen)
let lemma_rateInBytes inputByteLen rateInBytes i =
  let n = inputByteLen / rateInBytes in
  assert (i * rateInBytes + rateInBytes <= (n - 1) * rateInBytes + rateInBytes);
  assert ((n - 1) * rateInBytes + rateInBytes == n * rateInBytes - rateInBytes + rateInBytes);
  assert ((n - 1) * rateInBytes + rateInBytes == n * rateInBytes);
  assert (inputByteLen == inputByteLen / rateInBytes * rateInBytes + inputByteLen % rateInBytes);
  assert (n * rateInBytes <= inputByteLen)

let absorb (s:state)
           (rateInBytes:size_nat{rateInBytes > 0 /\ rateInBytes <= 200})
	   (inputByteLen:size_nat)
	   (input:lbytes inputByteLen)
	   (delimitedSuffix:uint8) : state =
  let n = inputByteLen / rateInBytes in
  let rem = inputByteLen % rateInBytes in
  let s : state =
    repeati n (fun i s ->
      lemma_rateInBytes inputByteLen rateInBytes i;
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
      lemma_rateInBytes outputByteLen rateInBytes i;
      let block = storeState rateInBytes s in
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
