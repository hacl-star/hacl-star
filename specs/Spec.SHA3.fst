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

val writeLane:
     s:state
  -> x:index
  -> y:index
  -> v:uint64
  -> r:state{readLane r x y == v /\ (forall i j. (i, j) <> (x, y) ==> readLane r i j == readLane s i j)}
let writeLane s x y v = s.[x + 5 * y] <- v

let rotl (a:uint64) (b:uint32{0 < uint_v b /\ uint_v b < 64}) : uint64 =
  (a <<. b) |. (a >>. (u32 64 -. b))

let state_theta_inner_C (s:state) (i:nat{i < 5}) =
  readLane s i 0 ^.
  readLane s i 1 ^.
  readLane s i 2 ^.
  readLane s i 3 ^.
  readLane s i 4

let state_theta0 (s:state) : lseq uint64 5 =
  let _C = create 5 (u64 0) in
  let _C =
    repeati_inductive 5
    (fun x _C ->
      forall (i:size_nat{i < x}). _C.[i] == state_theta_inner_C s i)
    (fun x _C ->
      _C.[x] <- state_theta_inner_C s x
    ) _C in
  _C

let state_theta1 (s':state) (_C:lseq uint64 5) : state =
  repeati_inductive 5
  (fun x s ->
    forall (i:size_nat{i < x}) (j:size_nat{j < 5}).
      let _D = _C.[(i + 4) % 5] ^. (rotl _C.[(i + 1) % 5] (u32 1)) in
      readLane s i j == readLane s' i j ^. _D)
  (fun x s ->
    let _D = _C.[(x + 4) % 5] ^. (rotl _C.[(x + 1) % 5] (u32 1)) in
    repeati_inductive 5
    (fun y s0 ->
      (forall (i:size_nat{i < x}) (j:size_nat{j < 5}). readLane s0 i j == readLane s i j) /\
      (forall (j:size_nat{j < y}). readLane s0 x j == readLane s' x j ^. _D))
    (fun y s0 ->
      writeLane s0 x y (readLane s' x y ^. _D)
    ) s
  ) s'

let state_theta (s:state) : state =
  let _C = state_theta0 s in
  state_theta1 s _C

val state_pi_rho_inner:
     current:uint64
  -> s:state
  -> i:size_nat{i < 24}
  -> tuple2 uint64 state
let state_pi_rho_inner current s i =
  lemma_keccak_piln i;
  lemma_keccak_rotc i;
  let r = keccak_rotc.[i] in
  let _Y = keccak_piln.[i] in
  let s1 = s.[_Y] <- rotl current r in
  let current = s.[_Y] in
  current, s1

let state_pi_rho (s_theta:state) : state =
  let current : uint64 = readLane s_theta 1 0 in
  let _, s_pi_rho =
    repeati_inductive 24
    (fun i (current, s) -> True)
    (fun i (current, s) ->
      state_pi_rho_inner current s i
    ) (current, s_theta) in
  s_pi_rho

val state_chi_inner:
     s:state
  -> x:index
  -> y:index
  -> uint64
let state_chi_inner s x y =
  readLane s x y ^.
  ((lognot (readLane s ((x + 1) % 5) y)) &.
    readLane s ((x + 2) % 5) y)

let state_chi (s_pi_rho:state) : state  =
  repeati_inductive 5
  (fun y s ->
    forall (j:size_nat{j < y}) (i:size_nat{i < 5}). readLane s i j == state_chi_inner s_pi_rho i j)
  (fun y s ->
    repeati_inductive 5
    (fun x s0 ->
      (forall (j:size_nat{j < y}) (i:size_nat{i < 5}). readLane s i j == readLane s0 i j) /\
      (forall (i:size_nat{i < x}). readLane s0 i y == state_chi_inner s_pi_rho i y))
    (fun x s0 ->
      writeLane s0 x y (state_chi_inner s_pi_rho x y)
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
