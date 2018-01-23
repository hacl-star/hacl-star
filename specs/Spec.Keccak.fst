module Spec.Keccak

open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open FStar.Mul

let lfsr86540 (lfsr:uint8) : tuple2 uint8 bool =
  let lfsr1 : uint8 = lfsr &. u8 1 in
  let result : bool = u8_to_UInt8 lfsr1 <> 0uy in
  let lfsr' : uint8 = lfsr <<. u32 1 in
  if (u8_to_UInt8 (lfsr &. u8 0x80) <> 0uy) then
    lfsr' ^. u8 0x71, result
  else
    lfsr', result

type state = lseq uint64 25
type index = n:size_nat{n < 5}

let readLane (s:state) (x:index) (y:index) : uint64 =
  s.[x * 5 + y]

let writeLane (s:state ) (x:index) (y:index) (v:uint64) : state =
  s.[x * 5 + y] <- v


let state_permute1 (s:state) (lfsr:uint8) : tuple2 state uint8 =
  let _C = create 5 (u64 0) in
  let _C = repeati 5 (fun x _C -> _C.[x] <- readLane s x 0 ^. readLane s x 1 ^. readLane s x 2 ^. readLane s x 3 ^. readLane s x 4) _C in
  let s_theta = repeati 5 (fun x s ->
		      let _D = _C.[(x+4)%5] ^. (_C.[(x+1)%5] <<<. (u32 1)) in
		      repeati 5 (fun y s -> writeLane s x y (readLane s x y ^. _D)) s) s in

  let x : index = 1 in
  let y : index = 0 in
  let current : uint64 = readLane s_theta x y in
  let (_,_,_,s_pi_rho) = repeati 25 (fun t (tup: tuple4 index index uint64 state) ->
			       let (x,y,current,s) = tup in
			       let r : uint32 = u32 (((t + 1) * (t + 2)/2) % 64) in
			       let _Y: index = ((2 * x + 3 * y) % 5) in
			       let x = y in
			       let y = _Y in
			       let temp = readLane s x y in
			       let s = writeLane s x y (current <<<. r) in
			       let current = temp in
			       (x,y,current,s)) (x,y,current,s_theta) in

  let s_copy = s_pi_rho in
  let s_chi = repeati 5 (fun y s -> repeati 5 (fun x s -> writeLane s x y
						    ((readLane s_copy x y) ^.
						    ((lognot (readLane s_copy ((x+1)%5) y)) &.
						     (readLane s_copy ((x+2)%5) y)))) s) s_pi_rho in
  let (s_iota,lfsr) = repeati 7 (fun j (s,lfsr) -> Math.Lemmas.pow2_le_compat 6 j;
				  assert_norm (pow2 6 = 64);
                                  let bitPosition = u32 ((pow2 j) - 1) in
				  let (lfsr,result) = lfsr86540 lfsr in
				  if result then
				    (writeLane s 0 0 ((readLane s_chi 0 0) ^. ((u64 1) <<. bitPosition)), lfsr)
				  else (s,lfsr))
			 (s_chi,lfsr) in
  (s_iota,lfsr)

let state_permute (s:state) : state =
  let lfsr = u8 1 in
  let (s,lfsr) = repeat 25 (fun (s,lfsr) -> state_permute1 s lfsr) (s,lfsr) in
  s


let loadState (rate: size_t{rate <= 200}) (input: lbytes rate) (s:state) : state =
  let block = create 200 (u8 0) in
  let block = update_slice block 0 rate input in
  repeati 25 (fun j s ->
    let nj = uint_from_bytes_le #U64 (slice block (j*8) ((j*8) + 8)) in
    s.[j] <- (s.[j] ^. nj) ) s

let storeState (rate: size_t{rate <= 200}) (s:state) : lbytes rate =
  let block = create 200 (u8 0) in
  let block = repeati 25 (fun j block -> update_slice block (j * 8) (j*8 + 8) (uint_to_bytes_le #U64 s.[j])) block in
  slice block 0 rate

let sponge (rate:size_t{rate > 0 /\ rate <= 200})
	   (inputByteLen:size_t)
	   (input:lbytes inputByteLen)
	   (delimitedSuffix:uint8) : state =
   let s : state = create 25 (u64 0) in
   let blocks = inputByteLen / rate in
   let s : state = repeati blocks
       (fun i s ->
	  let s = loadState rate (slice input (i*rate) (i*rate + rate)) s in
	  state_permute s) s in
   let rem = inputByteLen - (blocks * rate) in
   let last = slice input (inputByteLen - rem) inputByteLen in
   let lastBlock = create rate (u8 0) in
   let lastBlock = update_slice lastBlock 0 rem last in
   let lastBlock = lastBlock.[rem] <- delimitedSuffix in
   let s = loadState rate lastBlock s in
   let s = if ((u8_to_UInt8 (delimitedSuffix &. u8 0x80) = 0uy) && (rem = rate - 1))
	   then state_permute s
	   else s in
   let nextBlock = create rate (u8 0) in
   let nextBlock = nextBlock.[rate - 1] <- u8 0x80 in
   let s = loadState rate nextBlock s in
   s

let squeeze (s:state)
	    (rate:size_t{rate > 0 /\ rate < 200})
	    (outputByteLen: size_t)
	    : lbytes outputByteLen =
   let output = create outputByteLen (u8 0) in
   let outBlocks = outputByteLen / rate in
   let (s,output) = repeati outBlocks
       (fun i (s,o) ->
	  let block = storeState rate s in
          let o = update_slice o (i*rate) (i*rate + rate) block in
          let s = state_permute s in
          (s,o)) (s,output) in
   let remOut = outputByteLen - (outBlocks * rate) in
   let outBlock = storeState remOut s in
   update_slice output (outputByteLen - remOut) outputByteLen outBlock


let keccak (rate:size_t{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600})
	   (capacity:size_t{capacity + rate == 1600})
	   (inputByteLen:size_t)
	   (input:lbytes inputByteLen) (delimitedSuffix:uint8)
	   (outputByteLen:size_t)
	   : lbytes outputByteLen =
   let rateInBytes : size_t = rate / 8 in
   let s = sponge rateInBytes inputByteLen input delimitedSuffix in
   squeeze s rateInBytes outputByteLen
