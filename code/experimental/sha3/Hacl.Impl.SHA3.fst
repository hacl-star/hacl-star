module Hacl.Impl.SHA3

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.PQ.Buffer
open Lib.Endianness

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

inline_for_extraction noextract
let v = size_v

inline_for_extraction noextract
let state = lbuffer uint64 25

inline_for_extraction noextract
let index = n:size_t{v n < 5}

val lfsr86540:
    lfsr:lbytes 1
  -> Stack bool
    (requires fun h -> live h lfsr)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer lfsr) h0 h1)
[@"c_inline"]
let lfsr86540 lfsr =
  let open Lib.RawIntTypes in
  let lfsr0 = lfsr.(size 0) in
  let lfsr1 = lfsr0 &. u8 1 in
  let result = u8_to_UInt8 lfsr1 <> 0uy in
  let lfsr' = lfsr0 <<. u32 1 in
  let lfsr' =
    if u8_to_UInt8 (lfsr0 &. u8 0x80) <> 0uy
    then lfsr' ^. u8 0x71 else lfsr' in
  lfsr.(size 0) <- lfsr';
  result

inline_for_extraction noextract
val readLane:
     s:state
  -> x:index
  -> y:index
  -> Stack uint64
    (requires fun h -> live h s)
    (ensures  fun h0 r h1 -> modifies loc_none h0 h1)
let readLane s x y = s.(x +! size 5 *! y)

inline_for_extraction noextract
val writeLane:
     s:state
  -> x:index
  -> y:index
  -> v:uint64
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 r h1 -> modifies (loc_buffer s) h0 h1)
let writeLane s x y v = s.(x +! size 5 *! y) <- v

val state_theta:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
[@"c_inline"]
let state_theta s =
  push_frame();
  let _C:lbuffer uint64 5 = create (size 5) (u64 0) in
  let h0 = ST.get () in
  loop_nospec #h0 (size 5) _C
  (fun x ->
    _C.(x) <-
      readLane s x (size 0) ^.
      readLane s x (size 1) ^.
      readLane s x (size 2) ^.
      readLane s x (size 3) ^.
      readLane s x (size 4)
  );

  let h0 = ST.get () in
  loop_nospec #h0 (size 5) s
  (fun x ->
    let _D = _C.((x +. size 4) %. size 5) ^. (_C.((x +. size 1) %. size 5) <<<. u32 1) in
    let h1 = ST.get () in
    loop_nospec #h1 (size 5) s
    (fun y ->
      writeLane s x y (readLane s x y ^. _D)
    )
  );
  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val state_pi_rho:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let state_pi_rho s =
  push_frame();
  let x:lbuffer size_t 1 = create (size 1) (size 1) in
  let y:lbuffer size_t 1 = create (size 1) (size 0) in
  let current:lbuffer uint64 1 = create (size 1) (readLane s (size 1) (size 0)) in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 24)
  (fun h1 t ->
    live h1 x /\ live h1 y /\ live h1 current /\ live h1 s /\
    //v (get h1 x 0) < 5 /\ v (get h1 y 0) < 5 /\
    modifies (loc_union (loc_union (loc_buffer x) (loc_buffer y)) (loc_union (loc_buffer current) (loc_buffer s))) h0 h1)
  (fun t ->
    let h0 = ST.get () in
    assume (v (get h0 x 0) < 5 /\ v (get h0 y 0) < 5);

    let x0:index = x.(size 0) in
    let y0:index = y.(size 0) in
    let current0:uint64 = current.(size 0) in

    let r : r:uint32{uint_v r < 64} = size_to_uint32 (((t +. size 1) *. (t +. size 2) /. size 2) %. size 64) in
    let _Y:index = (size 2 *. x0 +. size 3 *. y0) %. size 5 in
    let temp = readLane s y0 _Y in
    assume (0 < uint_v r /\ uint_v r < 64);
    writeLane s y0 _Y (current0 <<<. r);

    x.(size 0) <- y0;
    y.(size 0) <- _Y;
    current.(size 0) <- temp
  );
  pop_frame()

inline_for_extraction noextract
val state_chi:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let state_chi s =
  push_frame ();
  let temp:state = create (size 25) (u64 0) in
  update_sub temp (size 0) (size 25) s;
  let h0 = ST.get () in
  loop_nospec #h0 (size 5) s
  (fun y ->
    let h1 = ST.get () in
    loop_nospec #h1 (size 5) s
    (fun x ->
      writeLane s x y
	(readLane temp x y ^.
	((lognot (readLane temp ((x +. size 1) %. size 5) y)) &. readLane temp ((x +. size 2) %. size 5) y))
    )
  );
  pop_frame ()

inline_for_extraction noextract
val state_iota:
     s:state
  -> lfsr:lbytes 1
  -> Stack unit
    (requires fun h -> live h s /\ live h lfsr /\ disjoint s lfsr)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer s) (loc_buffer lfsr)) h0 h1)
let state_iota s lfsr =
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 7)
  (fun h1 j ->
    live h1 lfsr /\ live h1 s /\
    modifies (loc_union (loc_buffer s) (loc_buffer lfsr)) h0 h1)
  (fun j ->
    let bitPosition = (u32 1 <<. size_to_uint32 j) -. u32 1 in
    assume (uint_v bitPosition < 64);
    let result = lfsr86540 lfsr in
    (if result then
      writeLane s (size 0) (size 0)
	(readLane s (size 0) (size 0) ^. (u64 1 <<. bitPosition)))
  )

val state_permute1:
     s:state
  -> lfsr:lbytes 1
  -> Stack unit
    (requires fun h -> live h s /\ live h lfsr /\ disjoint s lfsr)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer s) (loc_buffer lfsr)) h0 h1)
[@"c_inline"]
let state_permute1 s lfsr =
  state_theta s;
  state_pi_rho s;
  state_chi s;
  state_iota s lfsr

val state_permute:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
[@"c_inline"]
let state_permute s =
  push_frame();
  let lfsr:lbytes 1 = create (size 1) (u8 0x01) in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 24)
  (fun h1 i ->
    live h1 lfsr /\ live h1 s /\
    modifies (loc_union (loc_buffer lfsr) (loc_buffer s)) h0 h1)
  (fun i ->
    state_permute1 s lfsr
  );
  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val loadState:
     rateInBytes:size_t{v rateInBytes <= 200}
  -> input:lbytes (v rateInBytes)
  -> s:state
  -> Stack unit
    (requires fun h -> live h input /\ live h s /\ disjoint input s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
[@"c_inline"]
let loadState rateInBytes input s =
  push_frame();
  let block:lbytes 200 = create (size 200) (u8 0) in
  update_sub block (size 0) rateInBytes input;
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 25)
  (fun h1 j ->
    live h1 block /\ live h1 s /\
    modifies (loc_buffer s) h0 h1)
  (fun j ->
    s.(j) <- s.(j) ^. uint_from_bytes_le #U64 (sub #_ #200 #8 block (j *! size 8) (size 8))
  );
  pop_frame()

val storeState:
     rateInBytes:size_t{v rateInBytes <= 200}
  -> s:state
  -> res:lbytes (v rateInBytes)
  -> Stack unit
    (requires fun h -> live h s /\ live h res /\ disjoint s res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let storeState rateInBytes s res =
  push_frame();
  let block:lbytes 200 = create (size 200) (u8 0) in
  let h0 = ST.get () in
  loop_nospec #h0 (size 25) block
  (fun j ->
    uint_to_bytes_le (sub block (j *! size 8) (size 8)) s.(j)
  );
  update_sub res (size 0) rateInBytes (sub block (size 0) rateInBytes);
  pop_frame()

inline_for_extraction noextract
val absorb_last:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:uint8
  -> Stack unit
    (requires fun h -> live h s /\ live h input /\ disjoint s input)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let absorb_last s rateInBytes inputByteLen input delimitedSuffix =
  push_frame ();
  let lastBlock = create rateInBytes (u8 0) in
  let rem = inputByteLen %. rateInBytes in
  let last = sub input (inputByteLen -. rem) rem in
  update_sub lastBlock (size 0) rem last;
  lastBlock.(rem) <- delimitedSuffix;
  loadState rateInBytes lastBlock s;
  pop_frame ()

inline_for_extraction noextract
val absorb_next:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let absorb_next s rateInBytes =
  push_frame ();
  let nextBlock = create rateInBytes (u8 0) in
  nextBlock.(rateInBytes -! size 1) <- u8 0x80;
  loadState rateInBytes nextBlock s;
  state_permute s;
  pop_frame ()

val absorb:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:uint8
  -> Stack unit
    (requires fun h -> live h s /\ live h input /\ disjoint s input)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
[@"c_inline"]
let absorb s rateInBytes inputByteLen input delimitedSuffix =
  let open Lib.RawIntTypes in
  let n = inputByteLen /. rateInBytes in
  let rem = inputByteLen %. rateInBytes in
  let h0 = ST.get () in
  loop_nospec #h0 n s
  (fun i ->
    assume (v i * v rateInBytes + v rateInBytes <= v inputByteLen);
    loadState rateInBytes (sub #_ #(v inputByteLen) #(v rateInBytes) input (i *! rateInBytes) rateInBytes) s;
    state_permute s
  );
  absorb_last s rateInBytes inputByteLen input delimitedSuffix;
  (if (not (u8_to_UInt8 (delimitedSuffix &. u8 0x80) = 0uy) && (size_to_UInt32 rem = size_to_UInt32 (rateInBytes -. size 1)))
  then state_permute s);
  absorb_next s rateInBytes

val squeeze:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h -> live h s /\ live h output /\ disjoint s output)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer s) (loc_buffer output)) h0 h1)
[@"c_inline"]
let squeeze s rateInBytes outputByteLen output =
  let outBlocks = outputByteLen /. rateInBytes in
  let remOut = outputByteLen %. rateInBytes in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) outBlocks
  (fun h1 i ->
    live h1 s /\ live h1 output /\
    modifies (loc_union (loc_buffer s) (loc_buffer output)) h0 h1)
  (fun i ->
    assume (v i * v rateInBytes + v rateInBytes <= v outputByteLen);
    storeState rateInBytes s (sub output (i *! rateInBytes) rateInBytes);
    state_permute s
  );
  storeState remOut s (sub output (outputByteLen -. remOut) remOut)

val keccak:
     rate:size_t{v rate % 8 = 0 /\ v rate / 8 > 0 /\ v rate <= 1600}
  -> capacity:size_t{v capacity + v rate == 1600}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:uint8
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let keccak rate capacity inputByteLen input delimitedSuffix outputByteLen output =
  push_frame();
  let rateInBytes = rate /. size 8 in
  let s:state = create (size 25) (u64 0) in
  absorb s rateInBytes inputByteLen input delimitedSuffix;
  squeeze s rateInBytes outputByteLen output;
  pop_frame()
