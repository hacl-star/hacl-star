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

[@"c_inline"]
let rotl (a:uint64) (b:uint32{0 < uint_v b /\ uint_v b < 64}) : uint64 =
  (a <<. b) |. (a >>. (u32 64 -. b))

let keccak_rotc: b:lbuffer uint32 24 { LowStar.Buffer.recallable b } =
  [@ inline_let]
  let rotc_list: list uint32 =
    [u32 1; u32 3; u32 6; u32 10; u32 15; u32 21; u32 28; u32 36;
     u32 45; u32 55; u32 2; u32 14; u32 27; u32 41; u32 56; u32 8;
     u32 25; u32 43; u32 62; u32 18; u32 39; u32 61; u32 20; u32 44] in
  assert_norm (List.Tot.length rotc_list == 24);
  createL_global rotc_list

let keccak_piln: b:lbuffer size_t 24 { LowStar.Buffer.recallable b } =
  [@ inline_let]
  let piln_list: list size_t =
    [size 10; size 7; size 11; size 17; size 18; size 3; size 5; size 16;
     size 8; size 21; size 24; size 4; size 15; size 23; size 19; size 13;
     size 12; size 2; size 20; size 14; size 22; size 9; size 6; size 1] in
  assert_norm (List.Tot.length piln_list == 24);
  createL_global piln_list

let keccak_rndc: b:lbuffer uint64 24 { LowStar.Buffer.recallable b } =
  [@ inline_let]
  let rndc_list: list uint64 =
    [u64 0x0000000000000001; u64 0x0000000000008082; u64 0x800000000000808a; u64 0x8000000080008000;
     u64 0x000000000000808b; u64 0x0000000080000001; u64 0x8000000080008081; u64 0x8000000000008009;
     u64 0x000000000000008a; u64 0x0000000000000088; u64 0x0000000080008009; u64 0x000000008000000a;
     u64 0x000000008000808b; u64 0x800000000000008b; u64 0x8000000000008089; u64 0x8000000000008003;
     u64 0x8000000000008002; u64 0x8000000000000080; u64 0x000000000000800a; u64 0x800000008000000a;
     u64 0x8000000080008081; u64 0x8000000000008080; u64 0x0000000080000001; u64 0x8000000080008008] in
  assert_norm (List.Tot.length rndc_list == 24);
  createL_global rndc_list

inline_for_extraction noextract
val state_theta:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
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
    let _D = _C.((x +. size 4) %. size 5) ^. (rotl _C.((x +. size 1) %. size 5) (u32 1)) in
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
  let current:lbuffer uint64 1 = create (size 1) (readLane s (size 1) (size 0)) in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 24)
  (fun h1 t ->
    live h1 current /\ live h1 s /\
    modifies (loc_union (loc_buffer current) (loc_buffer s)) h0 h1)
  (fun i ->
    let current0:uint64 = current.(size 0) in
    recall keccak_rotc;
    recall keccak_piln;
    let r = keccak_rotc.(i) in
    let _Y = keccak_piln.(i) in
    assume (v _Y < 25);
    let temp = s.(_Y) in
    assume (0 < uint_v r /\ uint_v r < 64);
    s.(_Y) <- rotl current0 r;
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
  -> round:size_t{v round < 24}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let state_iota s round =
  recall keccak_rndc;
  writeLane s (size 0) (size 0) (readLane s (size 0) (size 0) ^. keccak_rndc.(round))

val state_permute1:
     s:state
  -> round:size_t{v round < 24}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let state_permute1 s round =
  state_theta s;
  state_pi_rho s;
  state_chi s;
  state_iota s round

val state_permute:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
let state_permute s =
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 24)
  (fun h1 i ->
    live h1 s /\ modifies (loc_buffer s) h0 h1)
  (fun i ->
    state_permute1 s i
  )

val loadState:
     rateInBytes:size_t{v rateInBytes <= 200}
  -> input:lbytes (v rateInBytes)
  -> s:state
  -> Stack unit
    (requires fun h -> live h input /\ live h s /\ disjoint input s)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s) h0 h1)
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
