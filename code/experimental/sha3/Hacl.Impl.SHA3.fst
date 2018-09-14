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

open Spec.SHA3.Constants

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module S = Spec.SHA3
module LSeq = Lib.Sequence

let keccak_rotc = IB.igcmalloc_of_list HyperStack.root rotc_list

let keccak_piln = IB.igcmalloc_of_list HyperStack.root piln_list

let keccak_rndc = IB.igcmalloc_of_list HyperStack.root rndc_list

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
    (ensures  fun h0 r h1 ->
      modifies loc_none h0 h1 /\
      r == S.readLane (as_seq h0 s) (v x) (v y))
let readLane s x y = s.(x +! size 5 *! y)

inline_for_extraction noextract
val writeLane:
     s:state
  -> x:index
  -> y:index
  -> v:uint64
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.writeLane (as_seq h0 s) (size_v x) (size_v y) v)
let writeLane s x y v = s.(x +! size 5 *! y) <- v

[@"c_inline"]
let rotl (a:uint64) (b:uint32{0 < uint_v b /\ uint_v b < 64}) =
  (a <<. b) |. (a >>. (u32 64 -. b))

let as_state (h:mem) (s:state) : S.state = as_seq_sp h s

let as_seq5 (h:mem) (s:lbuffer uint64 5) : LSeq.lseq uint64 5 = as_seq_sp h s

inline_for_extraction noextract
val state_theta_inner_C:
    #h0:mem
  -> s:state
  -> i:index
  -> _C:lbuffer uint64 5
  -> Stack unit
    (requires fun h ->
      live h s /\ live h _C /\ disjoint _C s /\
      as_state h0 s == as_state h s /\
      loop_inv h0 h 5 5 _C (S.state_theta_inner_C (as_state h0 s)) (v i))
    (ensures  fun _ _ h -> live h s /\
      loop_inv h0 h 5 5 _C (S.state_theta_inner_C (as_state h0 s)) (v i + 1))
let state_theta_inner_C #h0 s x _C =
  let h1 = ST.get () in
  _C.(x) <-
    readLane s x (size 0) ^.
    readLane s x (size 1) ^.
    readLane s x (size 2) ^.
    readLane s x (size 3) ^.
    readLane s x (size 4);
  let h2 = ST.get () in
  assert (as_seq h2 _C == S.state_theta_inner_C (as_state h0 s) (v x) (as_seq5 h1 _C));
  lemma_repeati_sp #h0 5 (S.state_theta_inner_C (as_state h0 s)) (as_seq5 h0 _C) (v x) (as_seq5 h1 _C)

inline_for_extraction noextract
val state_theta0:
     #h0:mem
  -> s:state
  -> _C:lbuffer uint64 5
  -> Stack unit
    (requires fun h ->
      h0 == h /\ live h s /\ live h _C /\
      disjoint _C s /\
      as_state h0 s == as_state h s)
    (ensures  fun _ _ h1 ->
      modifies (loc_buffer _C) h0 h1 /\
      as_seq_sp h1 _C == S.state_theta0 (as_seq_sp h0 s) (as_seq_sp h0 _C))
let state_theta0 #h0 s _C =
  let inv h h1 = live h1 s /\ live h1 _C /\ disjoint s _C /\ as_state h0 s == as_state h1 s in
  loop #h0 (size 5) _C inv (S.state_theta_inner_C (as_state h0 s))
  (fun x ->
    state_theta_inner_C #h0 s x _C
  )

val state_theta_inner_s_inner:
     #h0:mem
  -> s0:state
  -> x:index
  -> _D:uint64
  -> y:index
  -> s:state
  -> Stack unit
    (requires fun h -> live h s0 /\ live h s /\ disjoint s0 s /\
      as_seq h0 s0 == as_seq h s0 /\
      loop_inv h0 h 25 5 s (S.state_theta_inner_s_inner (as_seq h0 s0) (v x) _D) (v y))
    (requires fun _ _ h -> as_seq h0 s0 == as_seq h s0 /\
      loop_inv h0 h 25 5 s (S.state_theta_inner_s_inner (as_seq h0 s0) (v x) _D) (v y + 1))
let state_theta_inner_s_inner #h0 s0 x _D y s =
  let h1 = ST.get () in
  writeLane s x y (readLane s0 x y ^. _D);
  let h2 = ST.get () in
  assert (as_seq h2 s == S.writeLane (as_seq h1 s) (v x) (v y) (S.readLane (as_seq h0 s0) (v x) (v y) ^. _D));
  lemma_repeati_sp #h0 5 (S.state_theta_inner_s_inner (as_seq h0 s0) (v x) _D) (as_seq h0 s) (v y) (as_seq h1 s)

val state_theta_inner_s:
     #h0:mem
  -> s0:state
  -> _C:lbuffer uint64 5
  -> x:index
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s0 /\ live h s /\ live h _C /\
      disjoint _C s /\ disjoint s0 s /\
      as_seq h0 s0 == as_seq h s0 /\
      as_seq h0 _C == as_seq h _C /\
      loop_inv h0 h 25 5 s (S.state_theta_inner_s (as_seq h0 s0) (as_seq h0 _C)) (v x))
    (ensures  fun _ _ h -> loop_inv h0 h 25 5 s (S.state_theta_inner_s (as_seq h0 s0) (as_seq h0 _C)) (v x + 1))
let state_theta_inner_s #h0 s0 _C x s =
  let _D = _C.((x +. size 4) %. size 5) ^. rotl _C.((x +. size 1) %. size 5) (u32 1) in
  let inv h0 h = live h s0 /\ live h s /\ disjoint s0 s /\ as_seq h0 s0 == as_seq h s0 in
  let h1 = ST.get () in
  loop #h1 (size 5) s inv (S.state_theta_inner_s_inner (as_seq_sp h0 s0) (v x) _D)
  (fun y ->
    state_theta_inner_s_inner #h1 s0 x _D y s
  );
  let h2 = ST.get () in
  assert (as_seq h2 s == LSeq.repeati_sp #5 5 (S.state_theta_inner_s_inner (as_seq_sp h0 s0) (v x) _D) (as_seq h1 s));
  lemma_repeati_sp #h0 5 (S.state_theta_inner_s (as_seq h0 s0) (as_seq h0 _C)) (as_seq h0 s) (v x) (as_seq h1 s)

val copy_s:
     s0:state
  -> s1:state
  -> Stack unit
    (requires fun h -> live h s0 /\ live h s1 /\ disjoint s0 s1)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer s0) h0 h1 /\
      as_seq h1 s0 == as_seq h0 s1)
let copy_s s0 s1 = admit();
  update_sub #uint64 #25 s0 (size 0) (size 25) s1

val state_theta1:
     s:state
  -> _C:lbuffer uint64 5
  -> Stack unit
    (requires fun h ->
      live h s /\ live h _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_theta1 (as_seq h0 s) (as_seq h0 _C))
let state_theta1 s _C =
  push_frame ();
  let s0 = create (size 25) (u64 0) in
  copy_s s0 s;
  let inv h0 h =
    live h s0 /\ live h s /\ live h _C /\
    disjoint _C s /\ disjoint s0 s /\
    as_seq h0 s0 == as_seq h s0 /\
    as_seq h0 _C == as_seq h _C in
  let h0 = ST.get () in
  loop #h0 (size 5) s inv (S.state_theta_inner_s (as_seq_sp h0 s0) (as_seq_sp h0 _C))
  (fun x ->
    state_theta_inner_s #h0 s0 _C x s
  );
  let h1 = ST.get () in
  assert (as_seq h1 s == LSeq.repeati_sp #5 5 (S.state_theta_inner_s (as_seq_sp h0 s0) (as_seq_sp h0 _C)) (as_seq h0 s0));
  pop_frame ()

inline_for_extraction noextract
val state_theta:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_theta (as_state h0 s))
let state_theta s =
  push_frame();
  let _C:lbuffer uint64 5 = create (size 5) (u64 0) in
  let h0 = ST.get () in
  state_theta0 #h0 s _C;
  state_theta1 s _C;
  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val state_pi_rho_inner:
     i:size_t{v i < 24}
  -> current:lbuffer uint64 1
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s /\ live h current /\ disjoint current s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer current) (loc_buffer s)) h0 h1 /\
      (let current_sp, s_sp = S.state_pi_rho_inner (v i) (as_seq h0 current, as_seq h0 s) in
      as_seq h1 current == current_sp /\ as_seq h1 s == s_sp))
let state_pi_rho_inner i current s =
  IB.recall_contents keccak_rotc (Seq.seq_of_list rotc_list);
  IB.recall_contents keccak_piln (Seq.seq_of_list piln_list);
  let r = IB.index keccak_rotc (Lib.RawIntTypes.size_to_UInt32 i) in
  assert (r == LSeq.index S.keccak_rotc (v i));
  let _Y = IB.index keccak_piln (Lib.RawIntTypes.size_to_UInt32 i) in
  assume (v _Y == LSeq.index S.keccak_piln (v i));
  let temp = s.(_Y) in
  let current0:uint64 = current.(size 0) in
  s.(_Y) <- rotl current0 r;
  current.(size 0) <- temp

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
    state_pi_rho_inner i current s
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
	((lognot (readLane temp ((x +. size 1) %. size 5) y)) &.
	  readLane temp ((x +. size 2) %. size 5) y))
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
  IB.recall_contents keccak_rndc (Seq.seq_of_list rndc_list);
  writeLane s (size 0) (size 0) (readLane s (size 0) (size 0) ^. (IB.index keccak_rndc (Lib.RawIntTypes.size_to_UInt32 round)))

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
    S.lemma_rateInBytes (v inputByteLen) (v rateInBytes) (v i);
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
    S.lemma_rateInBytes (v outputByteLen) (v rateInBytes) (v i);
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
