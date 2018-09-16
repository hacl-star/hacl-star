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
module LSeq = Lib.Sequence
module S = Spec.SHA3

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
      loop_inv h0 h 5 _C (S.state_theta_inner_C (as_state h0 s)) (v i))
    (ensures  fun _ _ h -> live h s /\
      loop_inv h0 h 5 _C (S.state_theta_inner_C (as_state h0 s)) (v i + 1))
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

inline_for_extraction noextract
val state_theta_inner_s_inner:
     #h0:mem
  -> x:index
  -> _D:uint64
  -> y:index
  -> s:state
  -> Stack unit
    (requires fun h -> live h s /\
      loop_inv h0 h 5 s (S.state_theta_inner_s_inner (v x) _D) (v y))
    (requires fun _ _ h ->
      loop_inv h0 h 5 s (S.state_theta_inner_s_inner (v x) _D) (v y + 1))
let state_theta_inner_s_inner #h0 x _D y s =
  let h1 = ST.get () in
  writeLane s x y (readLane s x y ^. _D);
  let h2 = ST.get () in
  lemma_repeati_sp #h0 5 (S.state_theta_inner_s_inner (v x) _D) (as_seq h0 s) (v y) (as_seq h1 s)

inline_for_extraction noextract
val state_theta_inner_s:
     #h0:mem
  -> _C:lbuffer uint64 5
  -> x:index
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s /\ live h _C /\ disjoint _C s /\
      as_seq h0 _C == as_seq h _C /\
      loop_inv h0 h 5 s (S.state_theta_inner_s (as_seq h0 _C)) (v x))
    (ensures  fun _ _ h -> loop_inv h0 h 5 s (S.state_theta_inner_s (as_seq h0 _C)) (v x + 1))
let state_theta_inner_s #h0 _C x s =
  let _D = _C.((x +. size 4) %. size 5) ^. rotl _C.((x +. size 1) %. size 5) (u32 1) in
  let inv h0 h = live h s in
  let h1 = ST.get () in
  loop #h1 (size 5) s inv (S.state_theta_inner_s_inner (v x) _D)
  (fun y ->
    state_theta_inner_s_inner #h1 x _D y s
  );
  let h2 = ST.get () in
  assert (as_seq h2 s == LSeq.repeati_sp #5 5 (S.state_theta_inner_s_inner (v x) _D) (as_seq h1 s));
  lemma_repeati_sp #h0 5 (S.state_theta_inner_s (as_seq h0 _C)) (as_seq h0 s) (v x) (as_seq h1 s)

inline_for_extraction noextract
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
  let inv h0 h =
    live h s /\ live h _C /\ disjoint _C s /\
    as_seq h0 _C == as_seq h _C in
  let h0 = ST.get () in
  loop #h0 (size 5) s inv (S.state_theta_inner_s (as_seq_sp h0 _C))
  (fun x ->
    state_theta_inner_s #h0 _C x s
  );
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

inline_for_extraction noextract
val state_pi_rho_inner:
    #h0:mem
  -> i:size_t{v i < 24}
  -> current:lbuffer uint64 1
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s /\ live h current /\ disjoint current s /\
      loop2_inv h0 h 24 current s S.state_pi_rho_inner (v i))
    (ensures  fun h _ h1 ->
      loop2_inv h0 h1 24 current s S.state_pi_rho_inner (v i + 1) /\
      modifies (loc_union (loc_buffer current) (loc_buffer s)) h0 h1 /\
      (let current_sp, s_sp = S.state_pi_rho_inner (v i) (as_seq h current, as_seq h s) in
      as_seq h1 current == current_sp /\ as_seq h1 s == s_sp))
let state_pi_rho_inner #h0 i current s =
  let h = ST.get () in
  IB.recall_contents keccak_rotc (Seq.seq_of_list rotc_list);
  IB.recall_contents keccak_piln (Seq.seq_of_list piln_list);
  let r = IB.index keccak_rotc (Lib.RawIntTypes.size_to_UInt32 i) in
  assert (r == LSeq.index S.keccak_rotc (v i));
  let _Y = IB.index keccak_piln (Lib.RawIntTypes.size_to_UInt32 i) in
  assume (v _Y == LSeq.index S.keccak_piln (v i));
  let temp = s.(_Y) in
  let current0:uint64 = current.(size 0) in
  s.(_Y) <- rotl current0 r;
  current.(size 0) <- temp;
  let h1 = ST.get () in
  lemma_repeati_sp #h0 24 S.state_pi_rho_inner (as_seq h0 current, as_seq h0 s) (v i) (as_seq h current, as_seq h s)

inline_for_extraction noextract
val state_pi_rho:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_pi_rho (as_seq h0 s))
let state_pi_rho s =
  push_frame();
  let current:lbuffer uint64 1 = create (size 1) (readLane s (size 1) (size 0)) in
  let h0 = ST.get () in
  let inv h0 h1 = live h1 s /\ live h1 current /\ disjoint current s in
  loop2 #h0 (size 24) current s inv S.state_pi_rho_inner
  (fun i ->
    state_pi_rho_inner #h0 i current s
  );
  pop_frame()

inline_for_extraction noextract
val state_chi_inner:
     #h0:mem
  -> s_pi_rho:state
  -> y:index
  -> x:index
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s_pi_rho /\ live h s /\ disjoint s_pi_rho s /\
      as_seq h0 s_pi_rho == as_seq h s_pi_rho /\
      loop_inv h0 h 5 s (S.state_chi_inner (as_seq_sp h0 s_pi_rho) (v y)) (v x))
    (ensures  fun h _ h1 ->
      modifies (loc_buffer s) h h1 /\
      as_seq h1 s == S.state_chi_inner (as_seq h s_pi_rho) (v y) (v x) (as_seq h s) /\
      loop_inv h0 h1 5 s (S.state_chi_inner (as_seq_sp h0 s_pi_rho) (v y)) (v x + 1))
let state_chi_inner #h0 s_pi_rho y x s =
  let h1 = ST.get () in
  writeLane s x y
    (readLane s_pi_rho x y ^.
     ((lognot (readLane s_pi_rho ((x +. size 1) %. size 5) y)) &.
     readLane s_pi_rho ((x +. size 2) %. size 5) y));
  let h2 = ST.get () in
  lemma_repeati_sp #h0 5 (S.state_chi_inner (as_seq_sp h0 s_pi_rho) (v y)) (as_seq h0 s) (v x) (as_seq h1 s)

inline_for_extraction noextract
val state_chi_inner1:
    #h0:mem
  -> s_pi_rho:state
  -> y:index
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s_pi_rho /\ live h s /\ disjoint s_pi_rho s /\
      as_seq h0 s_pi_rho == as_seq h s_pi_rho /\
      loop_inv h0 h 5 s (S.state_chi_inner1 (as_seq_sp h0 s_pi_rho)) (v y))
    (ensures  fun h _ h1 ->
      modifies (loc_buffer s) h h1 /\
      as_seq h1 s == S.state_chi_inner1 (as_seq h s_pi_rho) (v y) (as_seq h s) /\
      loop_inv h0 h1 5 s (S.state_chi_inner1 (as_seq_sp h0 s_pi_rho)) (v y + 1))
let state_chi_inner1 #h0 s_pi_rho y s =
  let h1 = ST.get () in
  let inv h0 h1 = live h1 s_pi_rho /\ live h1 s /\ disjoint s_pi_rho s in
  loop #h1 (size 5) s inv (S.state_chi_inner (as_seq_sp h0 s_pi_rho) (v y))
  (fun x ->
    state_chi_inner #h1 s_pi_rho y x s
  );
  let h2 = ST.get () in
  lemma_repeati_sp #h0 5 (S.state_chi_inner1 (as_seq_sp h0 s_pi_rho)) (as_seq h0 s) (v y) (as_seq h1 s)

inline_for_extraction noextract
val copy_s:
     s0:state
  -> s1:state
  -> Stack unit
    (requires fun h -> live h s0 /\ live h s1 /\ disjoint s0 s1)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s0) h0 h1 /\
      as_seq h1 s0 == as_seq h0 s1)
let copy_s s0 s1 =
  let h0 = ST.get () in
  update_sub #uint64 #25 s0 (size 0) (size 25) s1;
  let h1 = ST.get () in
  LSeq.eq_intro (LSeq.sub #_ #25 (as_seq h1 s0) 0 25) (LSeq.sub #_ #25 (as_seq h0 s1) 0 25)

inline_for_extraction noextract
val state_chi:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_chi (as_seq h0 s))
let state_chi s =
  push_frame ();
  let s_pi_rho:state = create (size 25) (u64 0) in
  copy_s s_pi_rho s;
  let h0 = ST.get () in
  let inv h0 h1 = live h1 s_pi_rho /\ live h1 s /\ disjoint s_pi_rho s in
  loop #h0 (size 5) s inv (S.state_chi_inner1 (as_seq_sp h0 s_pi_rho))
  (fun y ->
    state_chi_inner1 #h0 s_pi_rho y s
  );
  pop_frame ()

inline_for_extraction noextract
val state_iota:
     s:state
  -> round:size_t{v round < 24}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_iota (as_seq h0 s) (v round))
let state_iota s round =
  IB.recall_contents keccak_rndc (Seq.seq_of_list rndc_list);
  writeLane s (size 0) (size 0) (readLane s (size 0) (size 0) ^. (IB.index keccak_rndc (Lib.RawIntTypes.size_to_UInt32 round)))

val state_permute1:
     #h0:mem
  -> round:size_t{v round < 24}
  -> s:state
  -> Stack unit
    (requires fun h1 -> live h1 s /\
      loop_inv h0 h1 24 s S.state_permute1 (v round))
    (ensures  fun h _ h1 ->
      modifies (loc_buffer s) h h1 /\
      as_seq h1 s == S.state_permute1 (v round) (as_seq h s) /\
      loop_inv h0 h1 24 s S.state_permute1 (v round + 1))
let state_permute1 #h0 round s =
  let h1 = ST.get () in
  state_theta s;
  state_pi_rho s;
  state_chi s;
  state_iota s round;
  let h2 = ST.get () in
  lemma_repeati_sp #h0 24 S.state_permute1 (as_seq h0 s) (v round) (as_seq h1 s)

val state_permute:
     s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_permute (as_seq h0 s))
let state_permute s =
  let h0 = ST.get () in
  let inv h0 h1 = live h1 s in
  loop #h0 (size 24) s inv S.state_permute1
  (fun i ->
    state_permute1 #h0 i s
  )

val loadState_inner:
     #h0:mem
  -> block:lbytes 200
  -> j:size_t{v j < 25}
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h block /\ live h s /\ disjoint block s /\
      as_seq h0 block == as_seq h block /\
      loop_inv h0 h 25 s (S.loadState_inner (as_seq_sp h0 block)) (v j))
    (ensures  fun h _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.loadState_inner (as_seq h block) (v j) (as_seq h s) /\
      loop_inv h0 h1 25 s (S.loadState_inner (as_seq_sp h0 block)) (v j + 1))
let loadState_inner #h0 block j s =
  let h1 = ST.get () in
  s.(j) <- s.(j) ^. uint_from_bytes_le #U64 (sub #_ #200 #8 block (j *! size 8) (size 8));
  let h2 = ST.get () in
  lemma_repeati_sp #h0 25 (S.loadState_inner (as_seq_sp h0 block)) (as_seq h0 s) (v j) (as_seq h1 s)

val loadState:
     rateInBytes:size_t{v rateInBytes <= 200}
  -> input:lbytes (v rateInBytes)
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h input /\ live h s /\ disjoint input s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.loadState (v rateInBytes) (as_seq h0 input) (as_seq h0 s))
let loadState rateInBytes input s =
  push_frame();
  let block:lbytes 200 = create (size 200) (u8 0) in
  update_sub block (size 0) rateInBytes input;
  let h0 = ST.get () in
  let inv h0 h1 =
    live h1 block /\ live h1 s /\ disjoint block s /\
    as_seq h0 block == as_seq h1 block in
  loop #h0 (size 25) s inv (S.loadState_inner (as_seq_sp h0 block))
  (fun i ->
    loadState_inner #h0 block i s
  );
  pop_frame ()

val storeState_inner:
     #h0:mem
  -> s:state
  -> j:size_t{v j < 25}
  -> block:lbytes 200
  -> Stack unit
    (requires fun h ->
      live h s /\ live h block /\ disjoint s block /\
      as_seq h0 s == as_seq h s /\
      loop_inv h0 h 25 block (S.storeState_inner (as_seq h0 s)) (v j))
    (ensures  fun h _ h1 ->
      modifies (loc_buffer block) h h1 /\
      as_seq h1 block == S.storeState_inner (as_seq h s) (v j) (as_seq h block) /\
      loop_inv h0 h1 25 block (S.storeState_inner (as_seq h0 s)) (v j + 1))
let storeState_inner #h0 s j block =
  let h1 = ST.get () in
  let tmp = sub block (j *! size 8) (size 8) in
  uint_to_bytes_le tmp s.(j);
  let h2 = ST.get () in
  assert (v j * 8 < 200);
  modifies_buffer_elim (sub #uint8 #200 #(v j * 8) block (size 0) (j *! size 8)) (loc_buffer tmp) h1 h2;
  modifies_buffer_elim (sub #uint8 #200 #(200 - v j * 8 - 8) block (j *! size 8 +! size 8) (size 200 -! j *! size 8 -! size 8)) (loc_buffer tmp) h1 h2;
  S.lemma_update_store (as_seq h1 s) (v j) (as_seq h1 block) (as_seq h2 block);
  assert (as_seq h2 block == S.storeState_inner (as_seq h1 s) (v j) (as_seq h1 block));
  lemma_repeati_sp #h0 25 (S.storeState_inner (as_seq h0 s)) (as_seq h0 block) (v j) (as_seq h1 block)

val storeState:
     rateInBytes:size_t{v rateInBytes <= 200}
  -> s:state
  -> res:lbytes (v rateInBytes)
  -> Stack unit
    (requires fun h -> live h s /\ live h res /\ disjoint s res)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.storeState (v rateInBytes) (as_seq h0 s))
let storeState rateInBytes s res =
  push_frame();
  let block:lbytes 200 = create (size 200) (u8 0) in
  let h0 = ST.get () in
  let inv h0 h = live h s /\ live h block /\ disjoint s block in
  loop #h0 (size 25) block inv (S.storeState_inner (as_seq_sp h0 s))
  (fun j ->
    storeState_inner #h0 s j block
  );
  update_sub res (size 0) rateInBytes (sub block (size 0) rateInBytes);
  pop_frame()

#reset-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 150"

inline_for_extraction noextract
val absorb_last:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:uint8
  -> Stack unit
    (requires fun h -> live h s /\ live h input /\ disjoint s input)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s ==
      S.absorb_last (as_seq h0 s) (v rateInBytes) (v inputByteLen) (as_seq h0 input) delimitedSuffix)
let absorb_last s rateInBytes inputByteLen input delimitedSuffix =
  push_frame ();
  let lastBlock = create rateInBytes (u8 0) in
  let rem = inputByteLen %. rateInBytes in
  assert (v rem == v inputByteLen % v rateInBytes);
  let last = sub input (inputByteLen -. rem) rem in
  let h0 = ST.get () in
  update_sub #uint8 #(v rateInBytes) lastBlock (size 0) rem last;
  let h1 = ST.get () in
  assert (as_seq h1 lastBlock == LSeq.update_sub #uint8 #(v rateInBytes) (as_seq h0 lastBlock) 0 (v rem) (as_seq h0 last));
  lastBlock.(rem) <- delimitedSuffix;
  let h2 = ST.get () in
  assert (as_seq h2 lastBlock == LSeq.upd #uint8 #(v rateInBytes) (as_seq h1 lastBlock) (v rem) delimitedSuffix);
  loadState rateInBytes lastBlock s;
  let h3 = ST.get () in
  assert (as_seq h3 s == S.loadState (v rateInBytes) (as_seq h2 lastBlock) (as_seq h2 s));
  pop_frame ()

#set-options "--z3rlimit 50 --max_fuel 0"

inline_for_extraction noextract
val absorb_next:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.absorb_next (as_seq h0 s) (v rateInBytes))
let absorb_next s rateInBytes =
  push_frame ();
  let nextBlock = create rateInBytes (u8 0) in
  nextBlock.(rateInBytes -! size 1) <- u8 0x80;
  loadState rateInBytes nextBlock s;
  state_permute s;
  pop_frame ()

inline_for_extraction noextract
val absorb_inner:
     #h0:mem
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> i:size_t{v i < v inputByteLen / v rateInBytes}
  -> s:state
  -> Stack unit
    (requires fun h ->
      live h s /\ live h input /\ disjoint s input /\
      as_seq h0 input == as_seq h input /\
      loop_inv h0 h (v inputByteLen / v rateInBytes) s
	(S.absorb_inner (v rateInBytes) (v inputByteLen) (as_seq h0 input)) (v i))
    (ensures  fun h _ h1 ->
      modifies (loc_buffer s) h h1 /\
      as_seq h1 s ==
      S.absorb_inner (v rateInBytes) (v inputByteLen) (as_seq h input) (v i) (as_seq h s) /\
      loop_inv h0 h1 (v inputByteLen / v rateInBytes) s
	(S.absorb_inner (v rateInBytes) (v inputByteLen) (as_seq h0 input)) (v i + 1))
let absorb_inner #h0 rateInBytes inputByteLen input i s =
  let h1 = ST.get () in
  S.lemma_rateInBytes (v inputByteLen) (v rateInBytes) (v i);
  loadState rateInBytes (sub #_ #(v inputByteLen) #(v rateInBytes) input (i *! rateInBytes) rateInBytes) s;
  state_permute s;
  let h2 = ST.get () in
  lemma_repeati_sp #h0 (v inputByteLen / v rateInBytes)
    (S.absorb_inner (v rateInBytes) (v inputByteLen) (as_seq h0 input)) (as_seq h0 s) (v i) (as_seq h1 s)

val absorb:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:uint8
  -> Stack unit
    (requires fun h -> live h s /\ live h input /\ disjoint s input)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s ==
      S.absorb (as_seq h0 s) (v rateInBytes) (v inputByteLen) (as_seq h0 input) delimitedSuffix)
let absorb s rateInBytes inputByteLen input delimitedSuffix =
  let open Lib.RawIntTypes in
  let n = inputByteLen /. rateInBytes in
  let rem = inputByteLen %. rateInBytes in
  let h0 = ST.get () in
  let inv h0 h =
    live h s /\ live h input /\ disjoint s input /\
    as_seq h0 input == as_seq h input in
  loop #h0 n s inv (S.absorb_inner (v rateInBytes) (v inputByteLen) (as_seq_sp h0 input))
  (fun i ->
    absorb_inner #h0 rateInBytes inputByteLen input i s
  );
  absorb_last s rateInBytes inputByteLen input delimitedSuffix;
  (if (not (u8_to_UInt8 (delimitedSuffix &. u8 0x80) = 0uy) && (size_to_UInt32 rem = size_to_UInt32 (rateInBytes -. size 1)))
  then state_permute s);
  absorb_next s rateInBytes

inline_for_extraction noextract
val squeeze_inner:
     #h0:mem
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> s:state
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h ->
      live h s /\ live h output /\ disjoint s output /\
      loop2_inv h0 h (v outputByteLen / v rateInBytes) s output (S.squeeze_inner (v rateInBytes) (v outputByteLen)) (v i))
    (ensures  fun h _ h1 ->
      modifies (loc_union (loc_buffer s) (loc_buffer output)) h0 h1 /\
      (let s_sp, o_sp = S.squeeze_inner (v rateInBytes) (v outputByteLen) (v i) (as_seq h s, as_seq h output) in
      as_seq h1 s == s_sp /\ as_seq h1 output == o_sp) /\
      loop2_inv h0 h1 (v outputByteLen / v rateInBytes) s output (S.squeeze_inner (v rateInBytes) (v outputByteLen)) (v i + 1))
let squeeze_inner #h0 rateInBytes outputByteLen i s output =
  S.lemma_rateInBytes (v outputByteLen) (v rateInBytes) (v i);
  let h1 = ST.get () in
  let tmp = sub output (i *! rateInBytes) rateInBytes in
  storeState rateInBytes s tmp;
  let h2 = ST.get () in
  modifies_buffer_elim (sub #uint8 #(v outputByteLen) #(v i * v rateInBytes) output (size 0) (i *! rateInBytes)) (loc_buffer tmp) h1 h2;
  modifies_buffer_elim (sub #uint8 #(v outputByteLen) #(v outputByteLen - v i * v rateInBytes - v rateInBytes)
    output (i *! rateInBytes +! rateInBytes) (outputByteLen -! i *! rateInBytes -! rateInBytes)) (loc_buffer tmp) h1 h2;
  S.lemma_update_squeeze (v rateInBytes) (v outputByteLen) (v i) (as_seq h1 s) (as_seq h1 output) (as_seq h2 output);
  state_permute s;
  lemma_repeati_sp #h0 (v outputByteLen / v rateInBytes) (S.squeeze_inner (v rateInBytes) (v outputByteLen))
    (as_seq h0 s, as_seq h0 output) (v i) (as_seq h1 s, as_seq h1 output)

inline_for_extraction noextract
val squeeze_rem:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h -> live h s /\ live h output /\ disjoint s output)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output == S.squeeze_rem (as_seq h0 s) (v rateInBytes) (v outputByteLen) (as_seq h0 output))
let squeeze_rem s rateInBytes outputByteLen output =
  let remOut = outputByteLen %. rateInBytes in
  let h1 = ST.get () in
  let tmp = sub output (outputByteLen -. remOut) remOut in
  storeState remOut s tmp;
  let h2 = ST.get () in
  modifies_buffer_elim (sub #uint8 #(v outputByteLen) #(v outputByteLen - v remOut) output (size 0) (outputByteLen -! remOut)) (loc_buffer tmp) h1 h2;
  S.lemma_update_squeeze_rem (as_seq h1 s) (v rateInBytes) (v outputByteLen) (as_seq h1 output) (as_seq h2 output)

val squeeze:
     s:state
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h -> live h s /\ live h output /\ disjoint s output)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer s) (loc_buffer output)) h0 h1 /\
      as_seq h1 output == S.squeeze (as_seq h0 s) (v rateInBytes) (v outputByteLen) (as_seq h0 output))
let squeeze s rateInBytes outputByteLen output =
  let outBlocks = outputByteLen /. rateInBytes in
  let h0 = ST.get () in
  let inv h0 h = live h s /\ live h output /\ disjoint s output in
  loop2 #h0 outBlocks s output inv (S.squeeze_inner (v rateInBytes) (v outputByteLen))
  (fun i ->
    squeeze_inner #h0 rateInBytes outputByteLen i s output
  );
  squeeze_rem s rateInBytes outputByteLen output

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

val keccak:
     rate:size_t{v rate % 8 == 0 /\ v rate / 8 > 0 /\ v rate <= 1600}
  -> capacity:size_t{v capacity + v rate == 1600}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:uint8
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output ==
      S.keccak (v rate) (v capacity) (v inputByteLen) (as_seq h0 input) delimitedSuffix (v outputByteLen) (as_seq h0 output))
let keccak rate capacity inputByteLen input delimitedSuffix outputByteLen output =
  push_frame();
  let rateInBytes = rate /. size 8 in
  let s:state = create (size 25) (u64 0) in
  absorb s rateInBytes inputByteLen input delimitedSuffix;
  squeeze s rateInBytes outputByteLen output;
  pop_frame()
