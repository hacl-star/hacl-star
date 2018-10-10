module Hacl.Impl.SHA3

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.Buffer
open Lib.Endianness

open Spec.SHA3.Constants

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module LSeq = Lib.Sequence
module LB = Lib.ByteSequence
module Loop = Lib.LoopCombinators
module S = Spec.SHA3

let keccak_rotc = icreateL_global rotc_list

let keccak_piln = icreateL_global piln_list

let keccak_rndc = icreateL_global rndc_list

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

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
let rotl (a:uint64) (b:size_t{0 < uint_v b /\ uint_v b < 64}) =
  rotate_left a b

inline_for_extraction noextract
val state_theta0:
    s:state
  -> _C:lbuffer uint64 5
  -> Stack unit
    (requires fun h -> live h s /\ live h _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer _C) h0 h1 /\
      as_seq h1 _C == S.state_theta0 (as_seq h0 s) (as_seq h0 _C))
let state_theta0 s _C =
  [@ inline_let]
  let spec h0 = S.state_theta_inner_C (as_seq h0 s) in
  let h0 = ST.get () in
  loop1 h0 (size 5) _C spec
  (fun x ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 _C) (v x);
    _C.(x) <-
      readLane s x (size 0) ^.
      readLane s x (size 1) ^.
      readLane s x (size 2) ^.
      readLane s x (size 3) ^.
      readLane s x (size 4)
  )

inline_for_extraction noextract
val state_theta_inner_s:
    _C:lbuffer uint64 5
  -> x:index
  -> s:state
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_theta_inner_s (as_seq h0 _C) (v x) (as_seq h0 s))
let state_theta_inner_s _C x s =
  let _D = _C.((x +. size 4) %. size 5) ^. rotl _C.((x +. size 1) %. size 5) (size 1) in
  [@ inline_let]
  let spec h0 = S.state_theta_inner_s_inner (v x) _D in
  let h0 = ST.get () in
  loop1 h0 (size 5) s spec
  (fun y ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 s) (v y);
    writeLane s x y (readLane s x y ^. _D)
  )

inline_for_extraction noextract
val state_theta1:
     s:state
  -> _C:lbuffer uint64 5
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_theta1 (as_seq h0 s) (as_seq h0 _C))
let state_theta1 s _C =
  [@ inline_let]
  let spec h0 = S.state_theta_inner_s (as_seq h0 _C) in
  let h0 = ST.get () in
  loop1 h0 (size 5) s spec
  (fun x ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 s) (v x);
    state_theta_inner_s _C x s
  )

inline_for_extraction noextract
val state_theta:
    s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_theta (as_seq h0 s))
let state_theta s =
  push_frame();
  let _C = create (size 5) (u64 0) in
  state_theta0 s _C;
  state_theta1 s _C;
  pop_frame()

#reset-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 50"

private
val index_map: #a:Type -> #b:Type -> f:(a -> b) -> l:list a -> i:nat{i < List.Tot.length l} ->
  Lemma (List.Tot.index (List.Tot.map f l) i == f (List.Tot.index l i))
let rec index_map #a #b f l i =
  if i = 0 then ()
  else
    match l with
    | [] -> ()
    | _ :: l' -> index_map f l' (i - 1)

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

inline_for_extraction noextract
val state_pi_rho_inner:
    i:size_t{v i < 24}
  -> current:lbuffer uint64 1
  -> s:state
  -> Stack unit
    (requires fun h -> live h s /\ live h current /\ disjoint current s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer s) (loc_buffer current)) h0 h1 /\
      (let c', s' = S.state_pi_rho_inner (v i) (bget h0 current 0, as_seq h0 s) in
      bget h1 current 0 == c' /\
      as_seq h1 s == s'))
let state_pi_rho_inner i current s =
  assert_norm (List.Tot.length piln_list <= max_size_t);
  recall_contents keccak_rotc S.keccak_rotc;
  recall_contents keccak_piln (LSeq.of_list piln_list);
  index_map S.sizes_v piln_list (v i);
  let _Y = iindex keccak_piln i in
  let r = iindex keccak_rotc i in
  let temp = s.(_Y) in  
  s.(_Y) <- rotl current.(size 0) r;
  current.(size 0) <- temp

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
  let h0 = ST.get () in
  let current:lbuffer uint64 1 = create (size 1) (readLane s (size 1) (size 0)) in
  let h1 = ST.get () in
  assert (bget h1 current 0 == S.readLane (as_seq h0 s) 1 0);
  let a_impl = (lbuffer uint64 1) & state in
  let refl h i : GTot (uint64 & S.state) = get h current 0, as_seq h s in
  let footprint i = loc_union (loc_buffer current) (loc_buffer s) in
  let spec h0 = S.state_pi_rho_inner in
  let h0 = ST.get () in
  loop h0 (size 24) S.state_pi_rho_s a_impl (current, s) refl footprint spec
  (fun i ->
    Loop.unfold_repeat_gen 24 S.state_pi_rho_s (spec h0) (refl h0 0) (v i);
    state_pi_rho_inner i current s
  );
  pop_frame()

inline_for_extraction noextract
val state_chi_inner:
    s_pi_rho:state
  -> y:index
  -> x:index
  -> s:state
  -> Stack unit
    (requires fun h0 -> live h0 s_pi_rho /\ live h0 s /\ disjoint s_pi_rho s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_chi_inner (as_seq h0 s_pi_rho) (v y) (v x) (as_seq h0 s))
let state_chi_inner s_pi_rho y x s =
  writeLane s x y
    (readLane s_pi_rho x y ^.
     ((lognot (readLane s_pi_rho ((x +. size 1) %. size 5) y)) &.
     readLane s_pi_rho ((x +. size 2) %. size 5) y))

inline_for_extraction noextract
val state_chi_inner1:
    s_pi_rho:state
  -> y:index
  -> s:state
  -> Stack unit
    (requires fun h0 -> live h0 s_pi_rho /\ live h0 s /\ disjoint s_pi_rho s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_chi_inner1 (as_seq h0 s_pi_rho) (v y) (as_seq h0 s))
let state_chi_inner1 s_pi_rho y s =
  [@ inline_let]
  let spec h0 = S.state_chi_inner (as_seq h0 s_pi_rho) (v y) in
  let h0 = ST.get () in
  loop1 h0 (size 5) s spec
  (fun x ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 s) (v x);
    state_chi_inner s_pi_rho y x s
  )

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
  let s_pi_rho: state = create (size 25) (u64 0) in
  copy s_pi_rho (size 25) s;
  [@ inline_let]
  let spec h0 = S.state_chi_inner1 (as_seq h0 s_pi_rho) in
  let h0 = ST.get () in
  loop1 h0 (size 5) s spec
  (fun y ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 s) (v y);
    state_chi_inner1 s_pi_rho y s
  );
  pop_frame()

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
  recall_contents keccak_rndc S.keccak_rndc;
  writeLane s (size 0) (size 0) (readLane s (size 0) (size 0) ^.
    (iindex keccak_rndc round))

val state_permute:
    s:state
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.state_permute (as_seq h0 s))
let state_permute s =
  [@ inline_let]
  let spec h0 = S.state_permute1 in
  let h0 = ST.get () in
  loop1 h0 (size 24) s spec
  (fun round ->
    Loop.unfold_repeati 24 (spec h0) (as_seq h0 s) (v round);
    state_theta s;
    state_pi_rho s;
    state_chi s;
    state_iota s round
  )

val loadState:
    rateInBytes:size_t{v rateInBytes <= 200}
  -> input:lbytes (v rateInBytes)
  -> s:state
  -> Stack unit
    (requires fun h -> live h input /\ live h s /\ disjoint input s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.loadState (v rateInBytes) (as_seq h0 input) (as_seq h0 s))
let loadState rateInBytes input s =
  push_frame();
  let block:lbytes 200 = create (size 200) (u8 0) in
  update_sub block (size 0) rateInBytes input;
  [@ inline_let]
  let spec h0 = S.loadState_inner (as_seq h0 block) in
  let h0 = ST.get () in
  loop1 h0 (size 25) s spec
  (fun j ->
    Loop.unfold_repeati 25 (spec h0) (as_seq h0 s) (v j);
    s.(j) <- s.(j) ^. uint_from_bytes_le #U64 (sub #_ #200 #8 block (j *! size 8) (size 8))
  );
  pop_frame ()

inline_for_extraction noextract
val storeState_inner:
    s:state
  -> j:size_t{v j < 25}
  -> block:lbytes 200
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 block /\ disjoint s block)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer block) h0 h1 /\
      as_seq h1 block == S.storeState_inner (as_seq h0 s) (v j) (as_seq h0 block))
let storeState_inner s j block =
  let sj = s.(j) in
  [@ inline_let]
  let spec h0 = Lib.ByteSequence.uint_to_bytes_le sj in
  let impl (b:lbuffer uint8 (v (size 8))) : Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer b) h0 h1 /\
      as_seq h1 b == spec h0)
    = uint_to_bytes_le #U64 b sj in
  update_sub_f block (j *! size 8) (size 8) spec impl

val storeState:
    rateInBytes:size_t{v rateInBytes <= 200}
  -> s:state
  -> res:lbytes (v rateInBytes)
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 res /\ disjoint s res)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.storeState (v rateInBytes) (as_seq h0 s))
let storeState rateInBytes s res =
  let h = ST.get() in
  push_frame();
  let block:lbytes 200 = create (size 200) (u8 0) in
  [@ inline_let]
  let spec h0 = S.storeState_inner (as_seq h0 s) in
  let h0 = ST.get () in
  loop1 h0 (size 25) block spec
  (fun j ->
    Loop.unfold_repeati 25 (spec h0) (as_seq h0 block) (v j);
    storeState_inner s j block
  );
  copy res rateInBytes (sub block (size 0) rateInBytes);
  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

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
val absorb_last:
    delimitedSuffix:byte_t
  -> rateInBytes:size_t{0 < v rateInBytes /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}  
  -> input:lbytes (v rem)
  -> s:state
  -> Stack unit
    (requires fun h -> live h s /\ live h input /\ disjoint s input)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s ==
      S.absorb_last delimitedSuffix (v rateInBytes) (v rem) 
        (as_seq h0 input) (as_seq h0 s))
let absorb_last delimitedSuffix rateInBytes rem input s =
  let open Lib.RawIntTypes in
  push_frame ();
  let lastBlock = create rateInBytes (u8 0) in
  let h0 = ST.get () in
  update_sub #uint8 #(v rateInBytes) lastBlock (size 0) rem input;
  lastBlock.(rem) <- byte_to_uint8 delimitedSuffix;
  loadState rateInBytes lastBlock s;
  if not ((delimitedSuffix &. byte 0x80) =. byte 0) && 
     (size_to_UInt32 rem = size_to_UInt32 (rateInBytes -. size 1))
  then state_permute s;
  absorb_next s rateInBytes;
  pop_frame()

private
val lemma_rateInBytes:
    inputByteLen:size_nat
  -> rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200}
  -> i:size_nat{i < inputByteLen / rateInBytes}
  -> Lemma (i * rateInBytes + rateInBytes <= inputByteLen)
let lemma_rateInBytes _ _ _ = ()

inline_for_extraction noextract
val absorb_inner:
    rateInBytes:size_t{0 < v rateInBytes /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> i:size_t{v i < v inputByteLen / v rateInBytes}
  -> s:state
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 input /\ disjoint s input)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s == S.absorb_inner (v rateInBytes) (v inputByteLen) 
        (as_seq h0 input) (v i) (as_seq h0 s))
let absorb_inner rateInBytes inputByteLen input i s =
  lemma_rateInBytes (v inputByteLen) (v rateInBytes) (v i);
  let block = sub input (i *. rateInBytes) rateInBytes in
  // SZ: repeat_blocks is defined in terms of LSeq.seq_sub but sub is specified
  // in terms of LSeq.sub, so we need to prove extensional equality explicitly.
  let h = ST.get () in
  LSeq.eq_intro
    (LSeq.sub #_ #(v inputByteLen) (as_seq h input) (v (i *. rateInBytes)) (v rateInBytes))
    (LSeq.seq_sub (as_seq h input) (v (i *. rateInBytes)) (v rateInBytes));
  loadState rateInBytes block s;
  state_permute s

val absorb:
    s:state
  -> rateInBytes:size_t{0 < v rateInBytes /\ v rateInBytes <= 200}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:byte_t
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 input /\ disjoint s input)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer s) h0 h1 /\
      as_seq h1 s ==
      S.absorb (as_seq h0 s) (v rateInBytes) (v inputByteLen) 
        (as_seq h0 input) delimitedSuffix)
let absorb s rateInBytes inputByteLen input delimitedSuffix =
  let nb = inputByteLen /. rateInBytes in
  let rem = inputByteLen %. rateInBytes in
  [@ inline_let]
  let spec h0 = S.absorb_inner (v rateInBytes) (v inputByteLen) (as_seq h0 input) in
  let h0 = ST.get () in
  loop1 h0 nb s spec (fun i -> 
    Loop.unfold_repeati (v nb) (spec h0) (as_seq h0 s) (v i);
    absorb_inner rateInBytes inputByteLen input i s);
  let last = sub input (nb *. rateInBytes) rem in
  // SZ: repeat_blocks is defined in terms of LSeq.seq_sub but sub is specified
  // in terms of LSeq.sub, so we need to prove extensional equality explicitly.
  let h = ST.get () in
  LSeq.eq_intro
    (LSeq.sub #_ #(v inputByteLen) (as_seq h input) (v (nb *. rateInBytes)) (v rem))
    (LSeq.seq_sub (as_seq h input) (v (nb *. rateInBytes)) (v rem));
  absorb_last delimitedSuffix rateInBytes rem last s

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

val lemma_update_squeeze:
    rateInBytes:size_nat{0 < rateInBytes /\ rateInBytes <= 200}
  -> outputByteLen:size_nat
  -> i:size_nat{i < outputByteLen / rateInBytes}
  -> s:S.state
  -> o:LB.lbytes (i * rateInBytes)
  -> o1:LB.lbytes (i * rateInBytes + rateInBytes)
  -> Lemma
    (requires
      LSeq.sub o1 0 (i * rateInBytes) == LSeq.sub o 0 (i * rateInBytes) /\
      LSeq.sub o1 (i * rateInBytes) rateInBytes == S.storeState rateInBytes s)
    (ensures o1 == snd (S.squeeze_inner rateInBytes outputByteLen i (s, o)))
let lemma_update_squeeze rateInBytes outputByteLen i s o o1 =
  Seq.lemma_split (LSeq.sub o1 0 (i * rateInBytes + rateInBytes)) (i * rateInBytes);
  // SZ: applying the above lemma is useless without knowing that 
  // LSeq.append is FStar.Seq.append and that LSeq.sub s o1 ... == Seq.slice ...
  // We can either prove a similar lemma written in terms of LSeq.sub and
  // LSeq.append in LSeq, or make some definitions transparent
  admit()

inline_for_extraction noextract
val squeeze_inner:
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v (outputByteLen /. rateInBytes)}
  -> s:state
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 output /\ disjoint s output)
    (ensures  fun h0 _ h1 ->
      lemma_rateInBytes (v outputByteLen) (v rateInBytes) (v i);
      modifies (loc_union (loc_buffer s) (loc_buffer output)) h0 h1 /\
      (let o = as_seq h0 (gsub output (size 0) (i *! rateInBytes)) in
       let s', output' =
         S.squeeze_inner (v rateInBytes) (v outputByteLen) (v i) (as_seq h0 s, o) in
       as_seq h1 s == s' /\
       as_seq h1 (gsub output (size 0) ((i +! size 1) *! rateInBytes)) == output'))
let squeeze_inner rateInBytes outputByteLen i s output =
  lemma_rateInBytes (v outputByteLen) (v rateInBytes) (v i);
  let h0 = ST.get () in
  storeState rateInBytes s (sub output (i *! rateInBytes) rateInBytes);
  let h1 = ST.get () in
  state_permute s;
  let o = as_seq h0 (gsub output (size 0) (i *! rateInBytes)) in
  let o' = as_seq h1 (gsub  output (size 0) ((i +! size 1) *! rateInBytes)) in
  lemma_update_squeeze (v rateInBytes) (v outputByteLen) (v i) (as_seq h1 s) o o'

#set-options "--max_ifuel 1"

val squeeze:
    s:state
  -> rateInBytes:size_t{0 < v rateInBytes /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 output /\ disjoint s output)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer s) (loc_buffer output)) h0 h1 /\
      as_seq h1 output ==
      S.squeeze (as_seq h0 s) (v rateInBytes) (v outputByteLen))
let squeeze s rateInBytes outputByteLen output = admit(); //TODO: add loop2
  let h0 = ST.get() in
  assert_norm (norm [delta]
    S.squeeze (as_seq h0 s) (v rateInBytes) (v outputByteLen) ==
    S.squeeze (as_seq h0 s) (v rateInBytes) (v outputByteLen));
  let outBlocks = outputByteLen /. rateInBytes in
  let remOut = outputByteLen %. rateInBytes in
  let tmp = sub output (outputByteLen -. remOut) remOut in
  let a_spec (i:size_nat{i <= v outputByteLen / v rateInBytes}) =
    S.state & (LB.lbytes (i * v rateInBytes)) in
  let a_impl = state & (lbytes (v outputByteLen)) in
  let refl h (i:size_nat{i <= v outBlocks}) :
    GTot (S.state & (LB.lbytes (i * v rateInBytes))) =
    assert (i * v rateInBytes <= v outputByteLen);
    as_seq h s,
    as_seq h (gsub output (size 0) (size i *! rateInBytes))
  in
  let footprint i = loc_union (loc_buffer s) (loc_buffer output) in
  let spec h0: i:size_nat{i < v outBlocks} -> a_spec i -> a_spec (i + 1) =
    S.squeeze_inner (v rateInBytes) (v outputByteLen) in
  let h0 = ST.get () in
  loop h0 outBlocks a_spec a_impl (s, output) refl footprint spec
  (fun i ->
    Loop.unfold_repeat_gen (v outBlocks) a_spec (spec h0) (refl h0 0) (v i);
    squeeze_inner rateInBytes outputByteLen i s output
  );
  storeState remOut s tmp;
  let h1 = ST.get() in
  Seq.lemma_split (as_seq h1 output) (v outputByteLen - v remOut);
  Seq.lemma_eq_intro (LSeq.create 0 (u8 0))
    (as_seq h0 (gsub output (size 0) (size 0)))

#set-options "--max_ifuel 0"

val keccak:
    rate:size_t{v rate % 8 == 0 /\ v rate / 8 > 0 /\ v rate <= 1600}
  -> capacity:size_t{v capacity + v rate == 1600}
  -> inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output ==
      S.keccak (v rate) (v capacity) (v inputByteLen) (as_seq h0 input) delimitedSuffix (v outputByteLen))
let keccak rate capacity inputByteLen input delimitedSuffix outputByteLen output =
  push_frame();
  let rateInBytes = rate /. size 8 in
  let s:state = create (size 25) (u64 0) in
  absorb s rateInBytes inputByteLen input delimitedSuffix;
  squeeze s rateInBytes outputByteLen output;
  pop_frame()
