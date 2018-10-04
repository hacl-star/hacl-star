module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Endianness

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Spec = Spec.Blake2s

module LB = LowStar.Buffer
module IB = LowStar.ImmutableBuffer

///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
noextract let op_String_Access #a #r0 #r1 m b = LB.as_seq #a #r0 #r1 m b

///
/// Blake2s
///

(* Define algorithm parameters *)
type working_vector = lbuffer uint32 Spec.size_block_w
type message_block_w = lbuffer uint32 Spec.size_block_w
type message_block = lbuffer uint8 Spec.size_block
type state = lbuffer uint32 Spec.size_hash_w
type idx = n:size_t{size_v n < 16}
type iv_t = lbuffer uint32 Spec.size_hash_w
type sigma_elt = n:size_t{size_v n < 16}
type sigma_t = lbuffer sigma_elt 160


let const_iv = IB.igcmalloc_of_list HyperStack.root Spec.list_iv
let const_sigma = IB.igcmalloc_of_list HyperStack.root Spec.list_sigma



(* Define algorithm functions *)
val g1: wv:working_vector -> a:idx -> b:idx -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> LB.live h wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.g1 h0.[wv] (v a) (v b) r))

let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:idx -> b:idx -> x:uint32 ->
  Stack unit
    (requires (fun h -> LB.live h wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.g2 h0.[wv] (v a) (v b) x))

let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (wv_a +. wv_b) x


val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> LB.live h wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  g2 wv a b x;
  g1 wv d a Spec.r1;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r2;
  g2 wv a b y;
  g1 wv d a Spec.r3;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r4

#reset-options "--max_fuel 0 --z3rlimit 150"

val blake2_round1 : wv:working_vector -> m:message_block_w -> i:size_t ->
  Stack unit
    (requires (fun h -> LB.live h wv /\ LB.live h m
                  /\ LB.disjoint wv m /\ LB.disjoint m wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_round1 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i =
  IB.recall_contents const_sigma (FStar.Seq.seq_of_list Spec.list_sigma);
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = IB.isub #sigma_elt const_sigma (Lib.RawIntTypes.size_to_UInt32 start_idx) (16ul) in
  admit();
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(IB.index s (0ul))) (m.(IB.index s (1ul)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(IB.index s (2ul))) (m.(IB.index s (3ul)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(IB.index s (4ul))) (m.(IB.index s (5ul)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(IB.index s (6ul))) (m.(IB.index s (7ul)))


val blake2_round2 : wv:working_vector -> m:message_block_w -> i:size_t ->
  Stack unit
    (requires (fun h -> LB.live h wv /\ LB.live h m
                   /\ LB.disjoint wv m /\ LB.disjoint m wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i =
  IB.recall_contents const_sigma (FStar.Seq.seq_of_list Spec.list_sigma);
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = IB.isub #sigma_elt const_sigma (Lib.RawIntTypes.size_to_UInt32 start_idx) (16ul) in
  admit();
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(IB.index s (8ul))) (m.(IB.index s (9ul)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(IB.index s (10ul))) (m.(IB.index s (11ul)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(IB.index s (12ul))) (m.(IB.index s (13ul)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(IB.index s (14ul))) (m.(IB.index s (15ul)))


val blake2_round : wv:working_vector -> m:message_block_w -> i:size_t ->
  Stack unit
    (requires (fun h -> LB.live h wv /\ LB.live h m
                   /\ LB.disjoint wv m /\ LB.disjoint m wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.blake2_round h0.[m] (v i) h0.[wv]))

let blake2_round wv m i =
  blake2_round1 wv m i;
  blake2_round2 wv m i


val blake2_compress1:
  wv:working_vector
  -> s:state
  -> m:message_block_w
  -> offset:uint64
  -> flag:Spec.last_block_flag ->
  Stack unit
    (requires (fun h -> LB.live h s /\ LB.live h m /\ LB.live h wv
                     /\ LB.disjoint wv s /\ LB.disjoint wv m
                     /\ LB.disjoint s wv /\ LB.disjoint m wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_compress1 h0.[wv] h0.[s] h0.[m] offset flag))

[@ Substitute ]
let blake2_compress1 wv s m offset flag =
  IB.recall_contents const_iv (FStar.Seq.seq_of_list Spec.list_iv);
  update_sub wv (size 0) (size 8) s;
  assume(LB.disjoint wv const_iv);
  update_isub wv (size 8) (size 8) const_iv;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 32) in
  // BB. Note that using the ^. operator here would break extraction !
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14);
 admit()


val blake2_compress2 :
  wv:working_vector -> m:message_block_w ->
  Stack unit
    (requires (fun h -> LB.live h wv /\ LB.live h m
                   /\ LB.disjoint wv m /\ LB.disjoint m wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer wv) h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 h0.[wv] h0.[m]))

[@ Substitute ]
let blake2_compress2 wv m =
  let h0 = ST.get () in
  admit();
  loop1 #uint32 #Spec.size_block_w h0 (size Spec.rounds_in_f) wv
    (fun h -> Spec.blake2_round h0.[m])
    (fun i -> blake2_round wv m i)


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:state ->
  Stack unit
    (requires (fun h -> LB.live h s /\ LB.live h wv
                   /\ LB.disjoint s wv /\ LB.disjoint wv s))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer s) h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner h0.[wv] (v i) h0.[s]))

[@ Substitute ]
let blake2_compress3_inner wv i s =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  wv:working_vector -> s:state ->
  Stack unit
    (requires (fun h -> LB.live h s /\ LB.live h wv
                     /\ LB.disjoint wv s /\ LB.disjoint s wv))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer s) h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 h0.[wv] h0.[s]))

[@ Substitute ]
let blake2_compress3 wv s =
  admit();
  let h0 = ST.get () in
  loop1 h0 (size 8) s
    (fun h -> Spec.blake2_compress3_inner h.[wv])
    (fun i -> blake2_compress3_inner wv i s)


val blake2_compress :
  s:state -> m:message_block_w ->
  offset:uint64 -> f:Spec.last_block_flag ->
  Stack unit
    (requires (fun h -> LB.live h s /\ LB.live h m
                     /\ LB.disjoint s m /\ LB.disjoint m s))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer s) h0 h1
                         /\ h1.[s] == Spec.blake2_compress h0.[s] h0.[m] offset f))

let blake2_compress s m offset flag =
  let h0 = ST.get () in
  alloc #h0 (size 16) (u32 0) s
  (fun h0 ->
    let s0 = h0.[s] in
    let m0 = h0.[m] in
    (fun _ sv -> sv == Spec.Blake2s.blake2_compress s0 m0 offset flag))
  (fun wv ->
    admit();
    blake2_compress1 wv s m offset flag;
    blake2_compress2 wv m;
    blake2_compress3 wv s)

inline_for_extraction
val blake2s_update_block:
    hash:state
  -> dd_prev:size_t{(size_v dd_prev + 1) * Spec.size_block <= max_size_t}
  -> d:message_block ->
  Stack unit
    (requires (fun h -> LB.live h hash /\ LB.live h d
                   /\ LB.disjoint hash d /\ LB.disjoint d hash))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.blake2s_update_block (v dd_prev) h0.[d] h0.[hash]))

let blake2s_update_block hash dd_prev d =
  let h0 = ST.get () in
  alloc #h0 (size 16) (u32 0) hash
  (fun h0 ->
    let d0 = h0.[d] in
    let s0 = h0.[hash] in
    (fun _ sv -> sv == Spec.blake2s_update_block (v dd_prev) d0 s0))
  (fun block ->
    admit();
    uints_from_bytes_le block (size Spec.size_block_w) d;
    let offset64 = to_u64 (size_to_uint32 ((dd_prev +. (size 1)) *. (size Spec.size_block))) in
    blake2_compress hash block offset64 false
  )

val blake2s_mkstate: unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures  (fun h0 hash h1 -> LB.live h1 hash))

let blake2s_mkstate () = create (size Spec.size_hash_w) (u32 0)

val blake2s_init_hash:
    hash:state
  -> kk:size_t{v kk <= 32}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
     (requires (fun h -> LB.live h hash))
     (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                          /\ h1.[hash] == Spec.Blake2s.blake2s_init_hash h0.[hash] (v kk) (v nn)))

let blake2s_init_hash hash kk nn =
  let s0 = hash.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  hash.(size 0) <- s0'


val blake2s_init:
  #vkk:size_t
  -> hash:state
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> LB.live h hash
                   /\ LB.live h k
                   /\ LB.disjoint hash k /\ LB.disjoint k hash))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2s.blake2s_init (v kk) h0.[k] (v nn)))

[@ Substitute ]
let blake2s_init #vkk hash k kk nn =
  IB.recall_contents const_iv (FStar.Seq.seq_of_list Spec.list_iv);
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) hash
  (fun h -> (fun _ sv -> sv == Spec.Blake2s.blake2s_init (v kk) h0.[k] (v nn)))
  (fun key_block ->
    admit();
    icopy hash (size Spec.size_hash_w) const_iv;
    blake2s_init_hash hash kk nn;
    if kk =. (size 0) then ()
    else begin
      update_sub key_block (size 0) kk k;
      blake2s_update_block hash (size 0) key_block end
  )


val blake2s_update_multi_iteration:
    hash:state
  -> dd_prev:size_t
  -> dd:size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d:lbuffer uint8 (v dd * Spec.size_block)
  -> i:size_t{v i + 1 <= v dd} ->
  Stack unit
    (requires (fun h -> LB.live h hash
                   /\ LB.live h d /\ LB.disjoint hash d /\ LB.disjoint d hash))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) h0.[d] (v i) h0.[hash]))

[@ Substitute ]
let blake2s_update_multi_iteration st dd_prev dd d i =
  let block = sub d (i *. size Spec.size_block) (size Spec.size_block) in
  blake2s_update_block st (dd_prev +. i) block;
  admit()


val blake2s_update_multi:
    hash: state
  -> dd_prev: size_t
  -> dd: size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d: lbuffer uint8 (size_v dd * Spec.size_block) ->
   Stack unit
     (requires (fun h -> LB.live h hash
                    /\ LB.live h d /\ LB.disjoint hash d /\ LB.disjoint d hash))
     (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                          /\ h1.[hash] == Spec.blake2s_update_multi (v dd_prev) (v dd) h0.[d] h0.[hash]))

let blake2s_update_multi hash dd_prev dd d =
  admit();
  let h0 = ST.get () in
  loop1 h0 dd hash
    (fun h -> Spec.Blake2s.blake2s_update_multi_iteration (v dd_prev) (v dd) h.[d])
    (fun i -> blake2s_update_multi_iteration hash dd_prev dd d i)


val blake2s_update_last:
    #vlen: size_t
  -> hash: state
  -> ll: size_t
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block /\ len == vlen}
  -> flag_key: bool ->
  Stack unit
    (requires (fun h -> LB.live h hash
                   /\ LB.live h last /\ LB.disjoint hash last /\ LB.disjoint last hash))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2s.blake2s_update_last (v ll) (v len) h0.[last] flag_key h0.[hash]))


let blake2s_update_last #vlen hash ll last len fk =
  let ll64 : uint64 = to_u64 #U32 (size_to_uint32 ll) in
  let ll_plus_block_bytes64 = ll64 +. (u64 Spec.size_block) in
  assume(ll_plus_block_bytes64 == u64 (size_v ll + Spec.size_block));
  (**) let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) hash
  (fun h ->
    let hash0 = h0.[hash] in
    let last0 = h0.[last] in
    (fun _ r -> r == Spec.Blake2s.blake2s_update_last (v ll) (v len) last0 fk hash0)
  )
  (fun last_block ->
    admit();
    update_sub last_block (size 0) len last;
    (**) let h1 = ST.get () in
    alloc #h1 (size Spec.size_block_w) (u32 0) hash
    (fun h ->
      let hash1 = h1.[hash] in
      let last_block1 = h1.[last_block] in
      (fun _ r -> r == Spec.Blake2s.blake2s_update_last_block (v ll) last_block1 fk hash1)
    )
    (fun last_block_w ->
      uint32s_from_bytes_le last_block_w (size 16) last_block;
      if not fk then
        blake2_compress hash last_block_w ll64 true
      else
        blake2_compress hash last_block_w ll_plus_block_bytes64 true
    )
  )


val blake2s_update_last_empty:
  hash: state ->
  Stack unit
    (requires (fun h -> LB.live h hash))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer hash) h0 h1
                         /\ (let data = Seq.create Spec.size_block (u8 0) in
                           h1.[hash] == Spec.Blake2s.blake2s_update_last (Spec.size_block) (Spec.size_block) data false h0.[hash])))

let blake2s_update_last_empty hash =
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) hash
  (fun h0 ->
    let hash0 = h0.[hash] in
    (fun _ r ->
      let data = Seq.create Spec.size_block (u8 0) in
      r ==  Spec.Blake2s.blake2s_update_last (Spec.size_block) (Spec.size_block) data false hash0))
  (fun data ->
    admit();
    blake2s_update_last #(size Spec.size_block) hash (size Spec.size_block) data (size Spec.size_block) false)


val blake2s_finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> hash: state
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> LB.live h hash
                   /\ LB.live h output /\ LB.disjoint output hash /\ LB.disjoint hash output))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2s.blake2s_finish h0.[hash] (v nn)))

let blake2s_finish #vnn output hash nn =
  (**) let h0 = ST.get () in
  alloc #h0 (size 32) (u8 0) output
  (fun h ->
    (fun _ r -> r == Spec.Blake2s.blake2s_finish h0.[hash] (v nn))
  )
  (fun full ->
    admit();
    uints_to_bytes_le full (size 8) hash;
    let final = sub full (size 0) nn in
    copy output nn final)


inline_for_extraction noextract
val blake2s:
    #vll: size_t
  -> #vkk: size_t
  -> #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> d: lbuffer uint8 (v vll)
  -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ ll == vll} // This could be relaxed
  -> k: lbuffer uint8 (v vkk)
  -> kk: size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> LB.live h output /\ LB.live h d /\ LB.live h k
                   /\ LB.disjoint output d /\ LB.disjoint d output
                   /\ LB.disjoint output k /\ LB.disjoint k output))
    (ensures  (fun h0 _ h1 -> LB.modifies (LB.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn)))

let blake2s #vll #vkk #vnn output d ll k kk nn =
  let h0 = ST.get () in
  alloc #h0 (size 8) (u32 0) output
  (fun h -> (fun _ r -> r == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn)))
  (fun hash ->
    let fk = if kk =. (size 0) then false else true in
    let rem = ll %. (size Spec.size_block) in
    let nblocks = ll /. (size Spec.size_block) in
    let blocks = sub #_ #_ #(v nblocks * Spec.size_block) d (size 0) (nblocks *. (size Spec.size_block)) in
    let last = sub #_ #_ #(v rem) d (nblocks *. (size Spec.size_block)) rem in
    admit();
    blake2s_init #vkk hash k kk nn;
    if ll =. (size 0) && kk =. (size 0) then blake2s_update_last_empty hash
    else begin
      let nprev = if kk =. (size 0) then (size 0) else (size 1) in
      blake2s_update_multi hash nprev nblocks d;
      blake2s_update_last #rem hash ll last rem fk
    end;
    blake2s_finish #vnn output hash nn)
