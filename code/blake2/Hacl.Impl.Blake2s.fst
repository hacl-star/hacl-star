module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2



(* Define algorithm parameters *)
type working_vector = lbuffer uint32 Spec.size_block_w
type message_block_w = lbuffer uint32 Spec.size_block_w
type message_block = lbuffer uint8 (Spec.size_block Spec.Blake2S)
type state = lbuffer uint32 Spec.size_hash_w
type index_t = n:size_t{size_v n < 16}

inline_for_extraction let size_word : size_t = 4ul

inline_for_extraction let size_block x : size_t = (size Spec.size_block_w) *. size_word

(* Constants *)
inline_for_extraction let const_iv = icreateL_global Spec.list_iv_S
inline_for_extraction let const_sigma = icreateL_global Spec.list_sigma
inline_for_extraction let rTable_S = icreateL_global Spec.rTable_list_S

(* Define algorithm functions *)
val g1: wv:working_vector -> a:index_t -> b:index_t -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 Spec.Blake2S h0.[wv] (v a) (v b) r))

let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:index_t -> b:index_t -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 Spec.Blake2S h0.[wv] (v a) (v b) x))

let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (wv_a +. wv_b) x


val blake2_mixing : wv:working_vector -> a:index_t -> b:index_t -> c:index_t -> d:index_t -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing Spec.Blake2S h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  recall_contents rTable_S (Seq.of_list Spec.rTable_list_S);
  g2 wv a b x;
  g1 wv d a (iindex rTable_S (size 0));
  g2 wv c d (u32 0);
  g1 wv b c (iindex rTable_S (size 1));
  g2 wv a b y;
  g1 wv d a (iindex rTable_S (size 2));
  g2 wv c d (u32 0);
  g1 wv b c (iindex rTable_S (size 3));
  admit()

#reset-options "--z3rlimit 150"

val blake2_round1 : wv:working_vector -> m:message_block_w -> i:size_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m /\ disjoint m wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round1 Spec.Blake2S h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i =
  recall_contents const_sigma (Seq.of_list Spec.list_sigma);
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = isub #Spec.sigma_elt_t #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(iindex s (size 0))) (m.(iindex s (size 1)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(iindex s (size 2))) (m.(iindex s (size 3)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(iindex s (size 4))) (m.(iindex s (size 5)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(iindex s (size 6))) (m.(iindex s (size 7)));
  admit()


val blake2_round2 : wv:working_vector -> m:message_block_w -> i:size_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                   /\ disjoint wv m /\ disjoint m wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 Spec.Blake2S h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i =
  recall_contents const_sigma (Seq.of_list Spec.list_sigma);
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = isub #Spec.sigma_elt_t #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(iindex s (size 8))) (m.(iindex s (size 9)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(iindex s (size 10))) (m.(iindex s (size 11)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(iindex s (size 12))) (m.(iindex s (size 13)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(iindex s (size 14))) (m.(iindex s (size 15)));
  admit()

#reset-options

val blake2_round : wv:working_vector -> m:message_block_w -> i:size_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                   /\ disjoint wv m /\ disjoint m wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round Spec.Blake2S h0.[m] (v i) h0.[wv]))

let blake2_round wv m i =
  blake2_round1 wv m i;
  blake2_round2 wv m i


val blake2_compress1:
  wv:working_vector
  -> s:state
  -> m:message_block_w
  -> offset:uint64
  -> flag:bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv
                     /\ disjoint wv s /\ disjoint wv m
                     /\ disjoint s wv /\ disjoint m wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress1 Spec.Blake2S h0.[wv] h0.[s] h0.[m] offset flag))

[@ Substitute ]
let blake2_compress1 wv s m offset flag =
  recall_contents const_iv (Seq.of_list Spec.list_iv_S);
  update_sub wv (size 0) (size 8) s;
  admit();
  update_isub wv (size 8) (size 8) const_iv;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. size 32) in
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (ones U32 SEC) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


#reset-options "--z3rlimit 15"

val blake2_compress2 :
  wv:working_vector -> m:message_block_w ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                   /\ disjoint wv m /\ disjoint m wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 Spec.Blake2S h0.[wv] h0.[m]))

[@ Substitute ]
let blake2_compress2 wv m =
  [@inline_let]
  let spec h = Spec.blake2_round Spec.Blake2S h.[m] in
  let h0 = ST.get () in
  admit();
  loop1 #uint32 #Spec.size_block_w h0 (size (Spec.rounds Spec.Blake2S)) wv
    (fun h -> spec h)
    (fun i ->
       Loops.unfold_repeati (Spec.rounds Spec.Blake2S) (spec h0) (as_seq h0 wv) (v i);
       blake2_round wv m i)


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:state ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                   /\ disjoint s wv /\ disjoint wv s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner Spec.Blake2S h0.[wv] (v i) h0.[s]))

[@ Substitute ]
let blake2_compress3_inner wv i s =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  wv:working_vector -> s:state ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                     /\ disjoint wv s /\ disjoint s wv))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 Spec.Blake2S h0.[wv] h0.[s]))

[@ Substitute ]
let blake2_compress3 wv s =
  [@inline_let]
  let spec h = Spec.blake2_compress3_inner Spec.Blake2S h.[wv] in
  let h0 = ST.get () in
  admit();
  loop1 h0 (size 8) s
    (fun h -> spec h)
    (fun i ->
      Loops.unfold_repeati 8 (spec h0) (as_seq h0 s) (v i);
      blake2_compress3_inner wv i s)


val blake2_compress :
    s:state
  -> m:message_block_w
  -> offset:uint64
  -> flag:bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m
                     /\ disjoint s m /\ disjoint m s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress Spec.Blake2S h0.[s] h0.[m] offset flag))

let blake2_compress s m offset flag =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = h1.[s] == Spec.blake2_compress Spec.Blake2S h0.[s] h0.[m] offset flag in
  salloc1_trivial h0 (size 16) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer s)) spec
  (fun wv ->
    admit();
    blake2_compress1 wv s m offset flag;
    blake2_compress2 wv m;
    blake2_compress3 wv s)


val blake2s_update_block:
    hash:state
  -> prev:size_t{size_v prev <= Spec.max_limb Spec.Blake2S}
  -> d:message_block ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d
                   /\ disjoint hash d /\ disjoint d hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.blake2_update_block Spec.Blake2S (v prev) h0.[d] h0.[hash]))

let blake2s_update_block hash prev d =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 16) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun _ h1 -> h1.[d] == Spec.blake2_update_block Spec.Blake2S (v prev) h0.[d] h0.[hash])
  (fun block_w ->
    admit();
    uints_from_bytes_le block_w (size Spec.size_block_w) d;
    let offset = to_u64 prev in
    blake2_compress hash block_w offset false
  )


val blake2s_init_hash:
    hash:state
  -> kk:size_t{v kk <= 32}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
     (requires (fun h -> live h hash))
     (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                          /\ h1.[hash] == Spec.blake2_init_hash Spec.Blake2S h0.[hash] (v kk) (v nn)))

let blake2s_init_hash hash kk nn =
  let s0 = hash.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (size 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  hash.(size 0) <- s0'


val blake2s_init:
  #vkk:size_t
  -> hash:state
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init Spec.Blake2S (v kk) h0.[k] (v nn)))

[@ Substitute ]
let blake2s_init #vkk hash k kk nn =
  recall_contents const_iv (Seq.of_list Spec.list_iv_S);
  let h0 = ST.get () in
  salloc1_trivial h0 (size_block Spec.Blake2S) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun _ h1 -> h1.[hash] == Spec.blake2_init Spec.Blake2S (v kk) h0.[k] (v nn))
  (fun key_block ->
    admit();
    icopy hash (size Spec.size_hash_w) const_iv;
    blake2s_init_hash hash kk nn;
    if kk =. (size 0) then ()
    else begin
      update_sub key_block (size 0) kk k;
      blake2s_update_block hash (size 0) key_block end
  )

#reset-options

val blake2s_update_last:
    #vlen: size_t
  -> hash: state
  -> prev: size_t{v prev <= Spec.max_limb Spec.Blake2S}
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block Spec.Blake2S /\ len == vlen} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h last /\ disjoint hash last /\ disjoint last hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last Spec.Blake2S (v prev) (v len) h0.[last] h0.[hash]))

let blake2s_update_last #vlen hash prev last len =
  push_frame ();
  let last_block = create #uint8 64ul (u8 0) in
  let last_block_w = create #uint32 16ul (u32 0) in
  update_sub last_block (size 0) len last;
  uints_from_bytes_le last_block_w (size 16) last_block;
  blake2_compress hash last_block_w (to_u64 prev) true;
  pop_frame ()

val blake2s_finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> hash: state
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output /\ disjoint output hash /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn)))

let blake2s_finish #vnn output hash nn =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 32) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer output))
  (fun _ h1 -> h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn))
  (fun full ->
    admit();
    uints_to_bytes_le full (size 8) hash;
    let final = sub full (size 0) nn in
    copy output nn final)


val blake2s:
    #vll: size_t
  -> #vkk: size_t
  -> #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> d: lbuffer uint8 (v vll)
  -> ll: size_t{v ll == vll}
  -> k: lbuffer uint8 (v vkk)
  -> kk: size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> live h output /\ live h d /\ live h k
                   /\ disjoint output d /\ disjoint d output
                   /\ disjoint output k /\ disjoint k output))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn)))

let blake2s #vll #vkk #vnn output d ll k kk nn =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 8) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer output))
  (fun _ h1 -> h1.[output] == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn))
  (fun hash ->
    let klen = if kk = 0ul then 0ul else 1ul in
    blake2s_init #vkk hash k kk nn;
    [@ inline_let]
    let spec_f = (fun i -> Spec.blake2_update_block Spec.Blake2S (((v klen) + i + 1) * (Spec.size_block Spec.Blake2S))) in
    [@ inline_let]
    let spec_l = (fun i -> Spec.blake2_update_last Spec.Blake2S ((v klen) * (Spec.size_block Spec.Blake2S) + (v ll))) in
    loopi_blocks (size 64) ll d spec_f spec_l
      (fun i block hash -> blake2s_update_block hash ((klen +. i +. 1) *. (size 64)) block)
      (fun i rem last hash -> blake2s_update_last hash ll last rem) hash;
    blake2s_finish #vnn output hash nn
  )
