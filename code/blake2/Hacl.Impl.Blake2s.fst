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
type vector_wp = lbuffer uint32 (size Spec.size_block_w)
type block_wp = lbuffer uint32 (size Spec.size_block_w)
type block_p = lbuffer uint8 (size (Spec.size_block Spec.Blake2S))
type hash_wp = lbuffer uint32 (size Spec.size_hash_w)
type index_t = n:size_t{size_v n < 16}

inline_for_extraction
let size_word : size_t = size 4

inline_for_extraction
let size_block x : n:size_t{v n > 0 /\ v n == Spec.size_block Spec.Blake2.Blake2S} = (size Spec.size_block_w) *. size_word


/// Constants


let const_iv: x:ilbuffer size_t 8ul{witnessed x (Spec.Blake2.ivTable Spec.Blake2.Blake2S) /\ recallable x} =
  createL_global Spec.Blake2.list_iv_S

let const_sigma: x:ilbuffer Spec.Blake2.sigma_elt_t 160ul{witnessed x Spec.Blake2.const_sigma /\ recallable x} =
  createL_global Spec.Blake2.list_sigma

let rTable_S: x:ilbuffer (rotval U32) 4ul{witnessed x (Spec.Blake2.rTable Spec.Blake2.Blake2S) /\ recallable x} =
  createL_global Spec.Blake2.rTable_list_S


/// Accessors for constants

val get_iv:
  s: size_t{size_v s < 8} ->
  Stack uint32
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      uint_v z == uint_v (Seq.index (Spec.ivTable Spec.Blake2S) (size_v s))))

[@ Substitute ]
let get_iv s =
  recall_contents const_iv (Spec.ivTable Spec.Blake2S);
  let r : size_t = index const_iv s in
  secret r


#set-options "--z3rlimit 50"

let op_String_Access (#a:Type) (#len:size_t) (h:mem) (b:lbuffer a len) = as_seq h b

val set_iv:
  hash: hash_wp ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Seq.map secret (Spec.ivTable Spec.Blake2S)))
[@ Substitute ]
let set_iv hash =
  recall_contents const_iv (Spec.ivTable Spec.Blake2S);
  let h0 = ST.get() in
  mapT (size (Spec.size_hash_w)) hash secret const_iv


#set-options "--z3rlimit 15"

val set_iv_sub:
  b: lbuffer uint32 16ul ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies1 b h0 h1
                      /\ (let b0: Seq.lseq uint32 16 = h0.[b] in
                         let b1: Seq.lseq uint32 16 = h1.[b] in
                         let src = Seq.map secret (Spec.ivTable Spec.Blake2S) in
                         b1 == Seq.update_sub b0 8 8 src)))
[@ Substitute ]
let set_iv_sub b =
  let h0 = ST.get () in
  let half0 = sub b (size 0) (size 8) in
  let half1 = sub b (size 8) (size 8) in
  let h1 = ST.get () in
  set_iv half1;
  let h2 = ST.get () in
  Seq.eq_intro h2.[b] (Seq.concat h2.[half0] h2.[half1]);
  Seq.eq_intro h2.[b] (Seq.update_sub h0.[b] 8 8 (Seq.map secret (Spec.ivTable Spec.Blake2S)))


#reset-options

val get_sigma:
  s: size_t{v s < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.const_sigma (v s))))

[@ Substitute ]
let get_sigma s =
  recall_contents const_sigma Spec.const_sigma;
  index const_sigma s


#set-options "--z3rlimit 15"

val get_sigma_sub:
  start: size_t ->
  i: size_t{v i < 16 /\ v start + v i < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.const_sigma (v start + v i))))

[@ Substitute ]
let get_sigma_sub start i = get_sigma (start +. i)


#reset-options

val get_r:
  s: size_t{v s < 4} ->
  Stack (rotval U32)
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index (Spec.rTable Spec.Blake2S) (v s))))

[@ Substitute ]
let get_r s =
  recall_contents rTable_S (Spec.rTable Spec.Blake2S);
  index rTable_S s


/// Define algorithm functions

val g1: wv:vector_wp -> a:index_t -> b:index_t -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 Spec.Blake2S h0.[wv] (v a) (v b) r))

let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:vector_wp -> a:index_t -> b:index_t -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 Spec.Blake2S h0.[wv] (v a) (v b) x))

let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (wv_a +. wv_b) x


val blake2_mixing : wv:vector_wp -> a:index_t -> b:index_t -> c:index_t -> d:index_t -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing Spec.Blake2S h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  let r0 = get_r (size 0) in
  let r1 = get_r (size 1) in
  let r2 = get_r (size 2) in
  let r3 = get_r (size 3) in
  g2 wv a b x;
  g1 wv d a r0;
  g2 wv c d (u32 0);
  g1 wv b c r1;
  g2 wv a b y;
  g1 wv d a r2;
  g2 wv c d (u32 0);
  g1 wv b c r3


#set-options "--z3rlimit 25"

val blake2_round1 : wv:vector_wp -> m:block_wp -> i:size_t{v i <= 9} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round1 Spec.Blake2S h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i =
  let start_idx = (i %. size 10) *. size 16 in
  assert (v start_idx == (v i % 10) * 16);
  let s0 = get_sigma_sub start_idx (size 0) in
  let s1 = get_sigma_sub start_idx (size 1) in
  let s2 = get_sigma_sub start_idx (size 2) in
  let s3 = get_sigma_sub start_idx (size 3) in
  let s4 = get_sigma_sub start_idx (size 4) in
  let s5 = get_sigma_sub start_idx (size 5) in
  let s6 = get_sigma_sub start_idx (size 6) in
  let s7 = get_sigma_sub start_idx (size 7) in
  blake2_mixing wv (size 0) (size 4) (size 8) (size 12) m.(s0) m.(s1);
  blake2_mixing wv (size 1) (size 5) (size 9) (size 13) m.(s2) m.(s3);
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) m.(s4) m.(s5);
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) m.(s6) m.(s7)



#set-options "--z3rlimit 25"

val blake2_round2 : wv:vector_wp -> m:block_wp -> i:size_t{v i <= 9} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 Spec.Blake2S h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i =
  let start_idx = (i %. size 10) *. size 16 in
  assert (v start_idx == (v i % 10) * 16);
  let s0 = get_sigma_sub start_idx (size 8) in
  let s1 = get_sigma_sub start_idx (size 9) in
  let s2 = get_sigma_sub start_idx (size 10) in
  let s3 = get_sigma_sub start_idx (size 11) in
  let s4 = get_sigma_sub start_idx (size 12) in
  let s5 = get_sigma_sub start_idx (size 13) in
  let s6 = get_sigma_sub start_idx (size 14) in
  let s7 = get_sigma_sub start_idx (size 15) in
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) m.(s0) m.(s1);
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) m.(s2) m.(s3);
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) m.(s4) m.(s5);
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) m.(s6) m.(s7)
  

#reset-options

val blake2_round: wv:vector_wp -> m:block_wp -> i:size_t{v i <= 9} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                   /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round Spec.Blake2S h0.[m] (v i) h0.[wv]))

let blake2_round wv m i =
  blake2_round1 wv m i;
  blake2_round2 wv m i


#reset-options "--z3rlimit 15"

val blake2_compress1:
    wv: vector_wp
  -> s: hash_wp
  -> m: block_wp
  -> offset: uint64
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv
                     /\ disjoint wv s /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress1 Spec.Blake2S h0.[wv] h0.[s] h0.[m] offset flag))

[@ Substitute ]
let blake2_compress1 wv s m offset flag =
  update_sub wv (size 0) (size 8) s;
  set_iv_sub wv;
  let low_offset = Spec.limb_to_word Spec.Blake2S offset in
  let high_offset = Spec.limb_to_word Spec.Blake2S (offset >>. size 32) in
  let wv_12 = logxor wv.(size 12) low_offset in
  let wv_13 = logxor wv.(size 13) high_offset in
  let wv_14 = logxor wv.(size 14) (ones (Spec.wt Spec.Blake2S) SEC) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


#reset-options "--z3rlimit 25"

val blake2_compress2 :
    wv: vector_wp
  -> m: block_wp ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 Spec.Blake2S h0.[wv] h0.[m]))

noextract inline_for_extraction
let rounds_nat:x:size_nat{x == Spec.rounds Spec.Blake2.Blake2S} = 10
noextract inline_for_extraction
let rounds_t:x:size_t{x == size rounds_nat} = 10ul

[@ Substitute ]
let blake2_compress2 wv m =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.blake2_round Spec.Blake2S h.[m] in
  loop1 h0 rounds_t wv spec
  (fun i ->
    Loops.unfold_repeati rounds_nat (spec h0) h0.[wv] (v i);
    blake2_round wv m i;
    let h' = ST.get() in
    assert (modifies (loc wv) h0 h'))



#reset-options "--z3rlimit 15"

val blake2_compress3_inner :
    wv: vector_wp
  -> i: size_t{v i < 8}
  -> s: hash_wp ->
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


#reset-options "--z3rlimit 25"

val blake2_compress3 :
    wv: vector_wp
  -> s: hash_wp ->
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
  loop1 h0 (size 8) s
    (fun h -> spec h)
    (fun i ->
      Loops.unfold_repeati 8 (spec h0) (as_seq h0 s) (v i);
      blake2_compress3_inner wv i s)


#reset-options "--z3rlimit 25"

val blake2_compress :
    s: hash_wp
  -> m: block_wp
  -> offset: uint64
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m
                     /\ disjoint s m /\ disjoint m s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress Spec.Blake2S h0.[s] h0.[m] offset flag))

let blake2_compress s m offset flag =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = live h1 s /\ h1.[s] == Spec.blake2_compress Spec.Blake2S h0.[s] h0.[m] offset flag in
  salloc1_trivial h0 (size 16) (u32 0) (Ghost.hide (loc s)) spec
  (fun wv ->
    blake2_compress1 wv s m offset flag;
    blake2_compress2 wv m;
    blake2_compress3 wv s)


#reset-options "--z3rlimit 50"

val blake2s_update_block:
    hash: hash_wp
  -> prev: uint64{uint_v prev <= Spec.Blake2.max_limb Spec.Blake2S}
  -> d: block_p ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.blake2_update_block Spec.Blake2S (uint_v prev) h0.[d] h0.[hash]))

let blake2s_update_block hash prev d =
  admit();
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = live h1 hash /\ h1.[hash] == Spec.blake2_update_block Spec.Blake2S (uint_v prev) h0.[d] h0.[hash] in
  salloc1_trivial h0 (size 16) (u32 0) (Ghost.hide (loc hash)) spec
  (fun block_w ->
     uints_from_bytes_le block_w d;
     let offset = prev in
     blake2_compress hash block_w offset false)


#reset-options

val blake2s_init_hash:
    hash: hash_wp
  -> kk: size_t{v kk <= 32}
  -> nn: size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
     (requires (fun h -> live h hash))
     (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                          /\ h1.[hash] == Spec.blake2_init_hash Spec.Blake2S (v kk) (v nn)))
[@ Substitute]
let blake2s_init_hash hash kk nn =
  set_iv hash;
  let s0 = hash.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (size 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  hash.(size 0) <- s0'


#reset-options "--z3rlimit 25"

val blake2s_init_branching:
    hash: hash_wp
  -> key_block: lbuffer uint8 64ul
  -> kk: size_t{v kk <= 32}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h k /\ live h key_block
                   /\ disjoint hash k /\ disjoint hash key_block /\ disjoint key_block k))
    (ensures  (fun h0 _ h1 -> modifies2 hash key_block h0 h1
                    /\ (if (v kk) = 0 then h1.[hash] == h0.[hash] else
                       let key_block1 = Seq.update_sub h0.[key_block] 0 (v kk) h0.[k] in
                       h1.[hash] == Spec.blake2_update_block Spec.Blake2S (Spec.size_block Spec.Blake2S) key_block1 h0.[hash])))

[@ Substitute ]
let blake2s_init_branching hash key_block kk k nn =
  let h0 = ST.get () in
  if kk <>. (size 0) then
  begin
    update_sub key_block (size 0) kk k;
    let prev = Spec.word_to_limb Spec.Blake2S (secret (size_block Spec.Blake2S)) in
    blake2s_update_block hash prev key_block
  end


#reset-options "--z3rlimit 15"

val blake2s_init:
    hash: hash_wp
  -> kk: size_t{v kk <= 32}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init Spec.Blake2S (v kk) h0.[k] (v nn)))

[@ Substitute ]
let blake2s_init hash kk k nn =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 64) (u8 0) (Ghost.hide (loc hash))
  (fun _ h1 -> live h1 hash /\ h1.[hash] == Spec.blake2_init Spec.Blake2S (v kk) h0.[k] (v nn))
  (fun key_block ->
    blake2s_init_hash hash kk nn;
    blake2s_init_branching hash key_block kk k nn)


#reset-options "--z3rlimit 15"

val blake2s_update_last:
    hash: hash_wp
  -> prev: uint64{uint_v prev <= Spec.Blake2.max_limb Spec.Blake2S}
  -> len: size_t{v len <= Spec.size_block Spec.Blake2S} 
  -> last: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last Spec.Blake2S (uint_v prev) (v len) h0.[last] h0.[hash]))

let blake2s_update_last hash prev len last =
  push_frame ();
  let last_block = create 64ul (u8 0) in
  let last_block_w = create 16ul (u32 0) in
  update_sub last_block (size 0) len last;
  uints_from_bytes_le last_block_w last_block;
  let offset = prev in
  blake2_compress hash last_block_w offset true;
  pop_frame ();
  admit()


#reset-options "--z3rlimit 25"

val blake2s_finish:
    nn: size_t{1 <= v nn /\ v nn <= 32} 
  -> output: lbuffer uint8 nn
  -> hash: hash_wp ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output /\ disjoint output hash /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn)))

let blake2s_finish nn output hash =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 32) (u8 0) (Ghost.hide (loc output))
  (fun _ h1 -> live h1 output /\ h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn))
  (fun full ->
    uints_to_bytes_le (size 8) full hash;
    let final = sub full (size 0) nn in
    copy output final)


#reset-options "--z3rlimit 50"

noextract inline_for_extraction
let spec_prev1 (klen:size_nat{klen == 0 \/ klen == 1})
	      (dlen:size_nat{if klen = 0 then dlen < pow2 64 else dlen + 64 < pow2 64})
	      (i:size_nat{i < dlen/64}) : r:nat{r < pow2 64} = (klen + i + 1) * 64

noextract inline_for_extraction
let spec_prev2 (klen:size_nat{klen == 0 \/ klen == 1})
	      (dlen:size_nat{if klen = 0 then dlen < pow2 64 else dlen + 64 < pow2 64})
	      (i:size_nat{i == dlen/64}) : r:nat{r < pow2 64} = (klen * 64) + dlen


noextract inline_for_extraction
let prev1 (klen:size_t{v klen == 0 \/ v klen == 1})
          (dlen:size_t{if v klen = 0 then v dlen < pow2 64 else v dlen + 64 < pow2 64})
	  (i:size_t{v i < v dlen/64}) :
	  (prev:uint64{uint_v prev == spec_prev1 (v klen) (v dlen) (v i)})
	  = let p = to_u64 (klen +. i +. size 1) *. u64 64 in
	    assert (uint_v p == spec_prev1 (v klen) (v dlen) (v i));
	    p

noextract inline_for_extraction
let prev2 (klen:size_t{v klen == 0 \/ v klen == 1})
          (dlen:size_t{if v klen = 0 then v dlen < pow2 64 else v dlen + 64 < pow2 64})
	  (i:size_t{v i == v dlen/64}) :
	  (prev:uint64{uint_v prev == spec_prev2 (v klen) (v dlen) (v i)})
	  = to_u64 dlen +. to_u64 (klen *. size 64)


#reset-options "--z3rlimit 150"

inline_for_extraction
val blake2s_update:
    hash: hash_wp
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.blake2_update Spec.Blake2S h0.[hash] h0.[d] (v kk)))

let blake2s_update hash ll d kk =
  let h0 = ST.get() in
  let klen = if kk =. size 0 then size 0 else size 1 in
  loopi_blocks (size_block Spec.Blake2S) ll d
    (Spec.spec_update_block Spec.Blake2S ((v klen + 1) * (Spec.size_block Spec.Blake2S)))
    (Spec.spec_update_last Spec.Blake2S (v klen * (Spec.size_block Spec.Blake2S) + v ll))
    (fun i block hash -> blake2s_update_block hash (prev1 klen ll i) block)
    (fun i len last hash -> blake2s_update_last hash (prev2 klen ll i) len last)
    hash


#reset-options "--z3rlimit 50"

val blake2s:
    nn:size_t{1 <= v nn /\ v nn <= 32} 
  -> output: lbuffer uint8 nn
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)}
  -> k: lbuffer uint8 kk ->
  Stack unit
    (requires (fun h -> live h output
                   /\ live h d
                   /\ live h k
                   /\ disjoint output d
                   /\ disjoint output k))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn)))

let blake2s nn output ll d kk k =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 8) (u32 0) (Ghost.hide (loc output))
  (fun _ h1 -> live h1 output /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn))
  (fun hash ->
    blake2s_init hash kk k nn;
    blake2s_update hash ll d kk;
    blake2s_finish nn output hash)
