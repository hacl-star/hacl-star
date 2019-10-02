module Hacl.Impl.Blake2

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

#set-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"

(* Define algorithm parameters *)
unfold type word_t (a:Spec.alg) = Spec.word_t a
type vector_wp (a:Spec.alg) = lbuffer (word_t a) (size Spec.size_block_w)
type block_wp (a:Spec.alg) = lbuffer (word_t a) (size Spec.size_block_w)
type block_p (a:Spec.alg) = lbuffer uint8 (size (Spec.size_block a))
type hash_wp (a:Spec.alg) = lbuffer (word_t a) (size Spec.size_hash_w)
type index_t = n:size_t{size_v n < 16}


inline_for_extraction
let size_word (a:Spec.alg): size_t = size (Spec.size_word a)

inline_for_extraction
let size_block (a:Spec.alg): x:size_t{v x = Spec.size_block a /\ v x <= Spec.max_limb a} = (size Spec.size_block_w) *! (size_word a)

noextract inline_for_extraction
let rounds_nat (a:Spec.alg): size_nat = Spec.rounds a

noextract inline_for_extraction
let rounds_t (a:Spec.alg): size_t = size (Spec.rounds a)

inline_for_extraction
val size_to_word: al:Spec.alg -> s:size_t -> u:word_t al{u == Spec.nat_to_word al (v s)}
let size_to_word al s = match al with
  | Spec.Blake2S -> size_to_uint32 s
  | Spec.Blake2B -> size_to_uint64 s

inline_for_extraction
val size_to_limb: al:Spec.alg -> s:size_t -> u:Spec.limb_t al{u == Spec.nat_to_limb al (v s)}
let size_to_limb al s = match al with
  | Spec.Blake2S -> size_to_uint64 s
  | Spec.Blake2B -> to_u128 (size_to_uint64 s)


/// Constants

let sigmaTable : x:ilbuffer Spec.Blake2.sigma_elt_t 160ul{witnessed x Spec.Blake2.sigmaTable /\ recallable x} =
  createL_global Spec.Blake2.list_sigma

let ivTable_S: (x:ilbuffer (Spec.pub_word_t Spec.Blake2S) 8ul{witnessed x (Spec.Blake2.ivTable Spec.Blake2S) /\ recallable x}) =
  createL_global Spec.Blake2.list_iv_S

let ivTable_B: (x:ilbuffer (Spec.pub_word_t Spec.Blake2B) 8ul{witnessed x (Spec.Blake2.ivTable Spec.Blake2B) /\ recallable x}) =
  createL_global Spec.Blake2.list_iv_B

let rTable_S : x:ilbuffer (rotval U32) 4ul{witnessed x (Spec.Blake2.rTable Spec.Blake2S) /\ recallable x} =
  createL_global Spec.Blake2.rTable_list_S

let rTable_B : x:ilbuffer (rotval U64) 4ul{witnessed x (Spec.Blake2.rTable Spec.Blake2B) /\ recallable x} =
  createL_global Spec.Blake2.rTable_list_B


/// Accessors for constants

val get_iv:
  a:Spec.alg
  -> s: size_t{size_v s < 8} ->
  Stack (word_t a)
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      v z == v (Seq.index (Spec.ivTable a) (v s))))

[@ Substitute ]
let get_iv a s =
  recall_contents #(Spec.pub_word_t Spec.Blake2S) #8ul ivTable_S (Spec.ivTable Spec.Blake2S);
  recall_contents #(Spec.pub_word_t Spec.Blake2B) #8ul ivTable_B (Spec.ivTable Spec.Blake2B);
  let ivTable: (x:ilbuffer (Spec.pub_word_t a) 8ul{witnessed x (Spec.Blake2.ivTable a) /\ recallable x}) =
    match a with
    | Spec.Blake2S -> ivTable_S
    | Spec.Blake2B -> ivTable_B
  in
  let r = index ivTable s in
  secret #(Spec.wt a) r


val set_iv:
  a:Spec.alg
  -> hash: hash_wp a ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                        /\ h1.[|hash|]  == Seq.map #(int_t (Spec.wt a) PUB) #(int_t (Spec.wt a) SEC) #8 secret (Spec.ivTable a)))
[@ Substitute ]
let set_iv a hash =
  recall_contents #(Spec.pub_word_t Spec.Blake2S) #8ul ivTable_S (Spec.ivTable Spec.Blake2S);
  recall_contents #(Spec.pub_word_t Spec.Blake2B) #8ul ivTable_B (Spec.ivTable Spec.Blake2B);
  let h0 = ST.get() in
  let ivTable: (x:ilbuffer (Spec.pub_word_t a) 8ul{witnessed x (Spec.Blake2.ivTable a) /\ recallable x}) =
    match a with
    | Spec.Blake2S -> ivTable_S
    | Spec.Blake2B -> ivTable_B
  in
  mapT (size (Spec.size_hash_w)) hash secret ivTable


val set_iv_sub:
  a:Spec.alg
  -> b:lbuffer (word_t a) 16ul ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies1 b h0 h1
                      /\ (let b0: Seq.lseq (word_t a) 16 = h0.[|b|] in
                         let b1: Seq.lseq (word_t a) 16 = h1.[|b|] in
                         let src = Seq.map secret (Spec.ivTable a) in
                         b1 == Seq.update_sub b0 8 8 src)))
[@ Substitute ]
let set_iv_sub a b =
  let h0 = ST.get () in
  let half0 = sub b (size 0) (size 8) in
  let half1 = sub b (size 8) (size 8) in
  let h1 = ST.get () in
  set_iv a half1;
  let h2 = ST.get () in
  Seq.eq_intro h2.[|b|] (Seq.concat h2.[|half0|] h2.[|half1|]);
  Seq.eq_intro h2.[|b|] (Seq.update_sub h0.[|b|] 8 8 (Seq.map secret (Spec.ivTable a)))


val get_sigma:
  s: size_t{v s < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.sigmaTable (v s))))

[@ Substitute ]
let get_sigma s =
  recall_contents sigmaTable Spec.sigmaTable;
  index sigmaTable s


val get_sigma_sub:
  start: size_t ->
  i: size_t{v i < 16 /\ v start + v i < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.sigmaTable (v start + v i))))

[@ Substitute ]
let get_sigma_sub start i = get_sigma (start +. i)


val get_r:
  a: Spec.alg
  -> s: size_t{v s < 4} ->
  Stack (rotval (Spec.wt a))
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index (Spec.rTable a) (v s))))

[@ Substitute ]
let get_r a s =
  recall_contents #(rotval (Spec.wt Spec.Blake2S)) #4ul rTable_S (Spec.rTable Spec.Blake2S);
  recall_contents #(rotval (Spec.wt Spec.Blake2B)) #4ul rTable_B (Spec.rTable Spec.Blake2B);
  let h0 = ST.get() in
  let rTable: (x:ilbuffer (rotval (Spec.wt a)) 4ul{witnessed x (Spec.Blake2.rTable a) /\ recallable x}) =
    match a with
    | Spec.Blake2S -> rTable_S
    | Spec.Blake2B -> rTable_B
  in
  index rTable s


/// Define algorithm functions

val g1: al:Spec.alg -> wv:vector_wp al -> a:index_t -> b:index_t -> r:rotval (Spec.wt al) ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.g1 al h0.[|wv|] (v a) (v b) r))

let g1 al wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: al:Spec.alg -> wv:vector_wp al -> a:index_t -> b:index_t -> x:word_t al ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.g2 al h0.[|wv|] (v a) (v b) x))

let g2 al wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a +. wv_b) +. x


val blake2_mixing : al:Spec.alg -> wv:vector_wp al -> a:index_t -> b:index_t -> c:index_t -> d:index_t -> x:word_t al -> y:word_t al ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_mixing al h0.[|wv|] (v a) (v b) (v c) (v d) x y))

let blake2_mixing al wv a b c d x y =
  let r0 = get_r al (size 0) in
  let r1 = get_r al (size 1) in
  let r2 = get_r al (size 2) in
  let r3 = get_r al (size 3) in
  g2 al wv a b x;
  g1 al wv d a r0;
  g2 al wv c d (Spec.nat_to_word al 0);
  g1 al wv b c r1;
  g2 al wv a b y;
  g1 al wv d a r2;
  g2 al wv c d (Spec.nat_to_word al 0);
  g1 al wv b c r3


val blake2_round1 : al:Spec.alg -> wv:vector_wp al -> m:block_wp al -> i:size_t{v i <= Spec.rounds al - 1} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_round1 al h0.[|wv|] h0.[|m|] (v i)))

[@ Substitute ]
let blake2_round1 al wv m i =
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
  blake2_mixing al wv (size 0) (size 4) (size 8) (size 12) m.(s0) m.(s1);
  blake2_mixing al wv (size 1) (size 5) (size 9) (size 13) m.(s2) m.(s3);
  blake2_mixing al wv (size 2) (size 6) (size 10) (size 14) m.(s4) m.(s5);
  blake2_mixing al wv (size 3) (size 7) (size 11) (size 15) m.(s6) m.(s7)


val blake2_round2 : al:Spec.alg -> wv:vector_wp al -> m:block_wp al -> i:size_t{v i <= Spec.rounds al - 1} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_round2 al h0.[|wv|] h0.[|m|] (v i)))

[@ Substitute ]
let blake2_round2 al wv m i =
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
  blake2_mixing al wv (size 0) (size 5) (size 10) (size 15) m.(s0) m.(s1);
  blake2_mixing al wv (size 1) (size 6) (size 11) (size 12) m.(s2) m.(s3);
  blake2_mixing al wv (size 2) (size 7) (size  8) (size 13) m.(s4) m.(s5);
  blake2_mixing al wv (size 3) (size 4) (size  9) (size 14) m.(s6) m.(s7)


val blake2_round: al:Spec.alg -> wv:vector_wp al -> m:block_wp al -> i:size_t{v i <= Spec.rounds al - 1} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                   /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_round al h0.[|m|] (v i) h0.[|wv|]))

let blake2_round al wv m i =
  blake2_round1 al wv m i;
  blake2_round2 al wv m i


val blake2_compress1:
    al:Spec.alg
  -> wv: vector_wp al
  -> s: hash_wp al
  -> m: block_wp al
  -> offset: Spec.limb_t al
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv
                     /\ disjoint wv s /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_compress1 al h0.[|wv|] h0.[|s|] h0.[|m|] offset flag))

[@ Substitute ]
let blake2_compress1 al wv s m offset flag =
  update_sub wv (size 0) (size 8) s;
  set_iv_sub al wv;
  [@inline_let]
  let low_offset = Spec.limb_to_word al offset in
  [@inline_let]
  let high_offset = Spec.limb_to_word al (offset >>. (size (bits (Spec.wt al)))) in
  let wv_12 = logxor wv.(size 12) low_offset in
  let wv_13 = logxor wv.(size 13) high_offset in
  let wv_14 = logxor wv.(size 14) (ones (Spec.wt al) SEC) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


#reset-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 1"

val blake2_compress2 :
  al:Spec.alg
  -> wv: vector_wp al
  -> m: block_wp al ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_compress2 al h0.[|wv|] h0.[|m|]))

[@ Substitute ]
let blake2_compress2 al wv m =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.blake2_round al h.[|m|] in
  loop1 h0 (rounds_t al) wv spec
  (fun i ->
    Loops.unfold_repeati (Spec.rounds al) (spec h0) h0.[|wv|] (v i);
    blake2_round al wv m i)


val blake2_compress3_inner :
  al:Spec.alg
  -> wv: vector_wp al
  -> i: size_t{v i < 8}
  -> s: hash_wp al ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                   /\ disjoint s wv /\ disjoint wv s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[|s|] == Spec.blake2_compress3_inner al h0.[|wv|] (v i) h0.[|s|]))

[@ Substitute ]
let blake2_compress3_inner al wv i s =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  let hi = logxor hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  al:Spec.alg
  -> wv: vector_wp al
  -> s: hash_wp al ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                     /\ disjoint wv s /\ disjoint s wv))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[|s|] == Spec.blake2_compress3 al h0.[|wv|] h0.[|s|]))

[@ Substitute ]
let blake2_compress3 al wv s =
  [@inline_let]
  let spec h = Spec.blake2_compress3_inner al h.[|wv|] in
  let h0 = ST.get () in
  loop1 h0 (size 8) s
    (fun h -> spec h)
    (fun i ->
      Loops.unfold_repeati 8 (spec h0) (as_seq h0 s) (v i);
      blake2_compress3_inner al wv i s)


val blake2_compress :
  al:Spec.alg
  -> s: hash_wp al
  -> m: block_wp al
  -> offset: Spec.limb_t al
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m
                     /\ disjoint s m /\ disjoint m s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[|s|] == Spec.blake2_compress al h0.[|s|] h0.[|m|] offset flag))

let blake2_compress al s m offset flag =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = live h1 s /\ h1.[|s|] == Spec.blake2_compress al h0.[|s|] h0.[|m|] offset flag in
  salloc1 h0 (size 16) (Spec.nat_to_word al 0) (Ghost.hide (loc s)) spec
  (fun wv ->
    blake2_compress1 al wv s m offset flag;
    blake2_compress2 al wv m;
    blake2_compress3 al wv s)


val blake2_update_block:
    al:Spec.alg
  -> hash: hash_wp al
  -> flag: bool
  -> totlen: Spec.limb_t al{uint_v totlen <= Spec.Blake2.max_limb al}
  -> d: block_p al ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.blake2_update_block al flag (v totlen) h0.[|d|] h0.[|hash|]))

let blake2_update_block al hash flag totlen d =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = live h1 hash /\ h1.[|hash|] == Spec.blake2_update_block al flag (uint_v totlen) h0.[|d|] h0.[|hash|] in
  salloc1 h0 (size 16) (Spec.nat_to_word al 0) (Ghost.hide (loc hash)) spec
  (fun block_w ->
     uints_from_bytes_le block_w d;
     let offset = totlen in
     blake2_compress al hash block_w offset flag)



val blake2_init_hash:
    al:Spec.alg
  -> hash: hash_wp al
  -> kk: size_t{v kk <= Spec.max_key al}
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
     (requires (fun h -> live h hash))
     (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                          /\ h1.[|hash|] == Spec.blake2_init_hash al (v kk) (v nn)))
[@ Substitute]
let blake2_init_hash al hash kk nn =
  set_iv al hash;
  let s0 = hash.(size 0) in
  let kk_shift_8 = shift_left (size_to_word al kk) (size 8) in
  let s0' = s0 ^. (Spec.nat_to_word al 0x01010000) ^. kk_shift_8 ^. (size_to_word al nn) in
  hash.(size 0) <- s0'


val blake2_init_branching:
    al:Spec.alg
  -> hash: hash_wp al
  -> key_block: lbuffer uint8 (size_block al)
  -> kk: size_t{v kk <= Spec.max_key al}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h k /\ live h key_block
                   /\ disjoint hash k /\ disjoint hash key_block /\ disjoint key_block k))
    (ensures  (fun h0 _ h1 -> modifies2 hash key_block h0 h1
                    /\ (if (v kk) = 0 then h1.[|hash|] == h0.[|hash|] else
                       let key_block1: Spec.block_s al = Seq.update_sub h0.[|key_block|] 0 (v kk) h0.[|k|] in
                       h1.[|hash|] == Spec.blake2_update_block al false (Spec.size_block al) key_block1 h0.[|hash|])))

[@ Substitute ]
let blake2_init_branching al hash key_block kk k nn =
  let h0 = ST.get () in
  if kk <>. (size 0) then
  begin
    update_sub key_block (size 0) kk k;
    assert(uint_v (secret (size_block al)) <= Spec.max_limb al);
    let totlenw = size_to_word al (size_block al) in
    [@inline_let]
    let totlen = Spec.word_to_limb al totlenw in
    blake2_update_block al hash false totlen key_block
  end


val blake2_init:
    al:Spec.alg
  -> hash: hash_wp al
  -> kk: size_t{v kk <= Spec.max_key al}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.Blake2.blake2_init al (v kk) h0.[|k|] (v nn)))

[@ Substitute ]
let blake2_init al hash kk k nn =
  let h0 = ST.get () in
  salloc1 h0 (size_block al) (u8 0) (Ghost.hide (loc hash))
  (fun _ h1 -> live h1 hash /\ h1.[|hash|] == Spec.blake2_init al (v kk) h0.[|k|] (v nn))
  (fun key_block ->
    blake2_init_hash al hash kk nn;
    blake2_init_branching al hash key_block kk k nn)


val blake2_update_last:
    al:Spec.alg
  -> hash: hash_wp al
  -> prev: Spec.limb_t al
  -> len: size_t{v len <= Spec.size_block al /\ v prev + v len <= Spec.Blake2.max_limb al}
  -> last: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.Blake2.blake2_update_last al (uint_v prev) (v len) h0.[|last|] h0.[|hash|]))

let blake2_update_last al hash prev rem last =
  let h0 = ST.get () in
  salloc1 h0 (size_block al) (u8 0) (Ghost.hide (loc hash))
  (fun _ h1 -> live h1 hash /\ h1.[|hash|] == Spec.Blake2.blake2_update_last al (v prev) (v rem) h0.[|last|] h0.[|hash|])
  (fun last_block ->
    update_sub last_block (size 0) rem last;
    let totlen: Spec.limb_t al = prev +! (size_to_limb al rem) in
    blake2_update_block al hash true totlen last_block)


val blake2_finish:
    al:Spec.alg
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al}
  -> output: lbuffer uint8 nn
  -> hash: hash_wp al ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output /\ disjoint output hash /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[|output|] == Spec.Blake2.blake2_finish al h0.[|hash|] (v nn)))

let blake2_finish al nn output hash =
  let h0 = ST.get () in
  salloc1 h0 (size (Spec.max_output al)) (u8 0) (Ghost.hide (loc output))
  (fun _ h1 -> live h1 output /\ h1.[|output|] == Spec.Blake2.blake2_finish al h0.[|hash|] (v nn))
  (fun full ->
    uints_to_bytes_le (size 8) full hash;
    let final = sub full (size 0) nn in
    copy output final)



let spec_update_block
    (al:Spec.alg)
    (init:nat)
    (d:Lib.ByteSequence.bytes{Seq.length d <= max_size_t
                             /\ init + Seq.length d <= max_size_t})
    (i:nat{init + Seq.length d <= Spec.max_limb al /\ i < Seq.length d / v (size_block al)}) =
    let block = Seq.sub #uint8 #(Seq.length d) d (i * v (size_block al)) (v (size_block al)) in
    Spec.blake2_update_block al false (init + ((i + 1) * v (size_block al))) block


val blake2_update_block_multi_single:
    al:Spec.alg
  -> hash: hash_wp al
  -> prev: Spec.limb_t al
  -> n: size_t{v prev + v n * v (size_block al) <= Spec.max_limb al /\ v prev + v n * v (size_block al) <= max_size_t}
  -> i: size_t{v i < v n}
  -> blocks: lbuffer uint8 (n *! size_block al){v n * v (size_block al) = length blocks} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h blocks /\ disjoint hash blocks))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                           /\ h1.[|hash|] == spec_update_block al (v prev) h0.[|blocks|] (v i) h0.[|hash|]))

let blake2_update_block_multi_single al hash prev n i blocks =
  let curlen:size_t = (i +! 1ul) *! (size_block al) in
  let curlen:Spec.limb_t al = size_to_limb al curlen in
  let totlen:Spec.limb_t al = prev +! curlen in
  let block:block_p al = sub blocks (i *! (size_block al)) (size_block al) in
  blake2_update_block al hash false totlen block


val spec_blake2_update_block_multi:
    al:Spec.alg
  -> prev:nat
  -> n:nat
  -> blocks:Lib.ByteSequence.bytes{n * v (size_block al) == Seq.length blocks /\ prev + n * (Spec.size_block al) <= Spec.max_limb al /\ prev + Seq.length blocks <= max_size_t}
  -> s:Spec.hash_ws al ->
  Tot (Spec.hash_ws al)

let spec_blake2_update_block_multi al prev n blocks s =
  repeati n (spec_update_block al prev blocks) s


val lemma_eq_block_multi:
    al:Spec.alg
  -> prev:nat
  -> n:nat
  -> blocks:Lib.ByteSequence.bytes{n * v (size_block al) == Seq.length blocks /\ prev + n * (Spec.size_block al) <= Spec.max_limb al}// /\ prev + Seq.length blocks <= max_size_t}
  -> hash:Spec.hash_ws al ->
  Lemma (spec_blake2_update_block_multi al prev n blocks hash
        == Spec.blake2_update_block_multi al prev n blocks hash)

let lemma_eq_block_multi al prev n blocks hash =
  let a = spec_blake2_update_block_multi al prev n blocks hash in
  let b = Spec.blake2_update_block_multi al prev n blocks hash in
  admit();
  Seq.eq_intro a b


val blake2_update_block_multi:
    al:Spec.alg
  -> hash: hash_wp al
  -> flag: bool
  -> prev: Spec.limb_t al
  -> n: size_t{v prev + v n * v (size_block al) <= Spec.max_limb al /\ v prev + v n * v (size_block al) <= max_size_t}
  -> blocks: lbuffer uint8 (n *! (size_block al)){v n * v (size_block al) = length blocks} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h blocks /\ disjoint hash blocks))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                        /\ h1.[|hash|] == Spec.blake2_update_block_multi al (v prev) (v n) h0.[|blocks|] h0.[|hash|]))

let blake2_update_block_multi al hash flag prev n blocks =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = spec_update_block al (v prev) h.[|blocks|] in
  loop1 h0 n hash spec
  (fun i ->
    Loops.unfold_repeati (v n) (spec h0) h0.[|hash|] (v i);
    blake2_update_block_multi_single al hash prev n i blocks);
  let h1 = ST.get() in
  lemma_eq_block_multi al (v prev) (v n) h0.[|blocks|] h0.[|hash|]



(* val spec_blake2: *)
(*     a:Spec.alg *)
(*   -> d:Lib.ByteSequence.bytes{Seq.length d <= max_size_t} *)
(*   -> kk:size_nat{kk <= Spec.max_key a /\ (if kk = 0 then Seq.length d <= Spec.max_limb a else Seq.length d + (Spec.size_block a) <= Spec.max_limb a)} *)
(*   -> k:Lib.ByteSequence.lbytes kk *)
(*   -> nn:size_nat{1 <= nn /\ nn <= Spec.max_output a} -> *)
(*   Tot (Lib.ByteSequence.lbytes nn) *)

(* let spec_blake2 a d kk k nn = *)
(*   let ll = Seq.length d in *)
(*   let n = ll / Spec.size_block a in *)
(*   let rem = ll % Spec.size_block a in *)
(*   let n,rem = if n <> 0 && rem = 0 then n - 1, Spec.size_block a else n, rem in *)
(*   let flag = if rem = 0 then true else false in *)
(*   let blocks = Seq.slice #uint8 #ll d 0 (n * (Spec.size_block a)) in *)
(*   let last = Seq.slice #uint8 #ll d (n * Spec.size_block a) ll in *)
(*   let kn = if kk = 0 then 0 else 1 in *)
(*   let prev_multi = kn * Spec.size_block a in *)
(*   let prev_last = (kn + n) * Spec.size_block a in *)
(*   let s: Spec.hash_ws a = Spec.blake2_init a kk k nn in *)
(*   let s: Spec.hash_ws a = Spec.blake2_update_block_multi a prev_multi n blocks s in *)
(*   let s: Spec.hash_ws a = Spec.blake2_update_last a prev_multi rem last s in *)
(*   Spec.blake2_finish a s nn *)


(* val compute_values: *)
(*     al:Spec.alg *)
(*   -> d:Lib.ByteSequence.bytes{Seq.length d <= max_size_t} *)
(*   -> kk:size_nat{kk <= Spec.max_key al /\ (if kk = 0 then Seq.length d <= Spec.max_limb al else Seq.length d + (Spec.size_block al) <= Spec.max_limb al)} *)
(*   -> k:Lib.ByteSequence.lbytes kk *)
(*   -> nn:size_nat{1 <= nn /\ nn <= Spec.max_output al} -> *)
(*   (\* Tot (size_nat & size_nat & bool & size_nat & size_nat & size_nat) *\) *)
(*   Pure (size_nat & size_nat & bool & size_nat & size_nat & size_nat) *)
(*   (requires ) *)
(*   (ensures  ) *)

(* let compute_values al d kk k nn = *)
(*   let ll = Seq.length d in *)
(*   let n = ll / Spec.size_block al in *)
(*   assert(n * Spec.size_block al <= max_size_t); *)
(*   assert((n + 1) * Spec.size_block al <= max_size_t); *)
(*   let rem = ll % Spec.size_block al in *)
(*   let n,rem = if n <> 0 && rem = 0 then n - 1, Spec.size_block al else n, rem in *)
(*   let flag = if rem = 0 then true else false in *)
(*   let kn = if kk = 0 then 0 else 1 in *)
(*   let prev_multi = kn * Spec.size_block al in *)
(*   let prev_last = (kn + n) * Spec.size_block al in *)
(*   assert(0 <= prev_last); *)
(*   assert(rem <= Spec.size_block al /\ prev_last + rem <= Spec.Blake2.max_limb al); *)
(*   assert((n + 1) * Spec.size_block al <= max_size_t); *)
(*   assert(prev_last <= max_size_t); *)
(*   n,rem,flag,kn,prev_multi,prev_last *)




val blake2:
    al:Spec.alg
  -> nn:size_t{1 <= v nn /\ v nn <= Spec.max_output al}
  -> output: lbuffer uint8 nn
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= Spec.max_key al /\ (if v kk = 0 then v ll < Spec.max_limb al else v ll + Spec.size_block al < Spec.max_limb al)}
  -> k: lbuffer uint8 kk ->
  Stack unit
    (requires (fun h -> live h output /\ live h d /\ live h k
                   /\ disjoint output d /\ disjoint output k))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[|output|] == Spec.Blake2.blake2 al h0.[|d|] (v kk) h0.[|k|] (v nn)))

let blake2 al nn output ll d kk k =
  let n = ll /. (size_block al) in
  let rem = ll %. (size_block al) in
  let n,rem = if n <>. 0ul && rem =. 0ul then n -! 1ul, size_block al else n, rem in
  let flag = if rem =. 0ul then true else false in
  let blocks = sub d 0ul (n *! (size_block al)) in
  let last = sub d (n *! (size_block al)) rem in
  let kn = if kk =. 0ul then 0ul else 1ul in
  let prev_multi: Spec.limb_t al = size_to_limb al (kn *! size_block al) in
  admit();
  let prev_last:Spec.limb_t al = size_to_limb al ((kn +! n) *! (size_block al)) in
  let h0 = ST.get () in
  salloc1 h0 (size 8) (Spec.nat_to_word al 0) (Ghost.hide (loc output))
  (fun _ h1 -> live h1 output /\ h1.[|output|] == Spec.Blake2.blake2b h0.[|d|] (v kk) h0.[|k|] (v nn))
  (fun hash ->
    blake2_init al hash kk k nn;
    blake2_update_block_multi al hash flag prev_multi n blocks;
    blake2_update_last al hash prev_last rem last;
    blake2_finish al nn output hash)
