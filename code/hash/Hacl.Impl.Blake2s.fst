module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf.LoadStore

module ST = FStar.HyperStack.ST
module LSeq = Spec.Lib.IntSeq
module Spec = Spec.Blake2s


///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
let op_String_Access #a #len m b = as_lseq #a #len b m


(* Lemmas *)
// let lemma_size_v_of_size_equal (s:size_nat) : Lemma (requires True)
//   (ensures (size_v (size s) == s))
//   [SMTPat (size s)] = ()

val lemma_repeati: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> i:size_nat{i < n} -> Lemma
  (requires True)
  (ensures  (f i (repeati #a i f init) == repeati #a (i + 1) f init))
  [SMTPat (repeati #a (i + 1) f init)]

let lemma_repeati #a n f init i = admit()

val lemma_repeati_zero: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> Lemma
  (requires True)
  (ensures  (init == repeati #a 0 f init))
  [SMTPat (repeati #a 0 f init)]

let lemma_repeati_zero #a n f init = admit()

val lemma_size_to_uint32_equal_u32_of_v_of_size_t: x:size_t -> Lemma
  (requires True)
  (ensures (size_to_uint32 x == u32 (v x)))
  [SMTPat (u32 (v x))]
let lemma_size_to_uint32_equal_u32_of_v_of_size_t x = admit()


// val lemma_repeati_ghost_is_repeati: #a:Type -> n:size_nat -> (f:(i:size_nat{i < n}  -> a -> Tot a)) -> init:a -> Lemma
//   (requires (True))
//   (ensures  (repeati #a n f init == repeati_ghost #a n f init))
//   [SMTPat (repeati_ghost #a n f init)]
// let lemma_repeati_ghost_is_repeati #a n f init = admit()


(* Functions to add to the libraries *)
val update_sub: #a:Type0 -> #len:size_nat -> #olen:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == olen} -> o:lbuffer a olen ->
  Stack unit
    (requires (fun h -> live h i /\ live h o))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 i h0 h1
                         /\ h1.[i] == Spec.Lib.IntSeq.update_sub #a #len h0.[i] (v start) (v n) h0.[o]))

[@ Substitute]
let update_sub #a #len #olen i start n o =
  let i' = sub i start n in
  copy n o i'


///
/// Blake2s
///

(* Definition of constants *)
inline_for_extraction let create_const_iv () =
  assert_norm(List.Tot.length Spec.list_init = 8);
  createL Spec.list_init

inline_for_extraction let sigma_list_size =
  normalize_term(List.Tot.map size Spec.list_sigma)

inline_for_extraction let create_const_sigma () =
  assert_norm(List.Tot.length Spec.list_init = 160);
  createL sigma_list_size


(* Define algorithm parameters *)
type init_vector = lbuffer uint32 8
type working_vector = lbuffer uint32 16
type message_block = lbuffer uint32 16
type hash_state = lbuffer uint32 8
type idx = n:size_t{size_v n < 16}
type sigma_t = lbuffer (n:size_t{size_v n < 16}) 160


val g1: wv:working_vector -> a:idx -> b:idx -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 h0.[wv] (v a) (v b) r))
let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:idx -> b:idx -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 h0.[wv] (v a) (v b) x))
let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (add_mod #U32 wv_a wv_b) x


val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
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


#set-options "--max_fuel 0 --z3rlimit 10"

val blake2_round1 : wv:working_vector -> m:message_block -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ as_list h.[const_sigma] == sigma_list_size))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h0.[m] == h1.[m]
                         /\ as_list h1.[const_sigma] == sigma_list_size
                         /\ h1.[wv] == Spec.blake2_round1 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i const_sigma =
  let i_mod_10 = size_mod i (size 10) in
  let start_idx = mul_mod #SIZE i_mod_10 (size 16) in
  let s = sub #(n:size_t{v n < 16}) #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(s.(size 0))) (m.(s.(size 1)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(s.(size 2))) (m.(s.(size 3)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(s.(size 4))) (m.(s.(size 5)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(s.(size 6))) (m.(s.(size 7)))


val blake2_round2 : wv:working_vector -> m:message_block -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ as_list h.[const_sigma] == sigma_list_size))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h0.[m] == h1.[m]
                         /\ as_list h1.[const_sigma] == sigma_list_size
                         /\ h1.[wv] == Spec.blake2_round2 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i const_sigma =
  let i_mod_10 = size_mod i (size 10) in
  let start_idx = mul_mod #SIZE i_mod_10 (size 16) in
  let s = sub #(n:size_t{v n < 16}) #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(s.(size 8))) (m.(s.(size 9)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(s.(size 10))) (m.(s.(size 11)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(s.(size 12))) (m.(s.(size 13)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(s.(size 14))) (m.(s.(size 15)))


val blake2_round : wv:working_vector -> m:message_block -> i:size_t -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ as_list h.[const_sigma] == sigma_list_size))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ as_list h1.[const_sigma] == sigma_list_size
                         /\ h1.[wv] == Spec.blake2_round h0.[m] (v i) h0.[wv]))

[@ (CConst "const_sigma")]
let blake2_round wv m i const_sigma =
  blake2_round1 wv m i const_sigma;
  blake2_round2 wv m i const_sigma


val blake2_compress1 : wv:working_vector ->
  s:hash_state -> m:message_block ->
  offset:uint64 -> flag:Spec.last_block_flag -> const_iv:lbuffer uint32 8 ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv /\ live h const_iv
                     /\ h.[const_iv] == Spec.const_init
                     /\ disjoint wv s /\ disjoint wv m /\ disjoint wv const_iv
                     /\ disjoint s wv /\ disjoint m wv /\ disjoint const_iv wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_compress1 h0.[wv] h0.[s] h0.[m] offset flag))

[@ Substitute ]
let blake2_compress1 wv s m offset flag const_iv =
  update_sub wv (size 0) (size 8) s;
  update_sub wv (size 8) (size 8) const_iv;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 Spec.word_size) in
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


val blake2_compress2 :
  wv:working_vector -> m:message_block -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ as_list h.[const_sigma] == sigma_list_size
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 h0.[wv] h0.[m]))

[@ Substitute ]
let blake2_compress2 wv m const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size Spec.rounds_in_f) wv
    (fun h0 -> let m0 = h0.[m] in Spec.blake2_round m0)
    (fun i wv ->
      assume(live h0 wv /\ live h0 m /\ live h0 const_sigma
           /\ as_list h0.[const_sigma] == sigma_list_size
           /\ disjoint wv m /\ disjoint wv const_sigma
           /\ disjoint m wv /\ disjoint const_sigma wv);
      blake2_round wv m i const_sigma)


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:hash_state -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner h0.[wv] (v i) h0.[s]))

[@ Substitute ]
let blake2_compress3_inner wv i s const_sigma =
  let i_plus_8 = add #SIZE i (size 8) in
  let hi_xor_wvi = logxor #U32 s.(i) wv.(i) in
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi

#reset-options "--max_fuel 0 --z3rlimit 25"

val blake2_compress3 :
  wv:working_vector -> s:hash_state -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma
                     /\ as_list h.[const_sigma] == sigma_list_size
                     /\ disjoint wv s /\ disjoint wv const_sigma
                     /\ disjoint s wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 h0.[wv] h0.[s]))

[@ Substitute ]
let blake2_compress3 wv s const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size 8) s
    (fun h0 -> let wv0 = h0.[wv] in Spec.blake2_compress3_inner wv0)
    (fun i s ->
      assume(live h0 s /\ live h0 wv /\ live h0 const_sigma
           /\ as_list h0.[const_sigma] == sigma_list_size
           /\ disjoint wv s /\ disjoint wv const_sigma
           /\ disjoint s wv /\ disjoint const_sigma wv);
    blake2_compress3_inner wv i s const_sigma)


val blake2_compress :
  s:hash_state -> m:message_block ->
  offset:uint64 -> f:Spec.last_block_flag -> const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h const_iv /\ live h const_sigma
                         /\ as_list h.[const_sigma] == sigma_list_size
                         /\ h.[const_iv] == Spec.const_init
                         /\ disjoint s m /\ disjoint s const_sigma /\ disjoint s const_iv
                         /\ disjoint m s /\ disjoint const_sigma s /\ disjoint const_iv s))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress h0.[s] h0.[m] offset f))

[@ (CConst "const_iv") (CConst "const_sigma")]
let blake2_compress s m offset flag const_iv const_sigma =
  let h = ST.get () in
  assert(live h s /\ live h m /\ live h const_iv /\ live h const_sigma
        /\ as_list h.[const_sigma] == sigma_list_size
        /\ h.[const_iv] == Spec.const_init
        /\ disjoint s m /\ disjoint s const_sigma /\ disjoint s const_iv
        /\ disjoint m s /\ disjoint const_sigma s /\ disjoint const_iv s);
  assert(live_list h [BufItem m]);
  assert(live_list h [BufItem s]);
  let f h0 h1 = h1.[s] == Spec.Blake2s.blake2_compress h0.[s] h0.[m] offset flag in
  salloc #_ #_ #16 (size 16) (u32 0) [BufItem m] [BufItem s]
  (fun h0 _ h1 -> f h0 h1)
  (fun wv ->
    assume(false);
    admit();
    blake2_compress1 wv s m offset flag const_iv;
    blake2_compress2 wv m const_sigma;
    blake2_compress3 wv s const_sigma)


val blake2s_internal1: hbuf:lbuffer uint32 8 ->
    kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
    Stack unit
     (requires (fun h -> live h hbuf))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hbuf h0 h1
                          /\ h1.[hbuf] == Spec.Blake2s.blake2s_internal1 h0.[hbuf] (v kk) (v nn)))

[@ Substitute]
let blake2s_internal1 hbuf kk nn =
  let hbuf0 = hbuf.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  let hbuf0' = hbuf0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  hbuf.(size 0) <- hbuf0'


val blake2s_internal2_: hbuf:lbuffer uint32 8 ->
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   to_compress:lbuffer uint32 16 ->
   i:size_t{v i < v dd - 1} ->
   const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
   Stack unit
     (requires (fun h -> live h hbuf /\ live h d /\ live h to_compress
                    /\ disjoint hbuf d /\ disjoint hbuf to_compress /\ disjoint hbuf const_iv /\ disjoint hbuf const_sigma
                    /\ disjoint d hbuf /\ disjoint to_compress hbuf /\ disjoint const_iv hbuf /\ disjoint const_sigma hbuf))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hbuf h0 h1
                          /\ h1.[hbuf] == Spec.blake2s_internal2_ (v dd) h0.[d] (v i) h0.[hbuf]))

[@ Substitute]
let blake2s_internal2_ h dd d to_compress i const_iv const_sigma =
  uint32s_from_bytes_le (size 16) to_compress (sub d (mul #SIZE i (size Spec.bytes_in_block)) (size Spec.bytes_in_block));
  blake2_compress h to_compress (to_u64 #U32 (size_to_uint32 (mul #SIZE (size_incr i) (size Spec.block_bytes)))) false const_iv const_sigma//FIXME: i should have the u64 type


val blake2s_internal2: hbuf:lbuffer uint32 8 ->
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   to_compress:lbuffer uint32 16 ->
   const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
   Stack unit
     (requires (fun h -> live h hbuf /\ live h d /\ live h to_compress
                    /\ disjoint hbuf d /\ disjoint hbuf to_compress /\ disjoint hbuf const_iv /\ disjoint hbuf const_sigma
                    /\ disjoint d hbuf /\ disjoint to_compress hbuf /\ disjoint const_iv hbuf /\ disjoint const_sigma hbuf))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hbuf h0 h1
                          /\ h1.[hbuf] == Spec.blake2s_internal2 h0.[hbuf] (v dd) h0.[d]))

[@ Substitute]
let blake2s_internal2 h dd d to_compress const_iv const_sigma =
  if (dd >. size 1) then
    let idx = size_decr dd in
    iteri idx
    (fun i h -> h)
    (fun i h -> blake2s_internal2_ h dd d to_compress i const_iv const_sigma) h


val blake2s_internal3: hbuf:lbuffer uint32 8 ->
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   ll:size_t -> kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
   to_compress:lbuffer uint32 16 -> tmp:lbuffer uint8 32 -> res:lbuffer uint8 (size_v nn) ->
   const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
   Stack unit
     (requires (fun h -> live h d /\ live h to_compress /\ live h res))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

[@ Substitute]
let blake2s_internal3 h dd d ll kk nn to_compress tmp res const_iv const_sigma =
  let offset:size_t = mul #SIZE (size_decr dd) (size 64) in
  uint32s_from_bytes_le (size 16) to_compress (sub d offset (size Spec.bytes_in_block));
  (if kk =. size 0 then
    blake2_compress h to_compress (to_u64 #U32 (size_to_uint32 ll)) true const_iv const_sigma
  else
    blake2_compress h to_compress (to_u64 #U32 (size_to_uint32 (add #SIZE ll (size Spec.block_bytes)))) true const_iv const_sigma
  );
  uint32s_to_bytes_le (size 8) tmp h;
  let tmp' = sub tmp (size 0) nn in
  copy nn tmp' res;
  pop_frame ()


val blake2s_internal:
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   ll:size_t -> kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
   to_compress:lbuffer uint32 16 -> wv:working_vector -> tmp:lbuffer uint8 32 -> res:lbuffer uint8 (size_v nn) ->
   const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
   Stack unit
     (requires (fun h -> live h d /\ live h to_compress /\ live h res /\ live h wv))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

[@ (CConst "const_iv") (CConst "const_sigma")]
 let blake2s_internal dd d ll kk nn to_compress wv tmp res const_iv const_sigma =
  push_frame ();
  assert_norm (List.Tot.length Spec.list_init = 8);
  let h : lbuffer uint32 8 = createL Spec.list_init in
  blake2s_internal1 h kk nn;
  blake2s_internal2 h dd d to_compress const_iv const_sigma;
  blake2s_internal3 h dd d ll kk nn to_compress tmp res const_iv const_sigma;
  pop_frame ()


val blake2s :
  ll:size_t{0 < size_v ll /\ size_v ll <= max_size_t - 2 * Spec.bytes_in_block } ->
  d:lbuffer uint8 (size_v ll) -> kk:size_t{size_v kk <= 32} ->
  k:lbuffer uint8 (size_v kk) -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} -> res:lbuffer uint8 (size_v nn) ->
  Stack unit
    (requires (fun h -> live h d /\ live h k /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

let blake2s ll d kk k nn res =
  let data_blocks : size_t = size_incr ((size_decr ll) /. (size Spec.bytes_in_block)) in
  let padded_data_length : size_t = mul #SIZE data_blocks (size Spec.bytes_in_block) in
  let data_length : size_t = add #SIZE (size Spec.bytes_in_block) padded_data_length in
  let len_st_u8 = add #SIZE (size 32) (add #SIZE padded_data_length (add #SIZE (size Spec.bytes_in_block) data_length)) in
  let len_st_u32 = size 32 in
  let const_iv : lbuffer uint32 8 = create_const_iv () in
  let const_sigma : lbuffer (n:size_t{size_v n < 16}) 160 = create_const_sigma () in
  salloc #uint8 #unit #(v len_st_u8) len_st_u8 (u8 0) [BufItem d; BufItem k] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun st_u8 ->
    salloc #uint32 #unit #(v len_st_u32) len_st_u32 (u32 0) [BufItem d; BufItem k] [BufItem st_u8; BufItem res]
    (fun h0 _ h1 -> True)
    (fun st_u32 ->
      let tmp = sub st_u8 (size 0) (size 32) in
      let padded_data = sub #uint8 #(v len_st_u8) #(v padded_data_length) st_u8 (size 32) padded_data_length in
      let padded_key = sub #uint8 #(v len_st_u8) #(Spec.bytes_in_block) st_u8 (add #SIZE (size 32) padded_data_length) (size Spec.bytes_in_block) in
      let data = sub #uint8 #(v len_st_u8) #(v data_length) st_u8 (add #SIZE (size 32) (add #SIZE padded_data_length (size Spec.bytes_in_block))) data_length in

      let padded_data' = sub padded_data (size 0) ll in
      copy ll d padded_data';

      let to_compress = sub st_u32 (size 0) (size 16) in
      let wv = sub st_u32 (size 16) (size 16) in

      if (kk =. size 0) then
	     blake2s_internal data_blocks padded_data' ll kk nn to_compress wv tmp res const_iv const_sigma
      else begin
	     let padded_key' = sub padded_key (size 0) kk in
	     copy kk k padded_key';

	     let data' = sub data (size 0) (size Spec.bytes_in_block) in
	     copy (size Spec.bytes_in_block) padded_key data';

	     let data' = sub data (size Spec.bytes_in_block) padded_data_length in
        copy padded_data_length padded_data data';
	     blake2s_internal (size_incr data_blocks) data' ll kk nn to_compress wv tmp res const_iv const_sigma
      end
    )
  )
