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

inline_for_extraction
let v = size_v
inline_for_extraction
let index (x:size_nat) = size x

let op_String_Access m b = as_lseq b m

(* Constants *)

// inline_for_extraction
// let normalized_sigma : list size_t =
//   normalize_term (List.Tot.map Spec.Blake2s.size_sigma_list Spec.sigma_list)

(* Lemmas *)
let lemma_size_v_of_size_equal (s:size_nat) : Lemma (requires True)
  (ensures (size_v (size s) == s))
  [SMTPat (size s)] = ()

let lemma_sigma_equal (s0:list size_t) (s1:list size_nat) : Lemma (requires True)
  (ensures (List.Tot.map size_v s0 == s1)) = admit()


val update_sub: #a:Type -> #len:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len} -> x:lbuffer a (v n) ->
  Stack unit
    (requires (fun h -> live h i /\ live h x))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 i h0 h1
                         /\ h1.[i] == Spec.Lib.IntSeq.update_sub #a #len h0.[i] (v start) (v n) h0.[x]))
let update_sub #a #len i start n x =
  let i' = sub i start n in
  copy n x i'


(* Define algorithm parameters *)
type init_vector = lbuffer uint32 8
type working_vector = lbuffer uint32 16
type message_block = lbuffer uint32 16
type hash_state = lbuffer uint32 8
type idx = n:size_t{size_v n < 16}


let g1 (wv:working_vector) (a:idx) (b:idx) (r:rotval U32) :
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 h0.[wv] (v a) (v b) r)) =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r

let g2 (wv:working_vector) (a:idx) (b:idx) (x:uint32) :
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 h0.[wv] (v a) (v b) x)) =
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


#set-options "--max_fuel 0 --z3rlimit 50"

val blake2_round1 : wv:working_vector -> m:message_block -> i:size_t -> sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round1 h0.[wv] h0.[m] (v i)))

let blake2_round1 wv m i sigma =
  let h0 = ST.get () in
  let i_mod_10 = size_mod i (size 10) in
  let start_idx = mul_mod #SIZE i_mod_10 (size 16) in
  let s = sub #(n:size_t{v n < 16}) #160 #16 sigma start_idx (size 16) in
  let h1 = ST.get () in
  assert(
    let s' : lseq (n:size_nat{n < 16}) 16 = Spec.Lib.IntSeq.sub Spec.Blake2s.sigma_list (v start_idx) 16 in
    h1.[s] == s'
  );
  assume(live h1 s);
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(s.(size 0))) (m.(s.(size 1)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(s.(size 2))) (m.(s.(size 3)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(s.(size 4))) (m.(s.(size 5)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(s.(size 6))) (m.(s.(size 7)));
  admit()


val blake2_round2 : wv:working_vector -> m:message_block -> i:size_t -> sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 h0.[wv] h0.[m] (v i)))

let blake2_round2 wv m i sigma =
  let i_mod_10 = size_mod i (size 10) in
  let start_idx = mul_mod #SIZE i_mod_10 (size 16) in
  let s = sub #(n:size_t{v n < 16}) #160 #16 sigma start_idx (size 16) in
  let h = ST.get () in
  assume(live h s);
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(s.(size 8))) (m.(s.(size 9)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(s.(size 10))) (m.(s.(size 11)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(s.(size 12))) (m.(s.(size 13)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(s.(size 14))) (m.(s.(size 15)))


val blake2_round : wv:working_vector -> m:message_block -> i:size_t -> sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round h0.[wv] h0.[m] (v i)))

let blake2_round wv m i sigma =
  blake2_round1 wv m i sigma;
  blake2_round2 wv m i sigma


val blake2_compress1 : wv:working_vector ->
  s:hash_state -> m:message_block ->
  offset:uint64 -> flag:Spec.last_block_flag -> const_iv:lbuffer uint32 8 ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_compress1 h0.[wv] h0.[s] h0.[m] offset flag))

let blake2_compress1 wv s m offset flag const_iv =
  // lemma_size_v_of_size_equal 8;
  let type_s = size_v (size 8) in
  let type_iv = size_v (size 8) in
  let s : lbuffer uint32 type_s = s in
  let const_iv : lbuffer uint32 type_s = const_iv in
  update_sub wv (size 0) (size 8) s;
  update_sub wv (size 8) (size 8) const_iv;
  // let wv_1 = sub wv (size 0) (size 8) in
  // let wv_2 = sub wv (size 8) (size 16) in admit();
  // copy (size 8) s wv_1;
  // copy (size 8) const_iv wv_2;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 Spec.word_size) in
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
  (if flag then wv.(size 14) <- wv_14)


val blake2_compress2 :
  wv:working_vector -> s:hash_state -> m:message_block -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies2 s wv h0 h1
                         /\ h1.[s] == Spec.blake2_compress2 h0.[wv] h0.[s] h0.[m]))

let blake2_compress2 wv s m const_sigma =
  iteri (size Spec.rounds_in_f)
    (fun i wv -> admit(); wv)
    (fun i wv -> blake2_round wv m i const_sigma) wv;
    iteri (size 8)
    (fun i h -> h)
    (fun i h ->
      let i_plus_8 = add #SIZE i (size 8) in
      let hi_xor_wvi = logxor #U32 h.(i) wv.(i) in
      let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
      s.(i) <- hi
    ) s

val blake2_compress :
  s:hash_state -> m:message_block ->
  offset:uint64 -> f:Spec.last_block_flag -> const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
  Stack unit
    (requires (fun h -> live h s /\ live h m))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress h0.[s] h0.[m] offset f))

let blake2_compress s m offset flag const_iv const_sigma =
  alloc #uint32 #unit #16 (size 16) (u32 0) [BufItem m] [BufItem s]
  (fun h0 _ h1 -> True)
  (fun wv ->
  blake2_compress1 wv s m offset flag const_iv;
  blake2_compress2 wv s m const_sigma)

 val blake2s_internal:
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   ll:size_t -> kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
   to_compress:lbuffer uint32 16 -> wv:working_vector -> tmp:lbuffer uint8 32 -> res:lbuffer uint8 (size_v nn) ->
   const_iv:lbuffer uint32 8 -> const_sigma:lbuffer (n:size_t{size_v n < 16}) 160 ->
   Stack unit
     (requires (fun h -> live h d /\ live h to_compress /\ live h res /\ live h wv))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

 let blake2s_internal dd d ll kk nn to_compress wv tmp res const_iv const_sigma =
  push_frame ();
  assert_norm (List.Tot.length Spec.init_list = 8);
  let h : lbuffer uint32 8 = createL Spec.init_list in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  h.(size 0) <- h.(size 0) ^. (u32 0x01010000) ^. (kk_shift_8) ^. size_to_uint32 nn;

  (if (dd >. size 1) then
    let idx = size_decr dd in
    iteri idx
    (fun i h -> h)
    (fun i h ->
      uint32s_from_bytes_le (size 16) to_compress (sub d (mul #SIZE i (size Spec.bytes_in_block)) (size Spec.bytes_in_block));
      blake2_compress h to_compress (to_u64 #U32 (size_to_uint32 (mul #SIZE (size_incr i) (size Spec.block_bytes)))) false const_iv const_sigma//FIXME: i should have the u64 type
    ) h);
   let offset:size_t = mul #SIZE (size_decr dd) (size 64) in
   uint32s_from_bytes_le (size 16) to_compress (sub d offset (size Spec.bytes_in_block));
   (if kk =. size 0 then
      blake2_compress h to_compress (to_u64 #U32 (size_to_uint32 ll)) true const_iv const_sigma
   else
      blake2_compress h to_compress (to_u64 #U32 (size_to_uint32 (add #SIZE ll (size Spec.block_bytes)))) true const_iv const_sigma);
  uint32s_to_bytes_le (size 8) tmp h;
  let tmp' = sub tmp (size 0) nn in
  copy nn tmp' res;
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
  let const_iv : lbuffer uint32 8 = createL Spec.init_list in
  let const_sigma : lbuffer (n:size_t{size_v n < 16}) 160 = createL Spec.sigma_list_size in
  alloc #uint8 #unit #(v len_st_u8) len_st_u8 (u8 0) [BufItem d; BufItem k] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun st_u8 ->
    alloc #uint32 #unit #(v len_st_u32) len_st_u32 (u32 0) [BufItem d; BufItem k] [BufItem st_u8; BufItem res]
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
