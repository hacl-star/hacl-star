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


#set-options "--max_fuel 0 --z3rlimit 25"

(* Define algorithm parameters *)
type init_vector = lbuffer uint32 8
type working_vector = lbuffer uint32 16
type message_block = lbuffer uint32 16
type hash_state = lbuffer uint32 8
type idx = n:size_t{size_v n < 16}


// val set_init_vector : vec:init_vector ->
//   Stack unit
//     (requires (fun h -> live h vec))
//     (ensures  (fun h0 _ h1 -> preserves_live h0 h1
//                          /\ modifies1 vec h0 h1
//                          /\ as_lseq vec h1 == Spec.init_vector))
// let set_init_vector vec =
//   vec.(size 0) <- Spec.init_vector.[0];
//   vec.(size 1) <- Spec.init_vector.[1];
//   vec.(size 2) <- Spec.init_vector.[2];
//   vec.(size 3) <- Spec.init_vector.[3];
//   vec.(size 4) <- Spec.init_vector.[4];
//   vec.(size 5) <- Spec.init_vector.[5];
//   vec.(size 6) <- Spec.init_vector.[6];
//   vec.(size 7) <- Spec.init_vector.[7];
//   admit()

// val set_sigma : vec:lbuffer (n:uint32{v n < 16}) 160  ->
//   Stack unit
//     (requires (fun h -> live h vec))
//     (ensures  (fun h0 _ h1 -> preserves_live h0 h1
//                          /\ modifies1 vec h0 h1
//                          /\ as_lseq vec h1 == Spec.sigma))
// let set_sigma vec =



let g1 (wv:working_vector) (a:idx) (b:idx) (r:rotval U32) :
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ as_lseq wv h1 == Spec.g1 (as_lseq wv h0) (size_v a) (size_v b) r)) =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r

let g2 (wv:working_vector) (a:idx) (b:idx) (x:uint32) :
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ as_lseq wv h1 == Spec.g2 (as_lseq wv h0) (size_v a) (size_v b) x)) =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- wv_a +. wv_b +. x

val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ as_lseq wv h1 == Spec.blake2_mixing (as_lseq wv h0) (size_v a) (size_v b) (size_v c) (size_v d) x y))

let blake2_mixing wv a b c d x y =
  g2 wv a b x;
  g1 wv d a Spec.r1;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r2;
  g2 wv a b y;
  g1 wv d a Spec.r3;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r4

val blake2_compress : 
  s:hash_state -> m:message_block -> wv:working_vector -> 
  offset:uint64 -> f:Spec.last_block_flag ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies2 s wv h0 h1
                         /\ as_lseq s h1 == Spec.blake2_compress (as_lseq s h0) (as_lseq m h0) offset f))

let blake2_compress s (* = h *) m wv offset f =
  assert_norm (List.Tot.length Spec.init_list = 8);
  let iv : lbuffer uint32 8 = createL Spec.init_list in
  assert_norm (List.Tot.length Spec.sigma_list = 160);
  let sigma : lbuffer (n:size_t{size_v n < 16}) 160 = createL (List.Tot.map size Spec.sigma_list) in
  let wv_1 = sub wv (size 0) (size 8) in
  let wv_2 = sub wv (size 8) (size 16) in
  copy (size 8) s wv_1;
  copy (size 8) iv wv_2;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 Spec.word_size) in
  let wv_12 = wv.(size 12) ^. low_offset in
  let wv_13 = wv.(size 13) ^. high_offset in
  let wv_14 = wv.(size 14) ^. (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
  if f then wv.(size 14) <- wv_14 else
  iteri (size Spec.rounds_in_f)
    (fun i wv -> admit(); wv)
    (fun i wv ->
      let s = sub #size_t #160 #16 sigma ((i %. size 10) *. size 16) (size 16) in
      blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(s.(size 0))) (m.(s.(size 1)));
      blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(s.(size 2))) (m.(s.(size 3)));
      blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(s.(size 4))) (m.(s.(size 5)));
      blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(s.(size 6))) (m.(s.(size 7)));
      blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(s.(size 8))) (m.(s.(size 9)));
      blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(s.(size 10))) (m.(s.(size 11)));
      blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(s.(size 12))) (m.(s.(size 13)));
      blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(s.(size 14))) (m.(s.(size 15)))
    ) wv;
    iteri (size 8)
    (fun i h -> h)
    (fun i h ->
      let hi = h.(i) ^. wv.(i) ^. wv.(i +. size 8) in
      s.(i) <- hi
    ) s

 val blake2s_internal:
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   ll:size_t -> kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
   to_compress:lbuffer uint32 16 -> wv:working_vector -> tmp:lbuffer uint8 32 -> res:lbuffer uint8 (size_v nn) ->
   Stack unit
     (requires (fun h -> live h d /\ live h to_compress /\ live h res /\ live h wv))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

 let blake2s_internal dd d ll kk nn to_compress wv tmp res =
  assert_norm (List.Tot.length Spec.init_list = 8);
  let h : lbuffer uint32 8 = createL Spec.init_list in
  h.(size 0) <- h.(size 0) ^. (u32 0x01010000) ^. (size_to_uint32 kk <<. (u32 8)) ^. size_to_uint32 nn;
  
  (if (dd >. size 1) then
    iteri (dd -. size 1)
    (fun i h -> h)
    (fun i h -> 
       uint32s_from_bytes_le (size 16) to_compress (sub d (i *. size Spec.bytes_in_block) (size Spec.bytes_in_block));
       blake2_compress h to_compress wv (to_u64 #U32 (size_to_uint32 ((size_incr i) *. size Spec.block_bytes))) false //FIXME: i should have the u64 type
    ) h);
   let offset:size_t = (size_decr dd) *. size 64 in
   uint32s_from_bytes_le (size 16) to_compress (sub d offset (size Spec.bytes_in_block));
   (if kk =. size 0 then
      blake2_compress h to_compress wv (to_u64 (size_to_uint32 ll)) true
   else
      blake2_compress h to_compress wv (to_u64 (size_to_uint32 (ll +. size Spec.block_bytes))) true);
  uint32s_to_bytes_le (size 8) tmp h;
  let tmp' = sub tmp (size 0) nn in
  copy nn tmp' res
   
val blake2s :
  ll:size_t{0 < size_v ll /\ size_v ll <= max_size_t - 2 * Spec.bytes_in_block } -> 
  d:lbuffer uint8 (size_v ll) -> kk:size_t{size_v kk <= 32} ->
  k:lbuffer uint8 (size_v kk) -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} -> res:lbuffer uint8 (size_v nn) ->
  Stack unit
    (requires (fun h -> live h d /\ live h k /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1))
   
let blake2s ll d kk k nn res =
  let data_blocks : size_t = size_incr ((size_decr ll) /. (size Spec.bytes_in_block)) in
  let padded_data_length : size_t = data_blocks *. (size Spec.bytes_in_block) in
  let data_length : size_t = size Spec.bytes_in_block +. padded_data_length in
  let len_st_u8 = size 32 +. padded_data_length +. (size Spec.bytes_in_block) +. data_length in
  let len_st_u32 = size 16 +. size 16 in

  alloc #uint8 #unit #(v len_st_u8) len_st_u8 (u8 0) [BufItem d; BufItem k] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun st_u8 ->
    alloc #uint32 #unit #(v len_st_u32) len_st_u32 (u32 0) [BufItem d; BufItem k] [BufItem st_u8; BufItem res]
    (fun h0 _ h1 -> True)
    (fun st_u32 ->
       let tmp = sub st_u8 (size 0) (size 32) in
       let padded_data = sub #uint8 #(v len_st_u8) #(v padded_data_length) st_u8 (size 32) padded_data_length in
       let padded_key = sub #uint8 #(v len_st_u8) #(Spec.bytes_in_block) st_u8 (size 32 +. padded_data_length) (size Spec.bytes_in_block) in
       let data = sub #uint8 #(v len_st_u8) #(v data_length) st_u8 (size 32 +. padded_data_length +. size Spec.bytes_in_block) data_length in

       let padded_date' = sub padded_data (size 0) ll in
       copy ll d padded_date';

       let to_compress = sub st_u32 (size 0) (size 16) in
       let wv = sub st_u32 (size 16) (size 16) in
       
       if (kk =. size 0) then 
	 blake2s_internal data_blocks d ll kk nn to_compress wv tmp res
       else begin
	 let padded_key' = sub padded_key (size 0) kk in
	 copy kk k padded_key';

	 let data' = sub data (size 0) (size Spec.bytes_in_block) in
	 copy (size Spec.bytes_in_block) padded_key data';

	 let data' = sub data (size Spec.bytes_in_block) padded_data_length in
	 copy padded_data_length padded_data data';
	 blake2s_internal (size_incr data_blocks) d ll kk nn to_compress wv tmp res
       end
    )
  )
