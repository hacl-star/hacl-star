module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas

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

val blake2_compress : s:hash_state -> b:message_block -> wv:working_vector -> offset:uint64 -> f:Spec.last_block_flag ->
  Stack unit
    (requires (fun h -> live h s /\ live h b /\ live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ as_lseq s h1 == Spec.blake2_compress (as_lseq s h0) (as_lseq b h0) offset f))

let blake2_compress s (* = h *) m wv offset f =
  let iv = createL Spec.init_list in
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

// val blake2s_internal : dd:size_nat{0 < dd /\ dd * bytes_in_block <= max_size_t}  -> d:lbytes (dd * bytes_in_block) -> ll:size_nat -> kk:size_nat{kk<=32} -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)

// let blake2s_internal dd d ll kk nn =
//   let h = init_vector in
//   let h = h.[0] <- h.[0] ^. (u32 0x01010000) ^. ((u32 kk) <<. (u32 8)) ^. (u32 nn) in
//   let h =
//     if dd > 1 then
//       repeati (dd -1) (fun i h ->
// 	     let to_compress : intseq U32 16 =
// 	     uints_from_bytes_le (sub d (i*bytes_in_block) bytes_in_block) in
// 	     blake2_compress h to_compress (u64 ((i+1)*block_bytes)) false
//       ) h else h
//   in
//   let offset : size_nat = (dd-1)*16*4 in
//   let last_block : intseq U32 16 = uints_from_bytes_le (sub d offset bytes_in_block) in
//   let h =
//     if kk = 0 then
//       blake2_compress h last_block (u64  ll) true
//     else
//       blake2_compress h last_block (u64 (ll + block_bytes)) true
//   in
//   sub (uints_to_bytes_le h) 0 nn

// val blake2s : ll:size_nat{0 < ll /\ ll <= max_size_t - 2 * bytes_in_block } ->  d:lbytes ll ->  kk:size_nat{kk<=32} -> k:lbytes kk -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)

// let blake2s ll d kk k nn =
//   let data_blocks : size_nat = ((ll - 1) / bytes_in_block) + 1 in
//   let padded_data_length : size_nat = data_blocks * bytes_in_block in
//   let padded_data = create padded_data_length (u8 0) in
//   let padded_data : lbytes (data_blocks * bytes_in_block) = update_slice padded_data 0 ll d in
//   if kk = 0 then
//     blake2s_internal data_blocks padded_data ll kk nn
//   else
//     let padded_key = create bytes_in_block (u8 0) in
//     let padded_key = update_slice padded_key 0 kk k in
//     let data_length : size_nat = bytes_in_block + padded_data_length in
//     let data = create data_length (u8 0) in
//     let data = update_slice data 0 bytes_in_block padded_key in
//     let data = update_slice data bytes_in_block data_length padded_data in
//     blake2s_internal (data_blocks+1) data ll kk nn
