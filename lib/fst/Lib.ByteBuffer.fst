module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

module Loops = Lib.LoopCombinators

friend Lib.ByteSequence

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

let uint_to_be #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, SEC -> 
    RawIntTypes.u16_from_UInt16 (C.Endianness.htobe16 (RawIntTypes.u16_to_UInt16 u))
  | U16, PUB -> C.Endianness.htobe16 u
  | U32, SEC -> C.Endianness.htobe32 u
  | U64,_ -> C.Endianness.htobe64 u

let uint_to_le #t #l u =
  match t with
  | U1 -> u
  | U8 -> u
  | U16 -> C.Endianness.htole16 u
  | U32 -> C.Endianness.htole32 u
  | U64 -> C.Endianness.htole64 u

let uint_from_be #t #l u =
  match t with
  | U1 -> u
  | U8 -> u
  | U16 -> C.Endianness.be16toh u
  | U32 -> C.Endianness.be32toh u
  | U64 -> C.Endianness.be64toh u

let uint_from_le #t #l u =
  match t with
  | U1 -> u
  | U8 -> u
  | U16 -> C.Endianness.le16toh u
  | U32 -> C.Endianness.le32toh u
  | U64 -> C.Endianness.le64toh u

/// BEGIN Constant-time buffer equality

inline_for_extraction noextract
val cmp_bytes: 
    #len1:size_t 
  -> #len2:size_t 
  -> b1:lbuffer uint8 len1 
  -> b2:lbuffer uint8 len2 
  -> len:size_t{v len <= v len1 /\ v len <= v len2} 
  -> res:lbuffer uint8 (size 1) ->
  Stack uint8
    (requires fun h -> 
      live h b1 /\ live h b2 /\ live h res /\ disjoint res b1 /\ disjoint res b2 /\
      v (bget h res 0) == 255)    
    (ensures fun h0 z h1 -> 
      modifies1 res h0 h1 /\
      (as_seq h0 (gsub b1 0ul len) == as_seq h0 (gsub b2 0ul len)  ==> v z == 255) /\
      (as_seq h0 (gsub b1 0ul len) =!= as_seq h0 (gsub b2 0ul len) ==> v z == 0))
let rec cmp_bytes #len1 #len2 b1 b2 len res =
  let a_spec i = uint8 in
  let refl h = bget h res 0 in
  let footprint i = loc res in
  let spec h = 
  let h0 = ST.get() in
  loop h0 len a_spec refl footprint
    (fun i ->
      Loops.unfold_repeat_gen len a_spec (spec h0) (refl h0 0);
      let z0 = res.(0ul) in
      res.(0ul) <- eq_mask b1.(i) b2.(i) &. z0
    )


(*
  UInt.logand_lemma_1 #8 255;
  UInt.logand_lemma_2 #8 255;
  UInt.logand_lemma_1 #8 0;
  UInt.logand_lemma_2 #8 0;
  let h0 = ST.get() in
  let inv h (i:nat{i <= v len}) =
    let z = bget h res 0 in
    modifies1 res h0 h /\
    (as_seq h0 (gsub b1 0ul (size i)) == as_seq h0 (gsub b2 0ul (size i))  ==> v z == 255) /\
    (as_seq h0 (gsub b1 0ul (size i)) =!= as_seq h0 (gsub b2 0ul (size i)) ==> v z == 0)
  in
  Loops.for 0ul len inv 
    (fun i ->
      let z0 = res.(0ul) in
      res.(0ul) <- eq_mask b1.(i) b2.(i) &. z0;
      let h = ST.get() in
      if v (bget h res 0) = 255 then
        begin
        let s1 = as_seq h0 (gsub b1 0ul (i +! 1ul)) in
        let s2 = as_seq h0 (gsub b2 0ul (i +! 1ul)) in
        FStar.Seq.lemma_split s1 (v i);
        FStar.Seq.lemma_split s2 (v i);       
        Seq.lemma_eq_intro s1 s2
        end
      else if v z0 = 0 then
        lemma_not_equal_slice (as_seq h0 b1) (as_seq h0 b2) 0 (v i) (v i + 1)
      else
        lemma_not_equal_last (as_seq h0 b1) (as_seq h0 b2) 0 (v i + 1));
  res.(0ul)

let lbytes_eq #len b1 b2 =
  push_frame();
  let res = create 1ul (u8 255) in
  let z = cmp_bytes b1 b2 len res in
  pop_frame();
  z = u8 255

/// END Constant-time buffer equality

#set-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 1"

val foo: l:secrecy_level -> b:Seq.seq UInt8.t ->
  Lemma (ensures (BS.nat_from_bytes_le #l b == Kremlin.Endianness.le_to_n b)) 
  (decreases (Seq.length b))
let rec foo l b = 
  if Seq.length b = 0 then () else foo l (Seq.tail b)

val bar: l:secrecy_level -> b:Seq.seq UInt8.t ->
  Lemma (ensures (BS.nat_from_bytes_be #l b == Kremlin.Endianness.be_to_n b)) 
  (decreases (Seq.length b))
let rec bar l b = 
  if Seq.length b = 0 then () else bar l (Seq.slice b 0 (Seq.length b - 1))

let uint_from_bytes_le #t #l i =
  let h0 = ST.get () in
  foo l (as_seq h0 i);
  match t with
  | U8 -> i.(0ul) 
  | U16 -> let u = C.load16_le i in cast #t #l U16 l u
  | U32 -> let u = C.load32_le i in cast #t #l U32 l u
  | U64 -> let u = C.load64_le i in cast #t #l U64 l u
  | U128 -> let u = C.load128_le i in cast #t #l U128 l u

let uint_from_bytes_be #t #l i =
  let h0 = ST.get () in
  bar l (as_seq h0 i);
  match t with
  | U8 -> i.(0ul)
  | U16 -> let u = C.load16_be i in cast #t #l U16 l u
  | U32 -> let u = C.load32_be i in cast #t #l U32 l u
  | U64 -> let u = C.load64_be i in cast #t #l U64 l u
  | U128 -> let u = C.load128_be i in cast #t #l U128 l u

let uint_to_bytes_le #t #l o i = 
  match t with
  | U8 -> o.(0ul) <- i
  | _ -> admit() 
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

let uint_to_bytes_be #t #l o i =
  match t with
  | U8 -> o.(0ul) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)

inline_for_extraction
val uints_from_bytes_le':
    #t:inttype{~(t == U1)}
  -> #l:secrecy_level
  -> #len:size_t{v len * numbytes t <= max_size_t}
  -> o:lbuffer (uint_t t l) len
  -> i:lbuffer (uint_t U8 l) (len *! size (numbytes t)) ->
  Stack unit
        (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
        (ensures  fun h0 _ h1 -> 
          modifies1 o h0 h1)
         // /\ as_seq h1 o == BS.uints_from_bytes_le #t #l #(v len) (as_seq h0 i))
let uints_from_bytes_le' #t #l #len o i =
  let h0 = ST.get() in
  [@ inline_let]
  let spec h : GTot (j:size_nat{j < v len} -> uint_t t l) =    
    let i0 = B.as_seq h0 i in
    fun j ->
    BS.uint_from_bytes_le (Sequence.sub i0 (j * numbytes t) (numbytes t)) 
  in
  let impl (j:size_t{v j < v len}) : Stack (uint_t t l)
          (requires fun h -> modifies1 (gsub o 0ul j) h0 h)
          (ensures  fun h r h' -> h == h' /\ r == spec h0 (v j)) 
  = 
    let h = ST.get() in
    let bj = B.sub #(uint_t U8 l) i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
    let r = uint_from_bytes_le bj in
//    assume (B.as_seq h bj = 
    assert (uint_v r == uint_v (BS.uint_from_bytes_le #t #l (B.as_seq h bj)));
    r
  in
  fill #(uint_t t l) h0 len o spec impl

(*
(*
let uints_from_bytes_le #t #l #len b =
  let l = create #(uint_t t l) len (nat_to_uint 0) in
  repeati len
    (fun i l -> l.[i] <- uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))) l
*)

inline_for_extraction
let uints_from_bytes_le #t #l #len o i =
  assume (l == PUB);
  let h0 = ST.get() in
  let open Lib.Sequence in
  [@ inline_let]
  let spec (h0:mem) : GTot (j:size_nat{j < v len} -> lseq (uint_t t l) (v len) ->
    lseq (uint_t t l) (v len))
    = 
    let s0 = as_seq h0 i in
    fun j s -> s.[j] <- (BS.uint_from_bytes_le (sub s0 (j * numbytes t) (numbytes t)))
  in
  let impl (j:size_t{v j < v len}) : Stack unit
     (requires loop1_inv h0 len (uint_t t l) len o spec (v j))
     (ensures  fun _ _ -> loop1_inv h0 len (uint_t t l) len o spec (v j + 1))
  =
    let b_i = B.sub #(uint_t U8 l) i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
    let u_i = uint_from_bytes_le b_i in
    o.(j) <- u_i; //upd #_ #len o j u_i 
    let h1 = ST.get() in
    assume (as_seq h1 o == LoopCombinators.repeati (v j + 1) (spec h0) (as_seq h0 o))
  in
  loop1 h0 len o spec impl;
  let h1 = ST.get() in  
  assert (loop1_inv h0 len (uint_t t l) len o spec (v len) h1);
  assume (as_seq h1 o == LoopCombinators.repeati (v len) (spec h0) (as_seq h0 o))
  
  admit()
  


  let inv (h1:mem) (j:nat{j <= v len}) = 
    modifies1 o h0 h1 /\
    Seq.slice (as_seq h1 o) 0 j == 
    BS.uints_from_bytes_le #t #l #j (Seq.slice (as_seq h0 i) 0 (j * numbytes t)) 
  in
  assert (Seq.slice (as_seq h0 o) 0 0 == Seq.empty);
  assert (inv h0 0);
  admit()
  
  
  let f' (j:size_t{0 <= v j /\ v j < v len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_le b_i in
      upd #_ #len o j u_i in
  Lib.Loops.for 0ul len inv f'

*)


inline_for_extraction
let uints_from_bytes_be #t #l #len o i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) = live h1 i /\ live h1 o in
  let f' (j:size_t{0 <= v j /\ v j < v len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_be b_i in
      upd #_ #len o j u_i in
  admit();
  Lib.Loops.for 0ul len inv f'

inline_for_extraction
let uints_to_bytes_le #t #l len o i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = live h1 i /\ live h1 o in
  let f' (j:size_t{0 <= v j /\ v j < v len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = i.(j) in
      let b_i = sub o (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_le b_i u_i in
  admit();
  Lib.Loops.for 0ul len inv f'

inline_for_extraction
let uints_to_bytes_be #t #l len o i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = live h1 i /\ live h1 o in
  let f' (j:size_t{0 <= v j /\ v j < v len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = i.(j) in
      let b_i = sub o (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_be b_i u_i in
  admit();
  Lib.Loops.for 0ul len inv f'
*)
