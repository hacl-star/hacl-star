module Hacl.Impl.Xor.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Seq
open FStar.Endianness
open Seq.Create
open Spec.Lib

let u32 = FStar.UInt32.t
let u8  = FStar.UInt8.t

#reset-options "--max_fuel 0 --z3rlimit 20"

private
val little_bytes_def_0: unit -> Lemma (little_bytes 0ul 0 == Seq.createEmpty)
private
val little_bytes_def_1: len:UInt32.t{0 < UInt32.v len} -> n:nat{n < pow2 (8*UInt32.v len)} ->
  Lemma (n / 256 < pow2 (8 * (UInt32.v len - 1)) /\
    little_bytes len n == 
         cons (UInt8.uint_to_t (n % 256)) (little_bytes FStar.UInt32.(len -^ 1ul) (n / 256)))

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"
let little_bytes_def_0 () = ()
let little_bytes_def_1 len n =
  let len = FStar.UInt32.(len -^ 1ul) in 
  let byte = UInt8.uint_to_t (n % 256) in
  assert_norm(pow2 8 = 256);
  let n' = n / 256 in 
  Math.Lemmas.pow2_plus 8 (8 * UInt32.v len);
  assert(n' < pow2 (8 * UInt32.v len ))

#reset-options "--max_fuel 0 --z3rlimit 20"

private
val lemma_uint32_to_le_def:
  x:u32 ->
  Lemma (
    let x0:nat = FStar.UInt32.(v (x &^ 0xfful)) in
    let x1:nat = FStar.UInt32.(v ((x >>^ 8ul) &^ 0xfful)) in
    let x2:nat = FStar.UInt32.(v ((x >>^ 16ul) &^ 0xfful)) in
    let x3:nat =  FStar.UInt32.(v ((x >>^ 24ul) &^ 0xfful)) in
    x0 < pow2 8 /\ x1 < pow2 8 /\ x2 < pow2 8 /\ x3 < pow2 8 /\
    (let x0 = UInt8.uint_to_t x0 in
     let x1 = UInt8.uint_to_t x1 in
     let x2 = UInt8.uint_to_t x2 in
     let x3 = UInt8.uint_to_t x3 in
    little_bytes 4ul (UInt32.v x) == create_4 x0 x1 x2 x3))
let lemma_uint32_to_le_def x =
  let open FStar.UInt32 in
  Math.Lemmas.division_multiplication_lemma (v x) (pow2 8) (pow2 8);
  Math.Lemmas.division_multiplication_lemma (v x) (pow2 16) (pow2 8);
  Math.Lemmas.division_multiplication_lemma (v x) (pow2 24) (pow2 8);
  Math.Lemmas.pow2_plus 8 8;
  Math.Lemmas.pow2_plus 16 8;
  Math.Lemmas.pow2_plus 24 8;
  little_bytes_def_1 4ul (v x);
  let tl = x >>^ 8ul in
  UInt.logand_mask (v x) 8;
  little_bytes_def_1 3ul (v tl);
  let tl' = tl >>^ 8ul in
  UInt.logand_mask (v tl) 8;
  little_bytes_def_1 2ul (v tl');
  let tl'' = tl' >>^ 8ul in
  UInt.logand_mask (v tl') 8;
  little_bytes_def_1 1ul (v tl'');
  let tl''' = tl'' >>^ 8ul in
  UInt.logand_mask (v tl'') 8;
  little_bytes_def_0 ();
  let x0 = UInt8.uint_to_t (v x % 256) in
  let x1 = UInt8.uint_to_t ((v x / 256) % 256) in
  let x2 = UInt8.uint_to_t ((v x / pow2 16) % 256) in
  let x3 = UInt8.uint_to_t ((v x / pow2 24) % 256) in
  lemma_eq_intro (little_bytes 4ul (v x)) (create_4 x0 x1 x2 x3)


private
val lemma_xor_vec1:
  x:u32 -> y:u32 -> s:u32{UInt32.v s <= 24} ->
  Lemma (
    let vx = UInt.to_vec (UInt32.v x) in
    let vy = UInt.to_vec (UInt32.v y) in
    let s  = UInt32.v s in
    FStar.BitVector.(slice (logxor_vec vx vy) s (s+8)
    == logxor_vec #8 (slice vx s (s+8)) (slice vy s (s+8))))
let lemma_xor_vec1 x y s =
  let s = UInt32.v s in
  let vx = UInt.to_vec (UInt32.v x) in
  let vy = UInt.to_vec (UInt32.v y) in
  let xorxy = BitVector.logxor_vec vx vy in
  let vx' = slice vx s (s+8) in
  let vy' = slice vy s (s+8) in
  let xorxy' = BitVector.logxor_vec #8 vx' vy' in
  lemma_eq_intro (slice xorxy s (s+8)) (xorxy')


private
val lemma_xor_vec2:
  x:u32 ->
  Lemma (
    let vx = UInt.to_vec (UInt32.v x) in
    let vx8 = UInt.to_vec (FStar.UInt32.(v (x >>^ 8ul) )) in
    let vx16 = UInt.to_vec (FStar.UInt32.(v (x >>^ 16ul) )) in
    let vx24 = UInt.to_vec (FStar.UInt32.(v (x >>^ 24ul) )) in
    slice vx8 24 32 == slice vx 16 24
    /\ slice vx16 24 32 == slice vx 8 16
    /\ slice vx24 24 32 == slice vx 0 8)
let lemma_xor_vec2 x =
  let vx = UInt.to_vec (UInt32.v x) in
  let vx8 = UInt.to_vec (FStar.UInt32.(v (x >>^ 8ul) )) in
  let vx16 = UInt.to_vec (FStar.UInt32.(v (x >>^ 16ul) )) in
  let vx24 = UInt.to_vec (FStar.UInt32.(v (x >>^ 24ul) )) in
  lemma_eq_intro (slice vx8 24 32) (slice vx 16 24);
  lemma_eq_intro (slice vx16 24 32) (slice vx 8 16);
  lemma_eq_intro (slice vx24 24 32) (slice vx 0 8)


private
val lemma_xor_vec3:
  unit -> Lemma (UInt.to_vec #32 0xff = append (BitVector.zero_vec #24) (BitVector.ones_vec #8))
let lemma_xor_vec3 () =
  UInt.ones_from_vec_lemma #8;
  assert(UInt.to_vec #8 0xff = BitVector.ones_vec #8);
  let ones8 = BitVector.ones_vec #8 in
  UInt.from_vec_lemma_1 #8 (UInt.to_vec #8 0xff) (BitVector.ones_vec #8);
  let z = append (BitVector.zero_vec #24) (BitVector.ones_vec #8) in
  lemma_eq_intro (slice z 24 32) (BitVector.ones_vec #8);
  UInt.from_vec_propriety #32 z 24;
  UInt.from_vec_lemma_1 #32 z (UInt.to_vec #32 0xff)


private
val lemma_xor_vec4: x:u32 -> 
  Lemma (slice (BitVector.logand_vec (UInt.to_vec #32 (UInt32.v x)) (UInt.to_vec #32 0xff)) 24 32
         == slice (UInt.to_vec #32 (UInt32.v x)) 24 32)
let lemma_xor_vec4 x =
  let x = UInt32.v x in
  lemma_xor_vec3 ();
  let vx = (UInt.to_vec #32 x) in
  let vones = (UInt.to_vec #32 0xff) in
  assert(forall (i:nat). (i >= 24 /\ i < 32) ==> index vones i = true);
  assert(forall (i:nat). (i >= 24 /\ i < 32) ==> index (BitVector.logand_vec vx vones) i = index vx i);
  lemma_eq_intro (slice (BitVector.logand_vec vx vones) 24 32) (slice vx 24 32)


private
val lemma_xor_vec5:
  x:u32 ->
  Lemma (
    let vx = UInt.to_vec FStar.UInt32.(v (x &^ 0xfful)) in
    let vx8 = UInt.to_vec FStar.UInt32.(v ((x >>^ 8ul) &^ 0xfful)) in
    let vx16 = UInt.to_vec FStar.UInt32.(v ((x >>^ 16ul) &^ 0xfful)) in
    let vx24 = UInt.to_vec FStar.UInt32.(v ((x >>^ 24ul) &^ 0xfful)) in
    slice (vx) 24 32 = slice (UInt.to_vec (UInt32.v x)) 24 32
    /\ slice (vx8) 24 32 = slice (UInt.to_vec (UInt32.v x)) 16 24
    /\ slice (vx16) 24 32 = slice (UInt.to_vec (UInt32.v x)) 8 16
    /\ slice (vx24) 24 32 = slice (UInt.to_vec (UInt32.v x)) 0 8)
let lemma_xor_vec5 x =
  let open FStar.UInt32 in
  let x = (x) in
  let x8 = ((x >>^ 8ul)) in
  let x16 = ((x >>^ 16ul)) in
  let x24 = ((x >>^ 24ul)) in
  let vx = UInt.to_vec FStar.UInt32.(v (x &^ 0xfful)) in
  let vx8 = UInt.to_vec FStar.UInt32.(v ((x >>^ 8ul) &^ 0xfful)) in
  let vx16 = UInt.to_vec FStar.UInt32.(v ((x >>^ 16ul) &^ 0xfful)) in
  let vx24 = UInt.to_vec FStar.UInt32.(v ((x >>^ 24ul) &^ 0xfful)) in
  lemma_xor_vec4 x;
  lemma_xor_vec4 x8;
  lemma_xor_vec4 x16;
  lemma_xor_vec4 x24;
  lemma_xor_vec2 x


private
val lemma_uint32_to_uint8_vec:
  x:u32 ->
  Lemma (let x' = (UInt.from_vec #8 (slice (UInt.to_vec (FStar.UInt32.(v (x &^ 0xfful)))) 24 32)) in
         let x'':nat = FStar.UInt32.(v (x &^ 0xfful)) in
         (x'' < pow2 8 /\ x'' = x'))
let lemma_uint32_to_uint8_vec x =
  assert_norm(pow2 8 = 256);
  UInt.logand_mask (UInt32.v x) 8;
  lemma_xor_vec4 x;
  UInt.slice_right_lemma #32 (UInt.to_vec (UInt32.v x)) 8


private
val lemma_uint32_to_le_def2:
  x:u32 ->
  Lemma (
    let x0 = slice (UInt.to_vec (FStar.UInt32.(v (x &^ 0xfful)))) 24 32 in
    let x1 = slice (UInt.to_vec FStar.UInt32.(v ((x >>^ 8ul) &^ 0xfful))) 24 32 in
    let x2 = slice (UInt.to_vec FStar.UInt32.(v ((x >>^ 16ul) &^ 0xfful))) 24 32 in
    let x3 = slice (UInt.to_vec FStar.UInt32.(v ((x >>^ 24ul) &^ 0xfful))) 24 32 in
    (let x0 = UInt8.uint_to_t (UInt.from_vec #8 x0) in
     let x1 = UInt8.uint_to_t (UInt.from_vec #8 x1) in
     let x2 = UInt8.uint_to_t (UInt.from_vec #8 x2) in
     let x3 = UInt8.uint_to_t (UInt.from_vec #8 x3) in
    little_bytes 4ul (UInt32.v x) == create_4 x0 x1 x2 x3))
let lemma_uint32_to_le_def2 x =
  let open FStar.UInt32 in
  lemma_uint32_to_le_def x;
  lemma_xor_vec2 x;
  lemma_xor_vec5 x;
  lemma_uint32_to_uint8_vec x;
  lemma_uint32_to_uint8_vec (x >>^ 8ul);
  lemma_uint32_to_uint8_vec (x >>^ 16ul);
  lemma_uint32_to_uint8_vec (x >>^ 24ul)


private
val lemma_xor_uint32_to_bytes:
  in1:u32 ->
  in2:u32 ->
  Lemma (let out1 = uint32_to_le in1 in
         let out2 = uint32_to_le in2 in
         map2 (fun x y -> FStar.UInt8.logxor x y) out1 out2 ==
         uint32_to_le (FStar.UInt32.logxor in1 in2))
let rec lemma_xor_uint32_to_bytes in1 in2 =
  lemma_uint32_to_le_def2 in1;
  lemma_uint32_to_le_def2 in2;
  let x = (FStar.UInt32.logxor in1 in2) in
  lemma_uint32_to_le_def2 x;
  lemma_xor_vec5 in1;
  lemma_xor_vec5 in2;
  lemma_xor_vec5 x;
  lemma_xor_vec1 in1 in2 0ul;
  lemma_xor_vec1 in1 in2 8ul;
  lemma_xor_vec1 in1 in2 16ul;
  lemma_xor_vec1 in1 in2 24ul;
  let l1 = little_bytes 4ul (UInt32.v in1) in
  let l2 = little_bytes 4ul (UInt32.v in2) in
  let lx = little_bytes 4ul (UInt32.v x) in
  cut (index lx 0 == FStar.UInt8.logxor (index l1 0) (index l2 0));
  cut (index lx 1 == FStar.UInt8.logxor (index l1 1) (index l2 1));
  cut (index lx 2 == FStar.UInt8.logxor (index l1 2) (index l2 2));
  cut (index lx 3 == FStar.UInt8.logxor (index l1 3) (index l2 3));
  lemma_eq_intro lx (map2 (fun x y -> FStar.UInt8.logxor x y) l1 l2)


#reset-options "--max_fuel 0 --z3rlimit 200"

private
val lemma_xor_uint32s_to_bytes_:
  in1:seq u32 ->
  in2:seq u32{length in1 = length in2} ->
  Lemma (requires (True))
        (ensures (
         let out1 = uint32s_to_le (length in1) in1 in
         let out2 = uint32s_to_le (length in1) in2 in
         map2 (fun x y -> FStar.UInt8.logxor x y) out1 out2 ==
         uint32s_to_le (length in1) (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2)))
         (decreases (length in1))
let rec lemma_xor_uint32s_to_bytes_ in1 in2 =
  if length in1 = 0 then (
    let out1 = uint32s_to_le (length in1) in1 in
    let out2 = uint32s_to_le (length in1) in2 in
    lemma_uint32s_to_le_def_0 0 in1;
    lemma_uint32s_to_le_def_0 0 in2;
    lemma_uint32s_to_le_def_0 0 (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2);
    lemma_eq_intro (map2 (fun x y -> FStar.UInt8.logxor x y) out1 out2)
                   (uint32s_to_le (length in1) (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2))
    )
  else (
    let len = length in1 in
    lemma_uint32s_to_le_def_1 (length in1) in1;
    lemma_uint32s_to_le_def_1 (length in1) in2;
    lemma_uint32s_to_le_def_1 (length in1) (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2);
    let h1 = index in1 (len-1) in
    let h2 = index in2 (len-1) in
    lemma_xor_uint32_to_bytes h1 h2;
    let t1 = slice in1 0 (length in1 - 1) in
    let t2 = slice in2 0 (length in2 - 1) in
    lemma_xor_uint32s_to_bytes_ t1 t2;
    let out1 = uint32s_to_le (length in1) in1 in
    let out2 = uint32s_to_le (length in2) in2 in
    let f = (fun x y -> FStar.UInt8.logxor x y) in
    lemma_eq_intro (map2 f out1 out2) 
                    (append (map2 f (uint32s_to_le (length t1) t1) (uint32s_to_le (length t1) t2))
                            (map2 f (uint32_to_le h1) (uint32_to_le h2)));
    lemma_eq_intro (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2)
                   (snoc (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2) (FStar.UInt32.logxor h1 h2));
    lemma_eq_intro (slice ((snoc (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2) (FStar.UInt32.logxor h1 h2))) 0 (length in1 - 1)) (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2);
    lemma_eq_intro (uint32s_to_le (length in1) (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2))
                   (uint32s_to_le (length in1) (snoc (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2) (FStar.UInt32.logxor h1 h2)));
    cut (index (snoc (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2) (FStar.UInt32.logxor h1 h2)) (len-1)
       == FStar.UInt32.logxor h1 h2);
    lemma_eq_intro (append (uint32s_to_le (length t1) ((map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2))) (uint32_to_le (FStar.UInt32.logxor h1 h2)))
                   (uint32s_to_le (length in1) (snoc (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2) (FStar.UInt32.logxor h1 h2)));
    lemma_eq_intro (map2 (fun x y -> FStar.UInt8.logxor x y) (uint32s_to_le (length t1) t1)
                                                           (uint32s_to_le (length t1) t2))
                   (uint32s_to_le (length t1) (map2 (fun x y -> FStar.UInt32.logxor x y) t1 t2));
    lemma_eq_intro (map2 (fun x y -> FStar.UInt8.logxor x y) out1 out2)
                   (uint32s_to_le (length in1) (map2 (fun x y -> FStar.UInt32.logxor x y) in1 in2))
    )


val lemma_xor_uint32s_to_bytes:
  in1:seq FStar.UInt8.t ->
  in2:seq u32{length in1 = 4 * length in2} ->
  Lemma (requires (True))
        (ensures (
         let out2 = uint32s_to_le (length in2) in2 in
         map2 (fun x y -> FStar.UInt8.logxor x y) in1 out2 ==
         uint32s_to_le (length in2) (map2 (fun x y -> FStar.UInt32.logxor x y) (uint32s_from_le (length in2) in1) in2)))
         (decreases (length in2))
let lemma_xor_uint32s_to_bytes in1 in2 =
  let in1' = uint32s_from_le (length in2) in1 in
  lemma_xor_uint32s_to_bytes_ in1' in2;
  lemma_uint32s_from_le_bij (length in2) in1
