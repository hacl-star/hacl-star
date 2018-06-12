module Hacl.Impl.Chacha20.Vec128.State

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Chacha20_vec
open C.Loops

module Spec = Spec.Chacha20
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

open Hacl.UInt32x4


#reset-options "--max_fuel 0 --z3rlimit 100"

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer vec{length b = 4}
let blocks = U32.(vec_size /^ 4ul)
let vecsizebytes = 16ul

inline_for_extraction
let zero = vec_zero()

[@ CInline]
val state_alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == HS.get_tip h1
      /\ Map.domain (HS.get_hmap h1) == Map.domain (HS.get_hmap h0)))
[@ CInline]
let state_alloc () =
  create zero 4ul


[@ CInline]
val state_incr:
    k:state ->
    Stack unit
      (requires (fun h -> live h k /\ (let st0 = as_seq h k in
         let z = vec_as_seq (Seq.index st0 3) in
         let c = Seq.index z 0 in
         UInt32.v c < pow2 32 - 1)))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1 /\ live h0 k /\
        (let st0 = as_seq h0 k in
         let st1 = as_seq h1 k in
         let op_String_Access = Seq.index in
         let c = (Seq.index (vec_as_seq (Seq.index st0 3)) 0) in
         UInt32.v c < pow2 32 - 1 /\
         st1.[0] == st0.[0] /\
         st1.[1] == st0.[1] /\
         st1.[2] == st0.[2] /\
         vec_as_seq st1.[3] == (Seq.upd (vec_as_seq st0.[3]) 0 FStar.UInt32.(c +^ 1ul)))
         ))
#reset-options "--max_fuel 0 --z3rlimit 100"
[@ CInline]
let state_incr k =
  let h0 = ST.get() in
  let k3 = k.(3ul) in
  k.(3ul) <- vec_increment k3;
  let h1 = ST.get() in
  assert(let vec  = vec_as_seq (Seq.index (as_seq h0 k) 3) in
         let vec' = vec_as_seq (Seq.index (as_seq h1 k) 3) in
         let x = Seq.index vec 0 in
         let x' = Seq.index vec' 0 in
         UInt32.v x' = UInt32.v x + 1);
  assert(let vec  = vec_as_seq (Seq.index (as_seq h0 k) 3) in
         let vec' = vec_as_seq (Seq.index (as_seq h1 k) 3) in
         let x = Seq.index vec 1 in
         let x' = Seq.index vec' 1 in
         x' == x);
  assert(let vec  = vec_as_seq (Seq.index (as_seq h0 k) 3) in
         let vec' = vec_as_seq (Seq.index (as_seq h1 k) 3) in
         let x = Seq.index vec 2 in
         let x' = Seq.index vec' 2 in
         x' == x);
  assert(let vec  = vec_as_seq (Seq.index (as_seq h0 k) 3) in
         let vec' = vec_as_seq (Seq.index (as_seq h1 k) 3) in
         let x = Seq.index vec 2 in
         let x' = Seq.index vec' 2 in
         x' == x);
  Seq.lemma_eq_intro (vec_as_seq (Seq.index (as_seq h1 k) 3))
                     (Seq.upd (vec_as_seq (Seq.index (as_seq h0 k) 3)) 0
                              (let vec = vec_as_seq (Seq.index (as_seq h0 k) 3) in
                               let c = Seq.index vec 0 in
                               FStar.UInt32.(c +^ 1ul)))


[@ CInline]
val state_to_key:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> h0 == h1))
[@ CInline]
let state_to_key k = ()

#reset-options "--max_fuel 0 --z3rlimit 200"

[@ CInline]
val state_to_key_block:
    stream_block:uint8_p{length stream_block = 64} ->
    k:state{disjoint k stream_block} ->
    Stack unit
      (requires (fun h -> live h k /\ live h stream_block))
      (ensures  (fun h0 _ h1 -> live h0 k /\ modifies_1 stream_block h0 h1 /\ live h1 stream_block /\
        (let stream_block = reveal_sbytes (as_seq h1 stream_block) in
         let k = as_seq h0 k in
         let op_String_Access = Seq.index in
         stream_block == FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[0]) @|
                                    Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[1]) @|
                                    Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[2]) @|
                                    Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[3])))))

#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_state_to_key_block:
  a:Seq.seq UInt8.t{Seq.length a = 16} ->
  b:Seq.seq UInt32.t{Seq.length b = 4} ->
  Lemma (requires (Spec.Lib.uint32s_from_le 4 a == b))
        (ensures (a == Spec.Lib.uint32s_to_le 4 b))
let lemma_state_to_key_block a b =
  Spec.Lib.lemma_uint32s_to_le_bij 4 b;
  Spec.Lib.lemma_uint32s_from_le_bij 4 a;
  Spec.Lib.lemma_uint32s_from_le_inj 4 a (Spec.Lib.uint32s_to_le 4 b);
  Seq.lemma_eq_intro a (Spec.Lib.uint32s_to_le 4 b)

#reset-options "--max_fuel 0 --z3rlimit 200"

[@ CInline]
let state_to_key_block stream_block k =
  let k0 = k.(0ul) in
  let k1 = k.(1ul) in
  let k2 = k.(2ul) in
  let k3 = k.(3ul) in
  let a = Buffer.sub stream_block 0ul  16ul in
  let b = Buffer.sub stream_block 16ul 16ul in
  let c = Buffer.sub stream_block 32ul 16ul in
  let d = Buffer.sub stream_block 48ul 16ul in
  let h0 = ST.get() in
  vec_store_le a k0;
  let h1 = ST.get() in
  lemma_state_to_key_block (reveal_sbytes (as_seq h1 a)) (vec_as_seq k0);
  vec_store_le b k1;
  let h2 = ST.get() in
  lemma_state_to_key_block (reveal_sbytes (as_seq h2 b)) (vec_as_seq k1);
  no_upd_lemma_1 h1 h2 b a;
  vec_store_le c k2;
  let h3 = ST.get() in
  lemma_state_to_key_block (reveal_sbytes (as_seq h3 c)) (vec_as_seq k2);
  no_upd_lemma_1 h2 h3 c a;
  no_upd_lemma_1 h2 h3 c b;
  vec_store_le d k3;
  let h4 = ST.get() in
  lemma_state_to_key_block (reveal_sbytes (as_seq h4 d)) (vec_as_seq k3);
  no_upd_lemma_1 h3 h4 d a;
  no_upd_lemma_1 h3 h4 d b;
  no_upd_lemma_1 h3 h4 d c;
  Seq.lemma_eq_intro (as_seq h4 stream_block) FStar.Seq.(as_seq h4 a @| as_seq h4 b @| as_seq h4 c @| as_seq h4 d)


[@ Substitute]
val constant_setup_:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c /\
      (let st0 = as_seq h0 c in let st1 = as_seq h1 c in let op_String_Access = Seq.index in
       let open Spec.Chacha20_vec in let open FStar.Seq in
       vec_as_seq st1.[0] == Seq.Create.create_4 c0 c1 c2 c3 /\
       st0.[1] == st1.[1] /\ st0.[2] == st1.[2] /\ st0.[3] == st1.[3])))
[@ Substitute]
let constant_setup_ st =
  st.(0ul)  <- vec_load_32x4 (uint32_to_sint32 0x61707865ul)
  	       		     (uint32_to_sint32 0x3320646eul)
			     (uint32_to_sint32 0x79622d32ul)
			     (uint32_to_sint32 0x6b206574ul)


[@ Substitute]
val constant_setup:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c /\
      (let st0 = as_seq h0 c in let st1 = as_seq h1 c in let op_String_Access = Seq.index in
       let open Spec.Chacha20_vec in let open FStar.Seq in
       vec_as_seq st1.[0] == Seq.Create.create_4 c0 c1 c2 c3 /\
       st0.[1] == st1.[1] /\ st0.[2] == st1.[2] /\ st0.[3] == st1.[3])))
[@ Substitute]
let constant_setup st =
  constant_setup_ st


[@ Substitute]
val keysetup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1 /\
      (let st0 = as_seq h0 st in let st1 = as_seq h1 st in let op_String_Access = Seq.index in
       let k = reveal_sbytes (as_seq h0 k) in
       st1.[0] == st0.[0] /\
       st1.[3] == st0.[3] /\
       vec_as_seq st1.[1] == Spec.Lib.uint32s_from_le 4 (Seq.slice k 0 16) /\
       vec_as_seq st1.[2] == Spec.Lib.uint32s_from_le 4 (Seq.slice k 16 32)
       )))
[@ Substitute]
let keysetup st k =
  let k0 = vec_load128_le (Buffer.sub k 0ul 16ul) in
  let k1 = vec_load128_le (Buffer.sub k 16ul 16ul) in
  st.(1ul) <- k0;
  st.(2ul) <- k1


[@ Substitute]
val ctr_ivsetup:
  st:state ->
  ctr:U32.t ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  Stack unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv /\ live h0 st /\
      (let st0 = as_seq h0 st in let st1 = as_seq h1 st in let op_String_Access = Seq.index in
       st1.[0] == st0.[0] /\
       st1.[1] == st0.[1] /\
       st1.[2] == st0.[2] /\
       vec_as_seq st1.[3] == Seq.cons ctr (Spec.Lib.uint32s_from_le 3 (reveal_sbytes (as_seq h0 iv)))) ))


val lemma_ctr_ivsetup:
  iv:Seq.seq UInt8.t{Seq.length iv = 12} ->
  Lemma (let s = Spec.Lib.uint32s_from_le 3 iv in
         Seq.index s 0 == Spec.Lib.uint32_from_le (Seq.slice iv 0 4) /\
         Seq.index s 1 == Spec.Lib.uint32_from_le (Seq.slice iv 4 8) /\
         Seq.index s 2 == Spec.Lib.uint32_from_le (Seq.slice iv 8 12))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_ctr_ivsetup iv =
  Spec.Lib.lemma_uint32s_from_le_def_1 3 iv;
  assert(Seq.index (Spec.Lib.uint32s_from_le 3 iv) 2 == Spec.Lib.uint32_from_le (Seq.slice iv 8 12));
  Spec.Lib.lemma_uint32s_from_le_def_1 2 (Seq.slice iv 0 8);
  Seq.lemma_eq_intro (Seq.slice (Seq.slice iv 0 8) 4 8) (Seq.slice iv 4 8);
  Seq.lemma_eq_intro (Seq.slice (Seq.slice iv 0 8) 0 4) (Seq.slice iv 0 4);
  assert(Seq.index (Spec.Lib.uint32s_from_le 3 iv) 1 == Spec.Lib.uint32_from_le (Seq.slice iv 4 8));
  Spec.Lib.lemma_uint32s_from_le_def_1 1 (Seq.slice iv 0 4);
  Seq.lemma_eq_intro (Seq.slice (Seq.slice iv 0 4) 0 4) (Seq.slice iv 0 4);
  Seq.lemma_eq_intro (Seq.slice (Seq.slice iv 0 4) 0 0) Seq.createEmpty;
  Spec.Lib.lemma_uint32s_from_le_def_0 0 (Seq.slice iv 0 0)


[@ Substitute]
let ctr_ivsetup st ctr iv =
  let n0 = hload32_le (Buffer.sub iv 0ul 4ul) in
  let n1 = hload32_le (Buffer.sub iv 4ul 4ul) in
  let n2 = hload32_le (Buffer.sub iv 8ul 4ul) in
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h iv) FStar.Seq.(as_seq h (Buffer.sub iv 0ul 4ul) @| as_seq h (Buffer.sub iv 4ul 4ul) @| as_seq h (Buffer.sub iv 8ul 4ul));
  lemma_ctr_ivsetup (reveal_sbytes (as_seq h iv));
  let v =  vec_load_32x4 (uint32_to_sint32 ctr) n0 n1 n2 in
  Seq.lemma_eq_intro (Seq.slice (vec_as_seq v) 1 4) (Spec.Lib.uint32s_from_le 3 (reveal_sbytes (as_seq h iv)));
  Seq.lemma_eq_intro (vec_as_seq v) (Seq.cons ctr (Spec.Lib.uint32s_from_le 3 (reveal_sbytes (as_seq h iv))));
  st.(3ul) <- v


[@ CInline]
val state_setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1 /\
      (let st = as_seq h1 st in
       let op_String_Access = Seq.index in
       Seq.Create.create_4 (vec_as_seq st.[0]) (vec_as_seq st.[1]) (vec_as_seq st.[2]) (vec_as_seq st.[3])
       == Spec.Chacha20_vec.setup (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) (U32.v c))))
[@ CInline]
let state_setup st k n c =
  let h0 = ST.get() in
  constant_setup st;
  keysetup st k;
  ctr_ivsetup st c n;
  let h = ST.get() in
  Seq.lemma_eq_intro (let st = as_seq h st in
                     let op_String_Access = Seq.index in
                     Seq.Create.create_4 (vec_as_seq st.[0]) (vec_as_seq st.[1])
                                         (vec_as_seq st.[2]) (vec_as_seq st.[3]))
                     (Spec.Chacha20_vec.setup (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) (U32.v c))
