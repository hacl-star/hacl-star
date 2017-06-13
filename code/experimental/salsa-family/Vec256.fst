module Vec256

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open Hacl.Cast
open C.Loops
open Spec.Chacha20_vec256
open FStar.Seq

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

let u32 = U32.t
let h32 = H32.t
let uint8_p = Buffer.buffer Hacl.UInt8.t

abstract val vec_add: v:vec -> v':vec -> Tot (v'':vec{
  index v'' 0 == U32.add_mod (index v 0) (index v' 0) /\ 
  index v'' 1 == U32.add_mod (index v 1) (index v' 1) /\ 
  index v'' 2 == U32.add_mod (index v 2) (index v' 2) /\ 
  index v'' 3 == U32.add_mod (index v 3) (index v' 3) /\ 
  index v'' 4 == U32.add_mod (index v 4) (index v' 4) /\ 
  index v'' 5 == U32.add_mod (index v 5) (index v' 5) /\ 
  index v'' 6 == U32.add_mod (index v 6) (index v' 6) /\ 
  index v'' 7 == U32.add_mod (index v 7) (index v' 7)
  })
let vec_add v v' =
  seq_map2 FStar.UInt32.op_Plus_Percent_Hat v v'

let vec128 = s:seq UInt32.t{length s = 4}

val get_fst: vec -> Tot vec128
let get_fst v = slice v 0 4

val get_snd: vec -> Tot vec128
let get_snd v = slice v 4 8

val mk: vec128 -> vec128 -> Tot vec
let mk v v' = v @| v'

abstract val vec_choose_128: v:vec -> v':vec -> i:UInt32.t{UInt32.v i = 0 \/ UInt32.v i = 1} ->
  j:UInt32.t{UInt32.v j = 2 \/ UInt32.v j = 3} -> Tot (v'':vec{
  let x = (if UInt32.v i = 0 then get_fst v else get_snd v) in
  let y = (if UInt32.v j = 2 then get_fst v' else get_snd v') in
  v'' == mk x y
})
let vec_choose_128 v v' i j =
  let x = (if UInt32.v i = 0 then get_fst v else get_snd v) in
  let y = (if UInt32.v j = 2 then get_fst v' else get_snd v') in
  mk x y

let vec_as_seq (v:vec) = v

assume val vec_store_le: b:uint8_p{Buffer.length b = 32} -> r:vec -> Stack unit
              (requires (fun h -> Buffer.live h b))
	      (ensures  (fun h0 _ h1 -> Buffer.live h1 b /\ Buffer.modifies_1 b h0 h1
	        /\ Buffer.live h0 b /\
	        (let s = Spec.Lib.uint32s_from_le 8 (Buffer.as_seq h1 b) in
		 s == vec_as_seq r)))

assume val vec_load_32x4: v0:U32.t -> v1:U32.t -> v2:U32.t -> v3:U32.t -> Tot (v:vec{
  index v 0 == v0 /\ index v 1 == v1 /\ index v 2 == v2 /\ index v 3 == v3 /\ 
  index v 4 == v0 /\ index v 5 == v1 /\ index v 6 == v2 /\ index v 7 == v3})

assume val vec_load_32x8: v0:U32.t -> v1:U32.t -> v2:U32.t -> v3:U32.t -> 
  v4:U32.t -> v5:U32.t -> v6:U32.t -> v7:U32.t -> Tot (v:vec{
  index v 0 == v0 /\ index v 1 == v1 /\ index v 2 == v2 /\ index v 3 == v3 /\ 
  index v 4 == v4 /\ index v 5 == v5 /\ index v 6 == v6 /\ index v 7 == v7})

assume val vec_load128_le: b:uint8_p{Buffer.length b = 16} ->
  Stack vec
    (requires (fun h -> Buffer.live h b))
    (ensures (fun h0 v h1 -> Buffer.live h0 b /\ h0 == h1
      /\ v == (Spec.Lib.uint32s_from_le 4 (Buffer.as_seq h0 b) @| Spec.Lib.uint32s_from_le 4 (Buffer.as_seq h0 b))))
