module Hacl.Spec.Chacha20

open FStar.Mul
open FStar.Seq
open Hacl.Cast
open Hacl.UInt32

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_s = seq H8.t
type key   = k:uint8_s{length k = 32}
type nonce = n:uint8_s{length n = 12}
type ctr   = u32
type block  = b:uint8_s{length b = 64}

type chacha_sctx = b:seq h32{length b = 16}
type ctx_idx = n:int{n >= 0 /\ n < 16}


(* ***************************************** *)
(* Local functions that should be outsourced *)
(* ***************************************** *)

private val lemma_max_uint32: n:nat ->
  Lemma (requires (n = 32))
        (ensures (pow2 n = 4294967296))
        [SMTPat (pow2 n)]
private let lemma_max_uint32 n = assert_norm (pow2 32 = 4294967296)

(* Needs to go to a general library *)
let bytes_to_h32 (k:uint8_s{length k >= 4}) : Tot h32
  = let k0 = Seq.index k 0 in
    let k1 = Seq.index k 1 in
    let k2 = Seq.index k 2 in
    let k3 = Seq.index k 3 in
    let z = sint8_to_sint32 k0 |^ (sint8_to_sint32 k1 <<^ 8ul)
            |^ (sint8_to_sint32 k2 <<^ 16ul) |^ (sint8_to_sint32 k3 <<^ 24ul) in
    z

(* Needs to go to a general library *)
let h32_to_bytes (x:h32) : Tot (s':uint8_s{length s' = 4})
  = let s = Seq.create 4 (uint8_to_sint8 0uy) in
    let s = Seq.upd s 0 (sint32_to_sint8 x) in
    let s = Seq.upd s 1 (sint32_to_sint8 (x >>^ 8ul)) in
    let s = Seq.upd s 2 (sint32_to_sint8 (x >>^ 16ul)) in
    let s = Seq.upd s 3 (sint32_to_sint8 (x >>^ 24ul)) in
    s

let rec iter (#a:Type) (ctr:nat) (max:nat{max >= ctr}) (f:a -> Tot a) (v:a) : Tot a (decreases (max-ctr)) =
  let v' = f v in
  if ctr < max then iter (ctr+1) max f v'
  else v'

#set-options "--initial_fuel 1 --max_fuel 1"

val map2: ('a -> 'b -> Tot 'c) -> a:list 'a -> b:list 'b{List.Tot.length a = List.Tot.length b} -> Tot (c:list 'c{List.Tot.length c = List.Tot.length a}) (decreases (List.Tot.length a))
let rec map2 f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | hd::tl, hd'::tl' -> (f hd hd')::(map2 f tl tl')


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


(* ***************************************** *)
(*                 Chacha Spec               *)
(* ***************************************** *)

inline_for_extraction let op_Less_Less_Less (a:h32) (s:u32{U32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


val chacha_quarter_round_spec: ctx:chacha_sctx -> a:ctx_idx -> b:ctx_idx -> c:ctx_idx -> d:ctx_idx ->
  Tot (ctx':chacha_sctx)
let chacha_quarter_round_spec ctx a b c d =
  let va = Seq.index ctx a in
  let vb = Seq.index ctx b in
  let vc = Seq.index ctx c in
  let vd = Seq.index ctx d in
  let va = va +%^ vb in
  let vd = vd ^^  va in
  let vd = vd <<< 16ul in
  let vc = vc +%^ vd in
  let vb = vb ^^  vc in
  let vb = vb <<< 12ul in
  let va = va +%^ vb in
  let vd = vd ^^  va in
  let vd = vd <<< 8ul in
  let vc = vc +%^ vd in
  let vb = vb ^^  vc in
  let vb = vb <<< 7ul in
  let ctx = Seq.upd ctx a va in
  let ctx = Seq.upd ctx b vb in
  let ctx = Seq.upd ctx c vc in
  let ctx = Seq.upd ctx d vd in
  ctx


val chacha_inner_block_spec: ctx:chacha_sctx -> Tot (ctx':chacha_sctx)
let chacha_inner_block_spec ctx =
  let ctx = chacha_quarter_round_spec ctx 0 4 8  12 in
  let ctx = chacha_quarter_round_spec ctx 1 5 9  13 in
  let ctx = chacha_quarter_round_spec ctx 2 6 10 14 in
  let ctx = chacha_quarter_round_spec ctx 3 7 11 15 in
  let ctx = chacha_quarter_round_spec ctx 0 5 10 15 in
  let ctx = chacha_quarter_round_spec ctx 1 6 11 12 in
  let ctx = chacha_quarter_round_spec ctx 2 7 8  13 in
  let ctx = chacha_quarter_round_spec ctx 3 4 9  14 in
  ctx

#reset-options

let chacha_state_setup_constants : c:seq h32{length c = 4} =
  let l = [(uint32_to_sint32 0x61707865ul); (uint32_to_sint32 0x3320646eul);
           (uint32_to_sint32 0x79622d32ul); (uint32_to_sint32 0x6b206574ul)] in
  assert_norm(List.Tot.length l = 4);
  SeqProperties.seq_of_list l

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

let chacha_state_setup_key (k:key) : Tot (k':seq h32{length k' = 8}) =
  let k' = Seq.create 8 (uint32_to_sint32 0ul) in
  let k' = Seq.upd k' 0 (bytes_to_h32 (slice k 0 4)) in
  let k' = Seq.upd k' 1 (bytes_to_h32 (slice k 4 8)) in
  let k' = Seq.upd k' 2 (bytes_to_h32 (slice k 8 12)) in
  let k' = Seq.upd k' 3 (bytes_to_h32 (slice k 12 16)) in
  let k' = Seq.upd k' 4 (bytes_to_h32 (slice k 16 20)) in
  let k' = Seq.upd k' 5 (bytes_to_h32 (slice k 20 24)) in
  let k' = Seq.upd k' 6 (bytes_to_h32 (slice k 24 28)) in
  let k' = Seq.upd k' 7 (bytes_to_h32 (slice k 28 32)) in
  k'


let chacha_state_setup_nonce (n:nonce) : Tot (n':seq h32{length n' = 3}) =
  let n' = Seq.create 3 (uint32_to_sint32 0ul) in
  let n' = Seq.upd n' 0 (bytes_to_h32 (slice n 0 4)) in
  let n' = Seq.upd n' 1 (bytes_to_h32 (slice n 4 8)) in
  let n' = Seq.upd n' 2 (bytes_to_h32 (slice n 8 12)) in
  n'


val chacha_state_setup_spec: k:key -> counter:ctr -> n:nonce -> Tot chacha_sctx
let chacha_state_setup_spec k counter n =
  chacha_state_setup_constants
  @| (chacha_state_setup_key k)
  @| (create 1 (uint32_to_sint32 counter))
  @| (chacha_state_setup_nonce n)


val chacha_state_sum: s:chacha_sctx -> s':chacha_sctx -> Tot chacha_sctx
let chacha_state_sum s s' =
  SeqProperties.seq_of_list (map2 (H32.add_mod) (SeqProperties.seq_to_list s) 
                                                (SeqProperties.seq_to_list s'))

val chacha_state_serialize: s:chacha_sctx -> Tot block
let chacha_state_serialize s =
  let l = SeqProperties.seq_to_list s in
  let l' = List.Tot.flatten (List.Tot.map (fun x -> SeqProperties.seq_to_list (h32_to_bytes x)) l) in
  assume (List.Tot.length l' = 64); // TODO
  SeqProperties.seq_of_list l'


val chacha_block: k:key -> counter:ctr -> n:nonce -> Tot block
let chacha_block k counter n =
  let state = chacha_state_setup_spec k counter n in
  let working_state = state in
  let state = iter 1 10 chacha_inner_block_spec state in
  let state = chacha_state_sum state working_state in
  chacha_state_serialize state


val chacha20_encrypt: k:key -> counter:ctr -> n:nonce -> plaintext:uint8_s -> Tot (c:uint8_s)
let chacha20_encrypt k counter n plaintext =
  let max = length plaintext / 64 in
  let rem = length plaintext % 64 in
  let rec loop (j:nat{j <= max}) (encrypted_message:uint8_s) : Tot uint8_s (decreases (max - j)) =
    if j = max then encrypted_message
    else let keystream = chacha_block k counter n in
         let block = slice plaintext (j*64) (j*64+64) in
         let encrypted_message = encrypted_message @|
                                (SeqProperties.seq_of_list (map2 (H8.logxor)
                                                           (SeqProperties.seq_to_list keystream)
                                                           (SeqProperties.seq_to_list block))) in
         loop (j+1) encrypted_message in
  let encrypted_message = loop 0 (createEmpty) in
  if rem = 0 then encrypted_message
  else let keystream = chacha_block k (UInt32.uint_to_t max) n in
       let block = slice plaintext max (length plaintext) in
       let encrypted_mesage = encrypted_message @|
                              SeqProperties.seq_of_list (map2 (H8.logxor)
                                                        (SeqProperties.seq_to_list keystream)
                                                        (SeqProperties.seq_to_list (slice block 0 rem))) in
       encrypted_message
