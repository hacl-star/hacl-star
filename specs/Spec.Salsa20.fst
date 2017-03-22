module Spec.Salsa20

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib
open Seq.Create

(* This should go elsewhere! *)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 8   (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type nonce = lbytes noncelen
type counter = UInt.uint_t 64
type state = m:seq UInt32.t {length m = 16}
type idx = n:nat{n < 16}
type shuffle = state -> Tot state 

val line: idx -> idx -> idx -> s:UInt32.t {v s < 32} -> shuffle
let line a b d s m = 
  let m = upd m a (index m a ^^ ((index m b +%^ index m d) <<< s)) in
  m

let quarter_round a b c d : shuffle = 
  line b a d 7ul @ 
  line c b a 9ul @
  line d c b 13ul @ 
  line a d c 18ul 

let column_round : shuffle = 
  quarter_round 0 4 8 12 @
  quarter_round 5 9 13 1 @
  quarter_round 10 14 2 6 @
  quarter_round 15 3 7 11 

let row_round : shuffle = 
  quarter_round 0 1 2 3  @
  quarter_round 5 6 7 4 @
  quarter_round 10 11 8 9 @
  quarter_round 15 12 13 14

let double_round: shuffle = 
  column_round @ row_round (* 2 rounds *)

let rec rounds : shuffle = 
    Spec.Loops.repeat_spec 10 double_round (* 20 rounds *)

let salsa20_core (s:state) : Tot state = 
    let s' = rounds s in
    Spec.Loops.seq_map2 (fun x y -> x +%^ y) s' s

(* state initialization *) 

unfold inline_for_extraction
let constant0 = 0x61707865ul
unfold inline_for_extraction
let constant1 = 0x3320646eul
unfold inline_for_extraction
let constant2 = 0x79622d32ul
unfold inline_for_extraction
let constant3 = 0x6b206574ul

let setup (k:key) (n:nonce) (c:counter): state =
  let ks = uint32s_from_le 8 k in
  let ns = uint32s_from_le 2 n in
  let c64 = UInt64.uint_to_t c in
  let c0 = FStar.Int.Cast.uint64_to_uint32 c64 in
  let c1 = FStar.Int.Cast.uint64_to_uint32 FStar.UInt64.(c64 >>^ 32ul) in
  create_16 constant0    (index ks 0) (index ks 1) (index ks 2)
          (index ks 3) constant1    (index ns 0) (index ns 1)
	  c0 	       c1	    constant2    (index ks 4)
          (index ks 5) (index ks 6) (index ks 7) constant3
	   

let salsa20_block (k:key) (n:nonce) (c:counter): block =
    let st = setup k n c in
    let st' = salsa20_core st in
    uint32s_to_le 16 st'


let salsa20_ctx: Spec.CTR.block_cipher_ctx = 
    let open Spec.CTR in
    {
    keylen = keylen;
    blocklen = blocklen;
    noncelen = noncelen;
    counterbits = 64;
    incr = 1
    }

let salsa20_cipher: Spec.CTR.block_cipher salsa20_ctx = salsa20_block

let salsa20_encrypt_bytes key nonce counter m = 
    Spec.CTR.counter_mode salsa20_ctx salsa20_cipher key nonce counter m



(* TESTS: https://cr.yp.to/snuffle/spec.pdf *)

#set-options "--lax"

let test_quarter_round () = 
    let st = create 16 0ul in
    let st1 = quarter_round 0 1 2 3 st in
    let st2 = quarter_round 0 1 2 3 (upd st 0 1ul) in 	
    (slice st1 0 4) = createL [0ul;0ul;0ul;0ul] &&
    (slice st2 0 4) = createL [0x08008145ul;0x80ul;0x010200ul;0x20500000ul] 


let test_row_round () = 
    let st = create 16 0ul in
    let st = upd st 0 1ul in
    let st = upd st 4 1ul in
    let st = upd st 8 1ul in
    let st = upd st 12 1ul in
    let st = row_round st in
    st = createL [
        0x08008145ul; 0x00000080ul; 0x00010200ul; 0x20500000ul;
	0x20100001ul; 0x00048044ul; 0x00000080ul; 0x00010000ul;
	0x00000001ul; 0x00002000ul; 0x80040000ul; 0x00000000ul;	
	0x00000001ul; 0x00000200ul; 0x00402000ul; 0x88000100ul
	]

let test_column_round () = 
    let st = create 16 0ul in
    let st = upd st 0 1ul in
    let st = upd st 4 1ul in
    let st = upd st 8 1ul in
    let st = upd st 12 1ul in
    let st = column_round st in
    st = createL [
       	 0x10090288ul; 0x00000000ul; 0x00000000ul; 0x00000000ul;
 	 0x00000101ul; 0x00000000ul; 0x00000000ul; 0x00000000ul;
    	 0x00020401ul; 0x00000000ul; 0x00000000ul; 0x00000000ul;
    	 0x40a04001ul; 0x00000000ul; 0x00000000ul; 0x00000000ul
		 ]
let test_column_round2 () = 
    let st = createL [
    	 0x08521bd6ul; 0x1fe88837ul; 0xbb2aa576ul; 0x3aa26365ul;	
    	 0xc54c6a5bul; 0x2fc74c2ful; 0x6dd39cc3ul; 0xda0a64f6ul;	
	 0x90a2f23dul; 0x067f95a6ul; 0x06b35f61ul; 0x41e4732eul;
    	 0xe859c100ul; 0xea4d84b7ul; 0x0f619bfful; 0xbc6e965aul] in
    let st = column_round st in
    st = createL [
         0x8c9d190aul; 0xce8e4c90ul; 0x1ef8e9d3ul; 0x1326a71aul;
	 0x90a20123ul; 0xead3c4f3ul; 0x63a091a0ul; 0xf0708d69ul;
	 0x789b010cul; 0xd195a681ul; 0xeb7d5504ul; 0xa774135cul;
	 0x481c2027ul; 0x53a8e4b5ul; 0x4c1f89c5ul; 0x3f78c9c8ul
		 ]

let test_salsa20_core () = 
    let st = uint32s_from_le 16 (createL [
    	   211uy;159uy; 13uy;115uy; 76uy; 55uy; 82uy;183uy; 3uy;117uy;222uy; 37uy;191uy;187uy;234uy;136uy;
	   49uy;237uy;179uy; 48uy; 1uy;106uy;178uy;219uy;175uy;199uy;166uy; 48uy; 86uy; 16uy;179uy;207uy;
	   31uy;240uy; 32uy; 63uy; 15uy; 83uy; 93uy;161uy;116uy;147uy; 48uy;113uy;238uy; 55uy;204uy; 36uy;
	   79uy;201uy;235uy; 79uy; 3uy; 81uy;156uy; 47uy;203uy; 26uy;244uy;243uy; 88uy;118uy;104uy; 54uy
	   ])   in
    let st = salsa20_core st in
    st = uint32s_from_le 16 (createL[
           109uy; 42uy;178uy;168uy;156uy;240uy;248uy;238uy;168uy;196uy;190uy;203uy; 26uy;110uy;170uy;154uy;
	   29uy; 29uy;150uy; 26uy;150uy; 30uy;235uy;249uy;190uy;163uy;251uy; 48uy; 69uy;144uy; 51uy; 57uy;
	   118uy; 40uy;152uy;157uy;180uy; 57uy; 27uy; 94uy;107uy; 42uy;236uy; 35uy; 27uy;111uy;114uy;114uy;
	   219uy;236uy;232uy;135uy;111uy;155uy;110uy; 18uy; 24uy;232uy; 95uy;158uy;179uy; 19uy; 48uy;202uy
	   ])
    
let test() = 
    test_quarter_round () &&
    test_row_round() &&
    test_column_round() &&
    test_column_round2() &&
    test_salsa20_core() 
