module Spec.Chacha20
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful2

(* Chacha20 State *)

noeq type chacha_state = {
  state_i:lseq uint32 16;
  state  :lseq uint32 16;
}

let create_state : allocator chacha_state = fun () ->
  let s = create 16 (u32 0) in
  let s' = create 16 (u32 0) in
  {state_i = s; state = s'} 
  
let state_i: array_accessor chacha_state uint32 16 = {
  get = (fun s -> s.state_i);
  put = (fun s v -> {s with state_i = v})
}

let state: array_accessor chacha_state uint32 16 = {
  get = (fun s -> s.state);
  put = (fun s v -> {s with state = v})
}

type chacha_st (a:Type0)  = stateful chacha_state a 
type index (#a:Type0) (#len:array_size_t) (k:array_accessor chacha_state a len) = 
     i:size_t{i < len}

(* Chacha20 Spec *)

let line (a:index state) (b:index state) (d:index state) (s:rotval U32) : chacha_st unit =
  mb <-- read state b ;
  ma <-- read state a ;
  write state a ((+.) #U32 ma mb) ;;
  ma <-- read state a ;
  md <-- read state d ;
  write state d ((md ^. ma) <<<. s)

let quarter_round a b c d : chacha_st unit =
  line a b d (u32 16) ;;
  line c d b (u32 12) ;;
  line a b d (u32 8)  ;;
  line c d b (u32 7)

let column_round : chacha_st unit = 
  quarter_round 0 4 8  12 ;;
  quarter_round 1 5 9  13 ;;
  quarter_round 2 6 10 14 ;;
  quarter_round 3 7 11 15

let diagonal_round : chacha_st unit =
  quarter_round 0 5 10 15 ;;
  quarter_round 1 6 11 12 ;;
  quarter_round 2 7 8  13 ;;
  quarter_round 3 4 9  14

let double_round: chacha_st unit =
    column_round ;; 
    diagonal_round (* 2 rounds *)

let rounds : chacha_st unit =
    repeat 10 double_round (* 20 rounds *)
 
let chacha20_core: chacha_st unit = 
    copy state_i state ;;
    rounds ;;
    in_place_map2 state_i state ((+.) #U32) 

(* stateate initialization *)
let c0 = u32 0x61707865
let c1 = u32 0x3320646e
let c2 = u32 0x79622d32
let c3 = u32 0x6b206574

let keylen = 32   (* in bytes *)
let blocklen = 64 (* in bytes *)
let noncelen = 12 (* in bytes *)

type chacha_key   = lbytes keylen
type chacha_block = lbytes blocklen
type chacha_nonce = lbytes noncelen
type counter = size_t


let setup (k:chacha_key) (n:chacha_nonce) (c:counter): chacha_st unit =
  write state_i 0 c0 ;;
  write state_i 1 c1 ;;
  write state_i 2 c2 ;;
  write state_i 3 c3 ;;
  import_slice k state_i 4 12 (uints_from_bytes_le #U32 #8) ;;
  write state_i 12 (u32 c) ;;
  import_slice n state_i 13 16 (uints_from_bytes_le #U32 #3) 


let chacha20_block (k:chacha_key) (n:chacha_nonce) (c:counter) (f:chacha_block -> stateful 't 'a) : stateful 't 'a =
  let b = 
    run create_state (
       setup k n c ;;
       chacha20_core ;;
       export state (uints_to_bytes_le #U32 #16)
    )
  in f b
let chacha20_ctx: Spec.CTR.block_cipher_ctx =
    let open Spec.CTR in
    {
    keylen = keylen;
    noncelen = noncelen;
    countermax = maxint U32;
    blocklen = blocklen;
    }

let chacha20_block_cipher: Spec.CTR.block_cipher chacha20_ctx = chacha20_block

let chacha20_encrypt_bytes key nonce counter len m =
    let chacha20_ctr = Spec.CTR.counter_mode chacha20_ctx chacha20_block_cipher in
    chacha20_ctr key nonce counter len m





