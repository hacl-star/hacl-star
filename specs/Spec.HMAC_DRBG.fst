module Spec.HMAC_DRBG

open Spec.Hash.Definitions
open Spec.Agile.HMAC

open Lib.IntTypes
open FStar.Seq
open FStar.Mul

/// HMAC-DRBG
///
/// See 10.1.2 in
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
/// 

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let supported_alg = a:hash_alg{ is_supported_alg a }

let reseed_interval   = pow2 48
let max_output_length = pow2 16
let max_length        = pow2 16

/// See p.54
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-57pt1r4.pdf
let min_length (a:supported_alg) =
  match a with
  | SHA1 -> 16
  | SHA2_256 | SHA2_384 | SHA2_512 -> 32

noeq
type state (a:supported_alg) =
| State: 
    k:lbytes (hash_length a) 
  -> v:lbytes (hash_length a) 
  -> reseed_counter:nat
  -> state a

val hmac_input_bound: a:supported_alg -> Lemma 
  (hash_length a + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
let hmac_input_bound = function
  | SHA1     -> 
    let a = SHA1 in
    assert_norm (hash_length a + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
  | SHA2_256 ->   
    let a = SHA2_256 in
    assert_norm (hash_length a + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
  | SHA2_384 -> 
    let a = SHA2_384 in
    assert_norm (hash_length a + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
  | SHA2_512 -> 
    let a = SHA2_512 in
    assert_norm (hash_length a + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)

val update: #a:supported_alg
  -> data:bytes
  -> state a 
  -> Pure (state a)
  (requires hash_length a + Seq.length data + 1 + block_length a <= max_input_length a)
  (ensures  fun _ -> True)
let update #a data (State k v ctr) =
  let zero_data = Seq.cons (u8 0) data in
  let k = hmac a k (v @| zero_data) in
  let v = hmac a k v in
  if Seq.length data = 0 then
    State k v ctr
  else
    let one_data = Seq.cons (u8 1) data in
    let k = hmac a k (v @| one_data) in
    let v = hmac a k v in
    State k v ctr

(* We omit personalization_string *)
val instantiate: #a:supported_alg
  -> entropy_input:bytes
  -> nonce:bytes
  -> Pure (state a)
  (requires
    hash_length a + Seq.length entropy_input 
    + Seq.length nonce + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
let instantiate #a entropy_input nonce =
  let seed_material = entropy_input @| nonce in
  let k = Seq.create (hash_length a) (u8 0) in
  let v = Seq.create (hash_length a) (u8 1) in  
  update #a seed_material (State k v 1)

val reseed: #a:supported_alg
  -> state a
  -> entropy_input: bytes
  -> Pure (state a)
  (requires 
    hash_length a + Seq.length entropy_input + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
let reseed #a st entropy_input =
  let State k v _ = update #a entropy_input st in
  State k v 1

let a_spec (a:hash_alg) (i:nat) = Lib.Sequence.lseq uint8 (hash_length a)

val generate_loop:
    a:supported_alg
  -> k:lbytes (hash_length a)
  -> max:nat
  -> i:nat{i < max}
  -> a_spec a i
  -> Pure (a_spec a (i + 1) & Lib.Sequence.lseq uint8 (hash_length a))
    (requires True)
    (ensures fun _ -> True)
let generate_loop a k max i vi =
  hmac_input_bound a;
  let v = hmac a k vi in v, v

(* We omit additional_input; n is the number of **bytes** requested *)
val generate: #a:supported_alg
  -> state a
  -> n:pos{n <= max_output_length}
  -> option (lbytes n & state a)
let generate #a (State k v ctr) n =
  hmac_input_bound a;
  if ctr > reseed_interval then 
    None
  else    
    let max = n / hash_length a in
    let v, output =
      Lib.Sequence.generate_blocks (hash_length a) max max (a_spec a)
        (generate_loop a k max)
        v
    in
    let v, output =
      if max * hash_length a < n then
        let v = hmac a k v in
        v, output @| Lib.Sequence.sub #_ #(hash_length a) v 0 (n - max * hash_length a)
      else
        v, output
    in
    let State k v _ = update Seq.empty (State k v ctr) in
    Some (output, State k v (ctr + 1))

(** Equivalently, but proving it requires proving extensionality of generate_blocks *)
val generate': #a:supported_alg
  -> state a
  -> n:pos{n <= max_output_length}
  -> option (lbytes n & state a)
let generate' #a (State k v ctr) n =
  hmac_input_bound a;
  if ctr > reseed_interval then 
    None
  else    
    // let max = ceil (n / hash_length a) in
    let max = (n + hash_length a - 1) / hash_length a in
    let v, output =
      Lib.Sequence.generate_blocks (hash_length a) max max (a_spec a)
        (generate_loop a k max)
        v
    in
    let State k v _ = update Seq.empty (State k v ctr) in
    Some (Seq.slice output 0 n, State k v (ctr + 1))
