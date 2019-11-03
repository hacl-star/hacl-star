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
let max_personalization_string_length = pow2 16
let max_additional_input_length = pow2 16

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
  (hash_length a + pow2 32 + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
let hmac_input_bound = function
  | SHA1     -> 
    let a = SHA1 in
    assert_norm (hash_length a + pow2 32 + pow2 32 +1 + block_length a + block_length a <= max_input_length a)
  | SHA2_256 ->   
    let a = SHA2_256 in
    assert_norm (hash_length a + pow2 32 + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
  | SHA2_384 -> 
    let a = SHA2_384 in
    assert_norm (hash_length a + pow2 32 + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)
  | SHA2_512 -> 
    let a = SHA2_512 in
    assert_norm (hash_length a + pow2 32 + pow2 32 + 1 + block_length a + block_length a <= max_input_length a)

val update: #a:supported_alg
  -> data:bytes
  -> k:lbytes (hash_length a)
  -> v:lbytes (hash_length a)
  -> Pure (lbytes (hash_length a) & lbytes (hash_length a))
  (requires hash_length a + Seq.length data + 1 + block_length a <= max_input_length a)
  (ensures  fun _ -> True)
let update #a data k v =
  let zero_data = Seq.cons (u8 0) data in
  let k = hmac a k (v @| zero_data) in
  let v = hmac a k v in
  if Seq.length data = 0 then
    k, v
  else
    let one_data = Seq.cons (u8 1) data in
    let k = hmac a k (v @| one_data) in
    let v = hmac a k v in
    k, v 

(* We omit personalization_string *)
val instantiate: #a:supported_alg
  -> entropy_input:bytes
  -> nonce:bytes
  -> personalization_string:bytes
  -> Pure (state a)
  (requires
    hash_length a
    + Seq.length entropy_input 
    + Seq.length nonce 
    + Seq.length personalization_string 
    + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
let instantiate #a entropy_input nonce personalization_string =
  let seed_material = entropy_input @| nonce @| personalization_string in
  let k = Seq.create (hash_length a) (u8 0) in
  let v = Seq.create (hash_length a) (u8 1) in  
  let k, v = update #a seed_material k v in
  State k v 1

val reseed: #a:supported_alg
  -> state a
  -> entropy_input: bytes
  -> additional_input: bytes
  -> Pure (state a)
  (requires 
    hash_length a + 
    Seq.length entropy_input + 
    Seq.length additional_input +
    1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
let reseed #a st entropy_input additional_input =
  let seed_material = entropy_input @| additional_input in
  let k, v = update #a seed_material st.k st.v in
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
  -> additional_input: bytes
  -> Pure (option (lbytes n & state a))
  (requires hash_length a + Seq.length additional_input + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
let generate #a st n additional_input =
  hmac_input_bound a;
  if st.reseed_counter > reseed_interval then 
    None
  else
    let k, v = 
      if Seq.length additional_input > 0 then
        update additional_input st.k st.v 
      else st.k, st.v
    in
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
    let k, v = update additional_input k v in
    Some (output, State k v (st.reseed_counter + 1))

(** Equivalently, but proving it requires proving extensionality of generate_blocks *)
val generate': #a:supported_alg
  -> state a
  -> n:pos{n <= max_output_length}
  -> additional_input: bytes
  -> Pure (option (lbytes n & state a))
  (requires hash_length a + Seq.length additional_input + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
let generate' #a st n additional_input =
  hmac_input_bound a;
  if st.reseed_counter > reseed_interval then 
    None
  else    
    let k, v = 
      if Seq.length additional_input > 0 then
        update additional_input st.k st.v 
      else st.k, st.v
    in
    // let max = ceil (n / hash_length a) in
    let max = (n + hash_length a - 1) / hash_length a in
    let v, output =
      Lib.Sequence.generate_blocks (hash_length a) max max (a_spec a)
        (generate_loop a k max)
        v
    in
    let k, v = update additional_input k v in
    Some (Seq.slice output 0 n, State k v (st.reseed_counter + 1))
