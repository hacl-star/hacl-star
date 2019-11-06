module Hacl.Test.HMAC_DRBG

open FStar.HyperStack.ST
open Test.Lowstarize

open Lib.IntTypes

open Hacl.HMAC_DRBG
open Spec.HMAC_DRBG.Test.Vectors

module D = Spec.Hash.Definitions
module L = Test.Lowstarize
module B = LowStar.Buffer

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* FStar.Reflection only supports up to 8-tuples *)
noextract
let vectors_tmp = List.Tot.map 
  (fun x -> x.a, h x.entropy_input, h x.nonce, h x.personalization_string, 
         h x.entropy_input_reseed, h x.additional_input_reseed,
         (h x.additional_input_1, h x.additional_input_2),
         h x.returned_bits)
  test_vectors

%splice[vectors_low] (lowstarize_toplevel "vectors_tmp" "vectors_low")

// Cheap alternative to friend Lib.IntTypes needed because Test.Lowstarize uses UInt8.t
assume val declassify_uint8: squash (uint8 == UInt8.t)

let vec8 = L.lbuffer UInt8.t

let vector = D.hash_alg & vec8 & vec8 & vec8 & vec8 & vec8 & (vec8 & vec8) & vec8

// This could replace TestLib.compare_and_print
val compare_and_print: b1:B.buffer UInt8.t -> b2:B.buffer UInt8.t -> len:UInt32.t 
  -> Stack bool
  (requires fun h0 -> B.live h0 b1 /\ B.live h0 b2 /\ B.length b1 == v len /\ B.length b2 == v len)
  (ensures  fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
let compare_and_print b1 b2 len =
  push_frame();
  LowStar.Printf.(printf "Expected: %xuy\n" len b1 done);
  LowStar.Printf.(printf "Computed: %xuy\n" len b2 done);
  let b = Lib.ByteBuffer.lbytes_eq #len b1 b2 in
  if b then 
    LowStar.Printf.(printf "PASS\n" done)
  else
    LowStar.Printf.(printf "FAIL\n" done);
  pop_frame();
  b

let test_one (vec:vector) : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let a, 
      LB entropy_input_len entropy_input, 
      LB nonce_len nonce,
      LB personalization_string_len personalization_string,
      LB entropy_input_reseed_len entropy_input_reseed,
      LB additional_input_reseed_len additional_input_reseed,
      (LB additional_input_1_len additional_input_1,
       LB additional_input_2_len additional_input_2),
      LB returned_bits_len returned_bits = vec 
  in
  B.recall entropy_input;
  B.recall nonce;
  B.recall personalization_string;
  B.recall entropy_input_reseed;
  B.recall additional_input_reseed;
  B.recall additional_input_1;
  B.recall additional_input_2;  
  B.recall returned_bits;
  // We need to check this at runtime because Low*-ized vectors don't carry any refinements
  if not (Spec.Agile.HMAC.is_supported_alg a &&
          min_length a <=. entropy_input_len && 
          entropy_input_len <=. max_length &&
          min_length a /. 2ul <=. nonce_len && 
          nonce_len <=. max_length &&
          personalization_string_len <=. max_personalization_string_length &&
          min_length a <=. entropy_input_reseed_len && 
          entropy_input_reseed_len <=. max_length &&
          additional_input_reseed_len <=. max_additional_input_length &&
          additional_input_1_len <=. max_additional_input_length &&
          additional_input_2_len <=. max_additional_input_length &&
          0ul <. returned_bits_len && 
          returned_bits_len <=. max_output_length)
  then C.exit (-1l)
  else
    begin
    push_frame();
    let output = B.alloca (u8 0) returned_bits_len in
    let st = alloca a in
    instantiate a st 
      entropy_input_len entropy_input 
      nonce_len nonce
      personalization_string_len personalization_string;
    reseed a st 
      entropy_input_reseed_len entropy_input_reseed
      additional_input_reseed_len additional_input_reseed;
    let ok = generate a output st returned_bits_len 
      additional_input_1_len additional_input_1
    in
    if ok then
      let ok = generate a output st returned_bits_len 
        additional_input_2_len additional_input_2 
      in
      if ok then
        let ok = compare_and_print returned_bits output returned_bits_len in
        if ok then ()
        else C.exit 1l
      else C.exit 1l
    else C.exit 1l;
    pop_frame()
    end

inline_for_extraction noextract
let test_many #a (label:C.String.t) 
  (f:a -> Stack unit (fun _ -> True) (fun _ _ _ -> True)) (vec: L.lbuffer a) 
=
  C.String.print label;
  C.String.(print !$"\n");
  let L.LB len vs = vec in
  let f (i:UInt32.t{0 <= v i /\ v i < v len}): Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
  =
    let open LowStar.BufferOps in
    B.recall vs;
    LowStar.Printf.(printf "HMAC-DRBG Test %ul/%ul\n" (i +! 1ul) len done);
    f vs.(i)
  in
  C.Loops.for 0ul len (fun _ _ -> True) f

let main () : St C.exit_code =
  test_many C.String.(!$"[HMAC_DRBG]") test_one vectors_low;
  C.EXIT_SUCCESS
