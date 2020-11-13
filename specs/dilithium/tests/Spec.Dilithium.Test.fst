module Spec.Dilithium.Test

open FStar.All
open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes

open Spec.Dilithium.NTT
open Spec.Dilithium.Packing
open Spec.Dilithium.Params
open Spec.Dilithium.Poly
open Spec.Dilithium.Stream
open Spec.Dilithium.Signing
open Spec.Dilithium.Verify
open Lib.LoopCombinators
open Lib.PrintSequence

open Spec.Dilithium.Test0

module SHA3 = Spec.SHA3


let to_stdout str = IO.print_string ("echo to stdout:\n" ^ str ^ "\n")


val print_seq: #t:inttype -> #l:secrecy_level -> n:size_nat -> s: lseq (int_t t l) n -> ML unit

let print_seq #t #l n s =
  let rec print_seq_inner (s: lseq (int_t t l) n) (i:size_nat) : ML unit =
    if i < n then
      (IO.print_string ((string_of_int (v s.[i])) ^ " ");
      print_seq_inner s (i+1))
    else IO.print_string "\n"
  in print_seq_inner s 0


let print_int n =
  IO.print_string (string_of_int n);
  IO.print_string "\n"


val foreach_ml: #a:Type -> n:size_nat -> s:lseq a n -> (f:a->ML unit) -> ML unit

let foreach_ml #a n s f = repeati_all_ml n (fun i _ -> (f s.[i])) ()


let print_poly (p: poly): ML unit =
  print_seq param_n p


(* generates a random sequence to use as test inputs from SHAKE-128.
  Just pass it a unique seed, it doesn't matter what it is
  The number of integers generated can be inferred from type checking *)

val rand_seq: #t:inttype{unsigned t /\ ~(U1? t)}
              -> #n:nat{n*16 < max_size_t}
              -> seed: nat{seed < maxint U64}
              -> lseq (uint_t t SEC) n

let rand_seq #t #n seed =
  let bt = numbytes t in
  let buf = SHA3.shake128 8 (uint_to_bytes_le (u64 seed)) (n*bt) in
  let result = (create n (zeros t SEC)) in
  repeati n (fun i result ->
    result.[i] <-
      let b: lbytes (numbytes t) = (sub buf (i*bt) bt) in
      uint_from_bytes_le #t #SEC b)
    result


// tbh i thought this would be a lot shorter
val rand_seq_mod: #t:inttype{unsigned t /\ ~(U1? t) /\ ~(U128? t)}
              -> #n:nat{n*16 < max_size_t}
              -> seed: nat{seed < maxint U64}
              -> modulus:int{0 < modulus /\ modulus <= maxint t}
              //-> Tot (lseq (x:(uint_t t SEC){v x < modulus}) n)
              -> Tot (s:(lseq (uint_t t SEC) n){forall (i:nat{i<n}).{:pattern s.[i]} v s.[i]<modulus})

let rand_seq_mod #t #n seed modulus =
  let r = rand_seq #t #n seed in
  let tl = uint_t t SEC in
  map #tl #tl #n (fun (x:tl) ->
    let _ = assert(((sec_int_v #t x) % modulus) < modulus) in
    uint #t #SEC ((sec_int_v #t x) % modulus)) r


let test_ntt () : ML unit =
  IO.print_string "ntt\n";
  let p:poly = rand_seq 0x4EA in
  print_poly p;
  print_poly (ntt p);
  print_poly (intt_tomont p)

let test_sha3 () : ML unit =
  IO.print_string "sha3\n";
  let seed:(lbytes seedbytes) = (rand_seq 0xCECCAC) in
  let nonce = u16 48646 in
  let state = stream_absorb Shake128 new_stream (seedbytes+2) (append_nonce seed nonce) in
  let state, digest = stream_squeeze Shake128 state 1 in
  print_seq (seedbytes+2) (append_nonce seed nonce);
  print_seq shake128_rate digest;
  let state = stream_absorb Shake256 new_stream (seedbytes+2) (append_nonce seed nonce) in
  let state, digest = stream_squeeze Shake256 state 1 in
  print_seq shake256_rate digest


(*
let test_eta () : ML unit =
  IO.print_string "eta\n";
  let rec fill_seed (seed: lbytes seedbytes) (i: size_nat) : Tot (lbytes seedbytes) (decreases %[seedbytes-i]) =
    if i < seedbytes
      then let _ = seed.[i] <- u8 (i % 11) in fill_seed seed (i + 1)
      else seed
  in
  let seed = fill_seed (create seedbytes (u8 0)) 0 in
  let nonce = u16 5 in
  (match poly_eta_uniform seed nonce with
  | None -> IO.print_string "sampling failed \n"
  | Some p -> print_poly p)
*)

let test_challenge () : ML unit =
  IO.print_string "chal\n";
  let (w1:polyveck {polyveck_is_4bit w1}) = repeati param_k
    (fun i (w1:polyveck {polyveck_is_4bit w1}) ->
      let (p:poly{poly_is_4bit p}) = rand_seq_mod #U32 #param_n (0xB175+i) 16 in
      assert (poly_is_4bit p);
      let w1' = (w1.[i] <- p) in
      assert (forall (i:nat{i < param_k}). (w1'.[i] == w1.[i] \/ w1'.[i] == p));
      w1')
    new_polyveck in
  //assert (forall i. i < param_k ==> poly_is_4bit w1.[i]);
  //assert (polyveck_is_4bit w1);
  let mu:(lbytes crhbytes) = (rand_seq 0xC0EFF1CE75) in
  let _ = print_seq crhbytes mu in
  let _ = foreach_ml param_k w1 print_poly in
  (match challenge mu w1 with
  | None -> IO.print_string "sampling failed \n"
  | Some p -> print_poly p)


let test_polymul () =
  IO.print_string "pmul\n";
  (* (x^2+3x)(2x^3+5x^2+x) = 2x^5+11x^4+16x^3+3x^2 *)
  let a = new_poly in
  let a = a.[1] <- u32 3 in
  let a = a.[2] <- u32 1 in
  print_seq param_n a;
  let b = new_poly.[1] <- u32 1 in
  let b = b.[2] <- u32 5 in
  let b = b.[3] <- u32 2 in
  print_seq param_n b;
  print_seq param_n (poly_poly_mul a b)


let test_decompose_and_hint () =
  IO.print_string "hint\n";
  let vec = new_polyveck in
  let p:poly = rand_seq 0xDEC0F05E in
  let vec = vec.[0] <- p in
  print_poly p;
  let v0, v1 = polyveck_decompose vec in
  print_poly v0.[0];
  print_poly v1.[0];
  let p,n = (poly_make_hint v0.[0] v1.[0]) in
  print_poly p


let test_rej () =
  IO.print_string "rej\n";
  let rho1:(lbytes seedbytes) = rand_seq_mod 0x753BC 255 in
  let rho2:(lbytes crhbytes) = rand_seq_mod 0x476AD 255 in
  let nonce1 = u16 1776 in
  let nonce2 = u16 1783 in
  print_seq seedbytes rho1;
  print_seq crhbytes rho2;
  print_int (v nonce1);
  print_int (v nonce2);
  let p1 = poly_uniform rho1 nonce1 in
  let p2 = poly_uniform_gamma1m1 rho2 nonce2 in
  match p1, p2 with
  | (Some p1), (Some p2) ->
    (print_poly p1;
    print_poly p2)
  | _ -> (IO.print_string "Rej_uniform failed\n")


let test_signature () =
  IO.print_string "sign\n";
  //let sk_len:size_nat = List.Tot.length test0_sk in
  // assert_norm (List.Tot.length test0_sk = skbytes);
  let sk: lbytes skbytes = test0_sk in
  let pk: lbytes pkbytes = test0_pk in
  let mlen = test0_mlen in
  // assert_norm (List.Tot.length test0_message = mlen);
  let m: lbytes mlen = test0_message in
  let sm = sign sk mlen m in
  let smlen = crypto_bytes + mlen in
  // IO.print_string "signed message:\n";
  match sm with
  | None -> IO.print_string "signing failed [end]\n"
  | Some sm -> begin
    //
    let sig = sub sm 0 crypto_bytes in
    let _ = if verify pk sig mlen m then
      IO.print_string "verify passed [end]\n"
    else IO.print_string "verify failed [end]\n" in
    print_seq smlen sm
    end


let test_pack () =
  IO.print_string "pack\n";
  let p:poly = rand_seq_mod (1969-07-20) 16 in
  assert (poly_is_4bit p);
  print_poly p;
  print_seq polyw1_packedbytes (polyw1_pack p)


let test_unpack () =
  IO.print_string "unpack\n";
  // assert_norm (List.Tot.length test0_sk = skbytes);
  let sk: lbytes skbytes = test0_sk in
  let (rho, key, tr, s1, s2, t0) = unpack_sk sk in
  print_seq seedbytes rho

#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

let test () : ML bool =
  // IO.print_string "___Dilithium Test___\n";
  // test_ntt ();
  // test_sha3 ();
  // test_polymul ();
  // test_rej ();
  // test_pack ();
  // test_unpack ();
  // test_challenge ();
  test_signature ();
  IO.print_string "end\n";
  true


