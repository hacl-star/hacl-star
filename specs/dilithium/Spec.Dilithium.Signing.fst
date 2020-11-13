module Spec.Dilithium.Signing
open Spec.Dilithium.Debug
open Spec.Dilithium.Params
open Spec.Dilithium.Stream
open Spec.Dilithium.Poly
open Spec.Dilithium.Packing
open Spec.Dilithium.NTT
open Spec.Dilithium.Verify
open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
module SHA3 = Spec.SHA3

val poly_make_hint: a0:poly -> a1:poly -> poly & nat

let poly_make_hint a0 a1 =
  repeati param_n (fun i ((p,n):poly&nat) ->
      let (h:nat) = make_hint a0.[i] a1.[i] in
      let p = p.[i] <- u32 h in
      p, n+h)
    (new_poly, 0)


val polyveck_make_hint':
    i: nat{i < param_k}
  -> h: polyveck
  -> n: nat{n = polyveck_partial_popcount h i 0}
  -> v0: polyveck
  -> v1: polyveck
  -> Tot (hn:(polyveck & nat) {let h,n = hn in n = polyveck_popcount h}) (decreases (param_k-i))

let rec polyveck_make_hint' i h n v0 v1 =
  let p, m = poly_make_hint v0.[i] v1.[i] in
  let h = h.[i] <- p in
  let n = polyveck_partial_popcount h i param_n in
  if i+1 = param_k then h,n else polyveck_make_hint' (i+1) h n v0 v1


let polyveck_make_hint = polyveck_make_hint' 0 new_polyveck 0


(* if this function fails to check with an "unknown assertion failed",
  try increasing fuel temporarily to get a better error message *)
#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

val signature_inner:
    nonce: uint16
  -> mu: lbytes crhbytes
  -> rho': lbytes crhbytes
  -> mat: lseq polyvecl param_k
  -> s1: polyvecl
  -> s2: polyveck
  -> t0: polyveck
  -> Tot (option (lbytes crypto_bytes)) (decreases (0xffff - (v nonce)))

let rec signature_inner nonce mu rho' mat s1 s2 t0 =
  // makes sure nonce doesnt overflow + guarantees termination
  // i am 99% sure its ok to branch on nonce, but it's a deviation from the ref code, so...
  if (v nonce) + param_l >= 0xffff then None else
  let y:option polyvecl = repeati #(option polyvecl) param_l
    (wrap_option param_l (fun i -> poly_uniform_gamma1m1 rho' (nonce +. u16 i)))
    (Some new_polyvecl) in
  match y with
  | None -> None
  | Some y ->
  let nonce = nonce +. u16 param_l in
  let yhat = polyvecl_ntt y in
  let w = repeati param_k
    (fun i w -> let ppa = polyvecl_pointwise_acc mat.[i] yhat in
      let reduced = poly_modq ppa in
      let intted = intt_tomont reduced in
      w.[i] <- intted
    )
    new_polyveck in
  let w = polyveck_modq w in
  let w = polyveck_modq w in
  let w0, w1 = polyveck_decompose w in
  assert (polyveck_is_4bit w1);
  let c = challenge mu w1 in
  match c with
  | None -> None
  | Some c ->
  let chat = ntt c in
  let z = repeati param_l (fun i z ->
    z.[i] <- intt_tomont (poly_pointwise_mont chat s1.[i]))
    new_polyvecl in
  let z = polyvecl_add z y in
  let (z:polyvecl{polyvecl_is_stdreps z}) = polyvecl_freeze z in
  if polyvecl_chknorm z (gamma1-beta) then
      signature_inner nonce mu rho' mat s1 s2 t0 // reject
  else
  let _ = assert (not (polyvecl_chknorm z (gamma1 - beta))) in
  let _ = assert (polyvecl_norm_bound z (gamma1-beta+1)) in
  let cs2 = repeati param_k (fun i cs2 ->
    cs2.[i] <- intt_tomont (poly_pointwise_mont chat s2.[i]))
    new_polyveck in
  let w0 = polyveck_sub w0 cs2 in
  let w0 = polyveck_freeze w0 in
  if polyveck_chknorm w0 (gamma2-beta) then
      signature_inner nonce mu rho' mat s1 s2 t0 // reject
  else  (* compute hints *)
  let ct0 = repeati param_k (fun i ct0 ->
    ct0.[i] <- intt_tomont (poly_pointwise_mont chat t0.[i]))
    new_polyveck in
  let ct0 = polyveck_modq ct0 in
  if polyveck_chknorm ct0 gamma2 then
      signature_inner nonce mu rho' mat s1 s2 t0 // reject
  else
  let w0 = polyveck_add w0 ct0 in
  let w0 = polyveck_modq w0 in
  let h, n = polyveck_make_hint w0 w1 in
  assert(n = polyveck_popcount h);
  if n > omega
    then signature_inner nonce mu rho' mat s1 s2 t0 // reject
  else
  let sig = pack_sig z h c in
  Some sig


val signature:
    sk: lbytes skbytes
  -> mlen: size_nat{mlen + crhbytes < max_size_t}
  -> m: lbytes mlen
  -> option (lbytes crypto_bytes)

let signature sk mlen m =
  let (rho, key, tr, s1, s2, t0) = unpack_sk sk in
  let mu = crh (crhbytes+mlen) (tr@|m) in //SHA3.shake256 (crhbytes+mlen) (tr@|m) crhbytes in
  let key = key @| mu in
  let rho':lbytes crhbytes = SHA3.shake256 (crhbytes + seedbytes) key crhbytes in
  let mat = expand_mat rho in
  match mat with
  | None -> None
  | Some mat ->
  let s1 = polyvecl_ntt s1 in
  let s2 = polyveck_ntt s2 in
  let t0 = polyveck_ntt t0 in
  signature_inner (u16 0) mu rho' mat s1 s2 t0


val sign:
    sk: lbytes skbytes
  -> mlen: size_nat {crypto_bytes + mlen < max_size_t}
  -> m: lbytes mlen
  -> option (lbytes (crypto_bytes + mlen))

let sign sk mlen m =
  match signature sk mlen m with
  | None -> None
  | Some sig -> Some (sig @| m)