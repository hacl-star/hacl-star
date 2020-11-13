module Spec.Dilithium.Verify

open Spec.Dilithium.Debug
open Spec.Dilithium.Params
open Spec.Dilithium.Stream
open Spec.Dilithium.Poly
open Spec.Dilithium.Packing
open Spec.Dilithium.NTT

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module SHA3 = Spec.SHA3


(* pass this to repati, partial apply to get a function i -> s -> s *)
val wrap_option: #t:Type -> n:size_nat -> f:(i:nat{i<n} -> option t)
  -> i:nat{i<n} -> option (lseq t n) -> Tot (option (lseq t n))

let wrap_option #t n f i s =
  match s with
  | None -> None
  | Some s' -> match f i with
    | None -> None
    | Some x -> Some (s'.[i] <- x)


(**** rejection sampling ****)

let append_nonce (#seed_size: size_nat{seed_size+2 < max_size_t}) (seed: lbytes seed_size) (nonce: uint16) =
  (seed @| (uint_to_bytes_le #U16 nonce))


(* rejection sampling from a fixed buffer, starting from an index i
yields sampled poly & total number of filled coefficients *)
type rej_sampler =
    p: poly
  -> i: size_nat // position in p
  -> buflen: size_nat
  -> buf: lbytes buflen
  -> j: nat {j <= buflen} // position in buf
  -> Tot (poly & size_nat) (decreases (buflen-j))


(* In the ref code, rejection sampling processes chunk_size bytes at a time.
if stream_rate % chunk_size != 0, then `off' bytes are left over each time,
and the unused bytes (rem) are passed to the next iteration. *)
val feed_rej_from_stream:
    shake: stream_t
  -> rej_fun: rej_sampler
  -> chunk_size: size_nat{chunk_size > 0 /\ chunk_size <= stream_rate shake}
  -> stream: SHA3.state
  -> p: poly
  -> i: size_nat {i < param_n}
  -> max_iters: nat
  -> off: size_nat{off < stream_rate shake}
  -> rem: lbytes off
  -> Tot (option poly) (decreases max_iters)

let rec feed_rej_from_stream shake rej_fun chunk_size stream p i max_iters off rem =
  if max_iters = 0 then None else
    let buflen:size_nat = stream_rate shake + off in
    let stream, buf = stream_squeeze shake stream 1 in
    let buf: lbytes buflen = rem @| buf in
    eq_intro (sub buf 0 off) rem;
    let p, i = rej_fun p i buflen buf 0 in
    let off = buflen % chunk_size in
    let rem = sub buf (buflen-off) off in
    if i >= param_n
      then Some p
      else feed_rej_from_stream shake rej_fun chunk_size stream p i (max_iters-1) off rem


val rej_uniform:
    p: poly
  -> i: size_nat
  -> buflen: size_nat
  -> buf: lbytes buflen
  -> j: nat{j<=buflen}
  -> Tot (poly & size_nat) (decreases (buflen-j))

let rec rej_uniform p i buflen buf j =
  if i >= param_n || (j+3) > buflen
    then p, i
  else
    let t = bytes3_to_u32 buf.[j] buf.[j+1] buf.[j+2] in
    let t = t &. u32 0x7FFFFF in
    let p,i = if v t < param_q then (p.[i] <- t), (i+1) else p, i in
    rej_uniform p i buflen buf (j+3)


// we should probably prove this is bounded by |p| < gamma1

val rej_uniform_gamma1m1:
    p: poly
  -> i: size_nat
  -> buflen: size_nat
  -> buf: lbytes buflen
  -> j: nat{j<=buflen}
  -> Tot (poly & size_nat) (decreases (buflen-j))

let rec rej_uniform_gamma1m1 p i buflen buf j =
  // from the ref: ``rej_gamma1m1() assumes GAMMA1 - 1 fits in 19 bits''
  assert(gamma1 <= 0x80000);
  if i >= param_n || (j+5) > buflen
    then p, i
  else
    let t0 = bytes3_to_u32 buf.[j] buf.[j+1] buf.[j+2] in
    let t0 = t0 &. u32 0xFFFFF in
    let t1 = (bytes3_to_u32 buf.[j+2] buf.[j+3] buf.[j+4]) >>. size 4 in
    let offset = u32 (param_q + gamma1 - 1) in
    let bound = 2*gamma1 - 2 in
    let (i:size_nat),p = if v t0 <= bound then i+1, (p.[i] <- (offset -. t0)) else i,p in
    let i,p = if v t1 <= bound && i < param_n then i+1, (p.[i] <- (offset -. t1)) else i,p in
    rej_uniform_gamma1m1 p i buflen buf (j+5)


val rej_eta:
    p: poly
  -> i: size_nat
  -> buflen: size_nat
  -> buf: lbytes buflen
  -> j: nat{j<=buflen}
  -> Tot (poly & size_nat) (decreases (buflen-j))

let rec rej_eta p i buflen buf j =
  // from the ref: ``rej_gamma1m1() assumes GAMMA1 - 1 fits in 19 bits''
  assert(eta <= 7);
  // eta > 3 for now
  assert (eta > 3);
  if i >= param_n || j = buflen
    then p, i
  else begin
    let t0 = buf.[j] &. u8 (0x0f) in
    let t1 = buf.[j] >>. size 4 in
    let p, (i:nat{i<=param_n}) = if (v t0 <= 2*eta)
      then (p.[i] <- (u32 (param_q + eta) -. to_u32 t0)), i+1
      else p, i in
    let p, (i:nat{i<=param_n}) = if (v t0 <= 2*eta && i < param_n)
      then (p.[i] <- (u32 (param_q + eta) -. to_u32 t1)), i+1
      else p, i in
    rej_eta p i buflen buf (j+1)
  end


val poly_from_sampling:
    shake: stream_t
  -> rej_sampler
  -> chunk_size: size_nat{0 < chunk_size /\ chunk_size < stream_rate shake}
  -> seed_size: size_nat{seed_size + 2 < max_size_t}
  -> lbytes seed_size
  -> uint16
  -> Tot (option poly)

let poly_from_sampling shake sampler chunk_size seed_size seed nonce =
  let stream = stream_absorb shake new_stream (seed_size+2) (append_nonce seed nonce) in
  feed_rej_from_stream shake sampler chunk_size stream new_poly 0 iter_cap 0 new_bytes


(* these are the actual functions to be used *)
let poly_uniform = poly_from_sampling Shake128 rej_uniform 3 seedbytes
let poly_uniform_gamma1m1 = poly_from_sampling Shake256 rej_uniform_gamma1m1 5 crhbytes
let poly_uniform_eta = poly_from_sampling Shake128 rej_eta 1 seedbytes


(**** Challenge ****)

let challenge_buflen = crhbytes + param_k * polyw1_packedbytes

// sample
let rec challenge_inner max_iters i (buf: lbytes challenge_buflen) state (position: size_nat):
            Tot (option (lbytes challenge_buflen & SHA3.state & x:size_nat{x<challenge_buflen}))
                (decreases max_iters) =
            if max_iters <= 0 then None
            else
              let (buf, state), position =
                if position >= shake256_rate
                then let state, sh_out = shake256_squeeze state 1 in
                  ((update_sub buf 0 shake256_rate sh_out), state), 0
                else (buf, state), position in
              (assert(position < shake256_rate /\ position < challenge_buflen);
              let b = buf.[position] in
                if v b > i
                then challenge_inner (max_iters-1) i buf state (position + 1)
                else Some (buf, state, position))


val challenge: mu: lbytes crhbytes -> w1: polyveck {polyveck_is_4bit w1} -> option poly

let challenge mu w1 =
  // packing mu and w1 into buf
  let buf: lbytes challenge_buflen = (create challenge_buflen (u8 0)) in
  let buf = update_sub buf 0 crhbytes mu in
  let buf = repeati param_k (fun i buf ->
              update_sub buf (crhbytes + (i * polyw1_packedbytes)) polyw1_packedbytes (polyw1_pack w1.[i])) buf in
  // seed state
  let state = shake256_absorb new_stream challenge_buflen buf in
  let state, sh_out = shake256_squeeze state 1 in
  let buf = update_sub buf 0 shake256_rate sh_out in
  let signs = repeati 8 (fun i signs -> signs |. ((to_u64 buf.[i]) <<. size (8*i))) (u64 0) in
  let c = new_poly in
  let position = 8 in
  match
    repeat_range 196 256
      (fun i args ->
        match args with
        | None -> None
        | Some (buf, state, position, signs, c) ->
        let (x: (option (lbytes challenge_buflen & SHA3.state & x:size_nat{x<challenge_buflen})))
          = challenge_inner iter_cap i buf state position in
        match x with
        | None -> None
        | Some (buf, state, position) ->
        let _ = assert(position < challenge_buflen) in
        let b:size_nat = v   buf.[position] in
        let c:poly = c.[i] <- c.[b] in
        // ref:  c[b] = 1 ^ (-((uint32_t)signs & 1) & (1 ^ (Q-1)));
        let c = c.[b] <- if (v signs) % 2 = 1 then u32 (param_q-1) else u32 1 in
        let signs = signs >>. size 1 in
        Some (buf, state, position+1, signs, c))
      (Some (buf, state, position, signs, c)) with
  | Some (_, _, _, _, c) -> Some c
  | None -> None


val expand_mat: rho: lbytes seedbytes -> option (lseq polyvecl param_k)

let expand_mat rho =
  repeati param_k
    (wrap_option param_k (fun i ->
      repeati param_l
        (wrap_option param_l (fun j ->
          let nonce = (((u16 i) <<. size 8) +. (u16 j)) in
          poly_uniform rho nonce))
        (Some new_polyvecl)))
    (Some (create param_k new_polyvecl))


#set-options "--fuel 1 --ifuel 1 --z3rlimit 300"

val verify:
    pk: lbytes pkbytes
  -> sig: lbytes crypto_bytes
  -> mlen: size_nat {crypto_bytes + mlen < max_size_t}
  -> m: lbytes mlen
  -> bool // true if verifies correctly

let verify pk sig mlen m =
  let rho, t1 = unpack_pk pk in
  match unpack_sig sig with
  | None -> false
  | Some (z, h, c) ->
  if not (fa (fun (p:poly) -> fa (fun (x:uint32) -> v x < param_q) p) z) then false else
  let _ = assert (forall i. fa (fun (x:uint32) -> v x < param_q) z.[i]) in
  let _ = assert (polyvecl_is_stdreps z) in
  if polyvecl_chknorm z (gamma1 - beta) then false else
  let mu = SHA3.shake256 pkbytes pk crhbytes in
  let mu = SHA3.shake256 (crhbytes+mlen) (mu@|m) crhbytes in
  let mat = expand_mat rho in
  match mat with
  | None -> false
  | Some mat ->
  let z = polyvecl_ntt z in
  let w1 = createi param_k (fun i -> polyvecl_pointwise_acc mat.[i] z) in
  let c' = ntt c in
  let t1 = polyveck_shiftl t1 in
  let t1 = polyveck_ntt t1 in
  let t1 = map (fun x -> poly_pointwise_mont c' x) t1 in
  let w1 = polyveck_sub w1 t1 in
  let w1 = polyveck_modq w1 in
  let w1 = polyveck_intt_tomont w1 in
  let w1 = polyveck_modq w1 in
  let w1 = polyveck_use_hint w1 h in



  let c' = challenge mu w1 in
  match c' with
  | None -> false
  | Some c' ->
  repeati param_n (fun i result -> result && (v c.[i] = v c'.[i])) true


val polyveck_from_option_inner:
  n:size_nat -> i:nat{i<n} -> lseq poly n -> (j:nat{j < n} -> option poly)
  -> Tot (option (lseq poly n)) (decreases (n-i))

let rec polyveck_from_option_inner n i vec f =
  match f i with
  | None -> None
  | Some p -> if i+1 >= n then Some (vec.[i] <- p) else
    polyveck_from_option_inner n (i+1) (vec.[i] <- p) f

let polyveck_from_option (n:size_nat{n>0}) f =
  polyveck_from_option_inner n 0 (create n new_poly) f


val keygen: lbytes (3*seedbytes) -> option (lbytes pkbytes & lbytes skbytes)

let keygen rand_seed =
  let rho = sub rand_seed 0 seedbytes in
  let rho' = sub rand_seed seedbytes seedbytes in
  let key = sub rand_seed (2*seedbytes) seedbytes in
  let mat = expand_mat rho in
  match mat with
  | None -> None
  | Some mat ->
  let s1 = polyveck_from_option param_l (fun i -> poly_uniform_eta rho' (u16 i)) in
  match s1 with
  | None -> None
  | Some s1 ->
  let s2 = polyveck_from_option param_k (fun i -> poly_uniform_eta rho' (u16 (param_l + i))) in
  match s2 with
  | None -> None
  | Some s2 ->
  let s1hat = polyvecl_ntt s1 in
  let t1 = createi param_k (fun i -> intt_tomont (poly_reduce (polyvecl_pointwise_acc mat.[i] s1hat))) in
  let t1 = polyveck_add t1 s2 in
  let t1 = polyveck_freeze t1 in
  let t0, t1 = polyveck_power2_round t1 in
  let pk = pack_pk rho t1 in
  let tr = crh pkbytes pk in
  let sk = pack_sk rho key tr s1 s2 t0 in
  Some (pk, sk)
