module Spec.Dilithium.Packing

open Spec.Dilithium.Params
open Spec.Dilithium.Poly
open Spec.Dilithium.Packing2

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators



(****************    Packing    ****************)

val polyw1_pack: p:poly {poly_is_4bit p}
  -> lbytes polyw1_packedbytes

let polyw1_pack p =
  let r = create polyw1_packedbytes (u8 0) in
  repeati (param_n/2) (fun i r -> r.[i] <- to_u8 (p.[2*i] |. (p.[2*i+1] <<. size 4))) r


let polyeta_pack (p:poly) : lbytes polyeta_packedbytes =
  (*** requires eta > 3***)
  assert (eta > 3);
  assert (polyeta_packedbytes = param_n/2);
  createi polyeta_packedbytes (fun i ->
    let t0 = u32 (param_q + eta) -. p.[2*i+0] in
    let t1 = u32 (param_q + eta) -. p.[2*i+1] in
    to_u8 t0 |. to_u8 (t1 <<. size 4))


let polyeta_unpack (a:lbytes polyeta_packedbytes) : poly =
  assert (eta > 3);
  let r = (create param_n (u32 0)) in
    repeati (param_n / 2) (fun i r ->
      let r = r.[2*i+0] <- to_u32 (a.[i] &. (u8 0x0F)) in
      let r = r.[2*i+1] <- to_u32 (a.[i] >>. (size 4)) in
      let r = r.[2*i+0] <- u32 (param_q + eta - v r.[2*i+0]) in
      r.[2*i+1] <- u32 (param_q + eta - v r.[2*i+1])
    ) r


let polyt0_pack (p:poly) : lbytes polyt0_packedbytes =
  assert (param_d = 14);
  let r = create polyt0_packedbytes (u8 0) in
  repeati (param_n/8) (fun i r ->
    let t0 = u32 (param_q + (pow2 (param_d-1))) -. p.[4*i+0] in
    let t1 = u32 (param_q + (pow2 (param_d-1))) -. p.[4*i+1] in
    let t2 = u32 (param_q + (pow2 (param_d-1))) -. p.[4*i+2] in
    let t3 = u32 (param_q + (pow2 (param_d-1))) -. p.[4*i+3] in
    let r = r.[7*i+0]  <-  to_u8 (t0) in
    let r = r.[7*i+1]  <-  to_u8 (t0 >>. size 8 |. t1 <<. size 6) in
    let r = r.[7*i+2]  <-  to_u8 (t1 >>. size 2) in
    let r = r.[7*i+3]  <-  to_u8 (t1 >>. size 10 |. t2 <<. size 4) in
    let r = r.[7*i+4]  <-  to_u8 (t2 >>. size 4) in
    let r = r.[7*i+5]  <-  to_u8 (t2 >>. size 12 |. t3 <<. size 2) in
    let r = r.[7*i+6]  <-  to_u8 (t3 >>. size 6) in
    r) r


let polyt0_unpack (a:lbytes polyt0_packedbytes) : poly =
  assert (param_n / 4 + 3 < param_n);
  assert (param_n < max_size_t);
  let r = new_poly in
    repeati (param_n / 4) (fun i r ->
      let a0 = to_u32 a.[7*i+0] in
      let a1 = to_u32 a.[7*i+1] in
      let a2 = to_u32 a.[7*i+2] in
      let a3 = to_u32 a.[7*i+3] in
      let a4 = to_u32 a.[7*i+4] in
      let a5 = to_u32 a.[7*i+5] in
      let a6 = to_u32 a.[7*i+6] in

      let r = r.[4*i+0] <- (a0 |. (a1 <<. size 8)) &. u32 0x3FFF in
      let r = r.[4*i+1] <- (a1 >>. size 6 |. a2 <<. size 2 |. a3 <<. size 10) &. u32 0x3FFF in
      let r = r.[4*i+2] <- (a3 >>. size 4 |. a4 <<. size 4 |. a5 <<. size 12) &. u32 0x3FFF in
      let r = r.[4*i+3] <-  a5 >>. size 2 |. a6 <<. size 6 in

      let x = (u32 param_q) +. ((u32 1) <<. size (param_d-1)) in
      let r = r.[4*i+0] <- x -. r.[4*i+0] in
      let r = r.[4*i+1] <- x -. r.[4*i+1] in
      let r = r.[4*i+2] <- x -. r.[4*i+2] in
      let r:poly = r.[4*i+3] <- x -. r.[4*i+3] in
      r
    ) r


#set-options "--fuel 2 --ifuel 2 --z3rlimit 300"

let polyt1_unpack (a:lbytes polyt1_packedbytes) : poly =
  repeati (param_n/8) (fun i p ->
    let p = p.[8*i+0] <- (to_u32 (a.[9*i+0] >>. size 0) |. (to_u32 a.[9*i+1] <<. size 8)) &. u32 0x1FF in
    let p = p.[8*i+1] <- (to_u32 (a.[9*i+1] >>. size 1) |. (to_u32 a.[9*i+2] <<. size 7)) &. u32 0x1FF in
    let p = p.[8*i+2] <- (to_u32 (a.[9*i+2] >>. size 2) |. (to_u32 a.[9*i+3] <<. size 6)) &. u32 0x1FF in
    let p = p.[8*i+3] <- (to_u32 (a.[9*i+3] >>. size 3) |. (to_u32 a.[9*i+4] <<. size 5)) &. u32 0x1FF in
    let p = p.[8*i+4] <- (to_u32 (a.[9*i+4] >>. size 4) |. (to_u32 a.[9*i+5] <<. size 4)) &. u32 0x1FF in
    let p = p.[8*i+5] <- (to_u32 (a.[9*i+5] >>. size 5) |. (to_u32 a.[9*i+6] <<. size 3)) &. u32 0x1FF in
    let p = p.[8*i+6] <- (to_u32 (a.[9*i+6] >>. size 6) |. (to_u32 a.[9*i+7] <<. size 2)) &. u32 0x1FF in
    let p = p.[8*i+7] <- (to_u32 (a.[9*i+7] >>. size 7) |. (to_u32 a.[9*i+8] <<. size 1)) &. u32 0x1FF in
    p) new_poly


let bytes3_to_u32 (b1:uint8) (b2:uint8) (b3:uint8) : (x:uint32{v x <= 0xffffff}) =
  let b1 = to_u32 b1 in
  assert (v b1 <= 0xff);
  let b2 = (to_u32 b2) <<. size 8 in
  assert (v b1 <= 0xff00);
  let b3 = (to_u32 b3) <<. size 16 in
  assert (v b1 <= 0xff0000);
  logor_disjoint b1 b2 8; // b1 | b2 = b1 + b2
  let x = b1 |. b2 in
  logor_disjoint x b3 16; // x | b3 = x + b3
  x |. b3


val polyz_pack: p:poly {poly_norm_bound p gamma1} -> (r:lbytes polyz_packedbytes)

let polyz_pack p =
  assert(gamma1 <= 0x80000);
  repeati (param_n/2)
    (fun i r ->
      assert (norm_q (v p.[2*i+0]) < gamma1);
      let t0 = map_2gamma1 p.[2*i+0] in
      let t1 = map_2gamma1 p.[2*i+1] in
      let r = r.[5*i+0] <- to_u8 t0 in
      let r = r.[5*i+1] <- to_u8 (t0 >>. size 8) in
      let r = r.[5*i+2] <- to_u8 (t0 >>. size 16 |. t1 <<. size 4) in
      let r = r.[5*i+3] <- to_u8 (t1 >>. size 4) in
      let r = r.[5*i+4] <- to_u8 (t1 >>. size 12) in
      r)
    (create polyz_packedbytes (u8 0))


val polyz_unpack: (a:lbytes polyz_packedbytes) -> p:poly

let polyz_unpack a =
  assert(gamma1 <= 0x80000);
  repeati (param_n/2)
    (fun i p ->
      let p0 = (bytes3_to_u32 a.[5*i+0] a.[5*i+1] a.[5*i+2]) in
      logand_le p0 (u32 0xfffff);
      let p0 =  p0 &. u32 0xfffff in
      let p1 = (bytes3_to_u32 a.[5*i+2] a.[5*i+3] a.[5*i+4]) in
      shift_right_lemma p1 (size 4);
      let p1 = p1 >>. size 4 in
      let p = p.[2*i + 0] <- map_2gamma1 p0 in
              p.[2*i + 1] <- map_2gamma1 p1)
    new_poly


val make_hint: a0:uint32 -> a1:uint32 -> h:nat{h = 0 \/ h = 1}

let make_hint a0 a1 =
  if v a0 <= gamma2 || v a0 > param_q - gamma2 || (v a0 = param_q - gamma2 && v a1 = 0)
  then 0 else 1


val polyveck_partial_popcount: vec:polyveck -> i:nat{i<param_k} -> j:nat{j<=param_n} -> nat

let rec polyveck_partial_popcount vec i j =
  match i, j with
  | 0, 0 -> 0
  | _, 0 -> polyveck_partial_popcount vec (i-1) param_n
  | _, _ -> (if v vec.[i].[j-1] = 0 then 0 else 1) + polyveck_partial_popcount vec i (j-1)


val lemma_polyveck_popcount_monotone:
  vec:polyveck
  -> h:nat{h<param_k}
  -> i:nat{i<=param_n}
  -> j:nat{j<param_k}
  -> k:nat{k<=param_n}
  -> Lemma (requires (h < j \/ (h = j /\ i <= k)))
      (ensures polyveck_partial_popcount vec h i <= polyveck_partial_popcount vec j k)

let rec lemma_polyveck_popcount_monotone vec h i j k =
  if h = j && i = k
    then ()
  else if k = 0
    then lemma_polyveck_popcount_monotone vec h i (j-1) param_n
    else lemma_polyveck_popcount_monotone vec h i j (k-1)


let polyveck_popcount vec = polyveck_partial_popcount vec (param_k-1) param_n



val unpack_h':
    k': nat {k' <= omega + param_k}
  -> j: nat {j < k'}
  -> packed_h:lbytes (omega + param_k)
  -> p:poly{poly_bound p 2}
  -> Tot (option (p': poly {poly_bound p' 2})) (decreases (k' - j))

let rec unpack_h' k' j packed_h p =
  lemma_seq_assignment_predicate p (v packed_h.[j]) (u32 1) (fun x -> v x < 2);
  let p = p.[v packed_h.[j]] <- u32 1 in
  if j+1 < k' then
    if v packed_h.[j+1] <= v packed_h.[j] then None
    else unpack_h' k' (j+1) packed_h p
  else Some p


// #set-options "--fuel 2 --ifuel 2 --z3rlimit 300"
val unpack_h:
    i: nat{i < param_k}
  -> k: nat
  -> h:polyveck{polyveck_bound h 2}
  -> packed_h:lbytes (omega + param_k)
  -> Tot (option (h':polyveck{polyveck_bound h' 2})) (decreases (param_k - i))

let rec unpack_h i k h packed_h =
  let k' = v packed_h.[omega+i] in
  if k' < k || k' > omega then None else
  let hi =
    if k = k' then Some h.[i]
    else unpack_h' k' k packed_h h.[i] in
  match hi with
  | None -> None
  | Some hi ->
  begin
  assert (poly_bound hi 2);
  lemma_seq_assignment_predicate h i hi (fun x -> poly_bound x 2);
  let (h:polyveck{polyveck_bound h 2}) = h.[i] <- hi in
  if i+1 = param_k then Some h else unpack_h (i+1) k' h packed_h
  end




val pack_hint':
    h:polyveck{polyveck_popcount h <= omega}
  -> i:nat{i<param_k}
  -> j:nat{j<=param_n}
  -> packed_h: lbytes (omega + param_k)
  -> k: nat{k <= polyveck_partial_popcount h i j}
  -> Tot (lbytes (omega+param_k)) (decreases %[(param_k-1)-i;param_n-j])

let rec pack_hint' h i j packed_h k =
  lemma_polyveck_popcount_monotone h i j (param_k-1) param_n;
  assert(polyveck_partial_popcount h i j <= polyveck_popcount h);
  if j = param_n
    then (let packed_h = (packed_h.[omega+i] <- u8 k) in
      (if i = (param_k-1) then packed_h else (pack_hint' h (i+1) 0 packed_h k)))
  else begin
    assert(j < param_n);
    // is it ok to branch on this?
    if v h.[i].[j] = 0
    then pack_hint' h i (j+1) packed_h k
    else begin
      assert (polyveck_partial_popcount h i (j+1) = 1 + polyveck_partial_popcount h i j);
      assert (k+1 <= polyveck_partial_popcount h i (j+1));
      assert(k < polyveck_partial_popcount h i (j+1));
      lemma_polyveck_popcount_monotone h i (j+1) (param_k-1) param_n;
      assert(polyveck_partial_popcount h i (j+1) <= omega);
      pack_hint' h i (j+1) (packed_h.[k] <- (u8 j)) (k+1)
    end
  end


val pack_hint: h:polyveck{polyveck_popcount h <= omega} -> lbytes (omega+param_k)

let pack_hint h =
  let packed_h: lbytes (omega+param_k) = (create (omega + param_k) (u8 0)) in
  pack_hint' h 0 0 packed_h 0


val pack_sig: z:polyvecl{polyvecl_norm_bound z gamma1} -> h:polyveck{polyveck_popcount h <= omega} -> c:poly -> lbytes crypto_bytes

let pack_sig z h c =
  assert (crypto_bytes = param_l*polyz_packedbytes + omega + param_k + param_n/8 + 8);
  let packed_z = (create (param_l*polyz_packedbytes) (u8 0)) in
  let packed_h = pack_hint h in
  let packed_c = (create (param_n/8 + 8) (u8 0)) in
  let (packed_z:(lbytes (param_l*polyz_packedbytes))) = repeati param_l (fun i sig ->
    update_sub sig (i*polyz_packedbytes) polyz_packedbytes (polyz_pack z.[i]))
    packed_z in
  let packed_c, signs, _ = repeati (param_n/8) (fun i (packed_c, signs, mask) ->
    let (x:uint8), signs, mask = repeati 8
      (fun j (x, signs, mask) ->
        // is this public enough to branch on?
        if v c.[8*i+j] = 0 then (x, signs, mask) else
          let x = x |. (u8 1 <<. size j) in
          let signs = if v c.[8*i+j] = param_q-1 then signs |. mask else signs in
          let mask = mask <<. size 1 in
          x, signs, mask)
      (u8 0, signs, mask) in
    (packed_c.[i] <- x), signs, mask)
    (packed_c, u64 0, u64 1) in
  let (packed_c: lbytes (param_n/8 + 8)) = repeati 8 (fun i packed_c ->
    packed_c.[param_n/8 + i] <- to_u8 (signs >>. size (8*i))) packed_c in
  assert(length packed_z = param_l*polyz_packedbytes);
  assert(length packed_h = omega + param_k);
  packed_z @| packed_h @| packed_c


val pack_sk:
    rho: lbytes seedbytes
  -> key: lbytes seedbytes
  -> tr: lbytes crhbytes
  -> s1: polyvecl
  -> s2: polyveck
  -> t0: polyveck -> lbytes skbytes

let pack_sk rho key tr s1 s2 t0 =
  let packed_s1 : lbytes (param_l * polyeta_packedbytes) =
    generate_blocks_simple polyeta_packedbytes param_l param_l (fun i -> polyeta_pack s1.[i]) in
  let packed_s2 : lbytes (param_k * polyeta_packedbytes) =
    generate_blocks_simple polyeta_packedbytes param_k param_k (fun i -> polyeta_pack s2.[i]) in
  let packed_t0 : lbytes (param_k * polyt0_packedbytes) =
    generate_blocks_simple polyt0_packedbytes param_k param_k (fun i -> polyt0_pack t0.[i]) in
  rho @| key @| tr
  @| packed_s1 @| packed_s2 @| packed_t0


val unpack_sk: sk: lbytes skbytes ->
  (lbytes seedbytes) & (lbytes seedbytes) & (lbytes crhbytes)
  & polyvecl & polyveck & polyveck

let unpack_sk sk =
  let rho = sub sk 0 seedbytes in
  let key = sub sk seedbytes seedbytes in
  let tr = sub sk (seedbytes + seedbytes) crhbytes in
  let i = seedbytes + seedbytes + crhbytes in
  let s1 = repeati param_l
    (fun (j:nat{j<param_l}) vec ->
      vec.[j] <- polyeta_unpack (sub sk (i+j*polyeta_packedbytes) polyeta_packedbytes))
    new_polyvecl in
  let i = i + param_l * polyeta_packedbytes in
  let s2 = repeati param_k
    (fun (j:nat{j<param_k}) vec -> vec.[j] <- polyeta_unpack (sub sk (i+j*polyeta_packedbytes) polyeta_packedbytes))
    new_polyveck in
  let i = i + param_k * polyeta_packedbytes in
  let t = repeati param_k
    (fun (j:nat{j<param_k}) vec -> vec.[j] <- polyt0_unpack (sub sk (i+j*polyt0_packedbytes) polyt0_packedbytes))
    new_polyveck in
  rho, key, tr, s1, s2, t


let pack_pk (rho: lbytes seedbytes) (t1: polyveck) : lbytes pkbytes =
  assert (pkbytes = seedbytes + param_k * polyt1_packedbytes);
  let packed_t1: lbytes (param_k * polyt1_packedbytes) =
    generate_blocks_simple polyt1_packedbytes param_k param_k (fun i -> polyt1_pack t1.[i]) in
  rho @| packed_t1



let unpack_pk (pk: lbytes pkbytes) =
  assert (seedbytes + polyt1_packedbytes * param_k <= pkbytes);
  let rho = sub pk 0 seedbytes in
  let t = repeati param_k
    (fun (j:nat{j<param_k}) vec -> vec.[j] <- polyt1_unpack (sub pk (seedbytes+j*polyt1_packedbytes) polyt1_packedbytes))
    new_polyveck in
  rho, t


let unpack_sig (sig:lbytes crypto_bytes) =
  assert (crypto_bytes = (param_l * polyz_packedbytes) + (omega + param_k) + (param_n/8 + 8));
  let (z:polyvecl) = createi param_l (fun j -> polyz_unpack (sub sig (j*polyz_packedbytes) polyz_packedbytes)) in
  let packed_h = sub sig (param_l * polyz_packedbytes) (omega + param_k) in
  let h = unpack_h 0 0 new_polyveck packed_h in
  match h with
  | None -> None
  | Some h ->
  let packed_c = sub sig (param_l * polyz_packedbytes + omega + param_k) (param_n/8 + 8) in
  let signs = repeati 8 (fun i signs -> signs |. (to_u64 packed_c.[param_n/8 + i]) <<. size (8*i)) (u64 0) in
  if v (signs >>. size 60) > 0 then None else
    let c, _ = repeati (param_n / 8) (fun i (c, signs) ->
      repeati 8 (fun j (c, signs) ->
        if v ((packed_c.[i] >>. size j) &. u8 0x01) = 1 then
          let c = c.[8*i + j] <- to_u32 (u64 1 ^. ((u64 0 -. (signs &. u64 1)) &. ((u64 1) ^. (u64 (param_q - 1))))) in
          let signs = signs >>. size 1 in
          c, signs
        else c, signs) (c, signs)) (new_poly,signs) in
  Some (z, h, c)