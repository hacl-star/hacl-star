module Hacl.EC.Ladder


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer


open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.EC.AddAndDouble


module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#set-options "--lax"

type uint8_p = buffer H8.t


val cmult_small_loop:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr ->  
  (* nqx:felem -> nqz:felem -> nqpqx:felem -> nqpqz:felem -> *)
  (* nqx2:felem -> nqz2:felem -> nqpqx2:felem -> nqpqz2:felem -> q:felem -> byte:H8.t -> *)
  (* i:U32.t -> *)
  Stack unit
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> true))
(* let rec cmult_small_loop nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q byte i = *)
let rec cmult_small_loop nq nqpq nq2 nqpq2 q byte i =
  let nqx = getx nq in
  let nqz = getz nq in
  let nqpqx = getx nqpq in
  let nqpqz = getz nqpq in
  let nqx2 = getx nq2 in
  let nqz2 = getz nq2 in
  let nqpqx2 = getx nqpq2 in
  let nqpqz2 = getz nqpq2 in
  if (U32 (i =^ 0ul)) then ()
  else (
    let bit = byte_to_limb (H8 (byte >>^ 7ul)) in
    (* swap_conditional nqx nqpqx bit; *)
    (* swap_conditional nqz nqpqz bit; *)
    swap_conditional nq nqpq bit;
    (* fmonty nqx2 nqz2 nqpqx2 nqpqz2 nqx nqz nqpqx nqpqz q; *)
    fmonty nq2 nqpq2 nq nqpq q;
    (* swap_conditional nqx2 nqpqx2 bit; *)
    (* swap_conditional nqz2 nqpqz2 bit; *)
    swap_conditional nq2 nqpq2 bit;
    let t = nqx in
    let nqx = nqx2 in
    let nqx2 = t in
    let t = nqz in
    let nqz = nqz2 in
    let nqz2 = t in
    let t = nqpqx in
    let nqpqx = nqpqx2 in
    let nqpqx2 = t in
    let t = nqpqz in
    let nqpqz = nqpqz2 in
    let nqpqz2 = t in
    let byte = H8 (byte <<^ 1ul) in
    (* cmult_small_loop nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q byte (U32 (i -^ 1ul)) *)
    cmult_small_loop nq nqpq nq2 nqpq2 q byte (U32 (i -^ 1ul))
  )


val cmult_big_loop:
  n:uint8_p{length n = 32} ->
  (* nqx:felem -> nqz:felem -> *)
  (* nqpqx:felem -> nqpqz:felem -> *)
  (* nqx2:felem -> nqz2:felem -> *)
  (* nqpqx2:felem -> nqpqz2:felem -> *)
  nq:felem ->
  nqpq:felem ->
  nq2:felem ->
  nqpq2:felem ->
  q:felem -> i:U32.t ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> true))
(* let rec cmult_big_loop n nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q i = *)
let rec cmult_big_loop n nq nqpq nq2 nqpq2 q i =
  if (U32 (i =^ 0ul)) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byte 8ul;
    cmult_big_loop n nq nqpq nq2 nqpq2 q i
  )


val cmult:
  (* resultx:felem -> resultz:felem -> *)
  result:felem ->
  n:uint8_p{length n = 32} ->
  q:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
    (* (requires (fun h -> live h resultx /\ live h resultz /\ live h n /\ live h q)) *)
    (* (ensures (fun h0 _ h1 -> modifies_2 resultx resultz h0 h1 /\ live h1 resultx /\ live h1 resultz)) *)
let cmult result n q =
  push_frame();
  let buf = create zero 40ul in
  (* let nqpqx  = Buffer.sub buf 0ul  5ul in *)
  (* let nqpqz  = Buffer.sub buf 5ul  5ul in *)
  (* let nqx    = Buffer.sub buf 10ul 5ul in *)
  (* let nqz    = Buffer.sub buf 15ul 5ul in *)
  (* let nqpqx2 = Buffer.sub buf 20ul 5ul in *)
  (* let nqpqz2 = Buffer.sub buf 25ul 5ul in *)
  (* let nqx2   = Buffer.sub buf 30ul 5ul in *)
  (* let nqz2   = Buffer.sub buf 35ul 5ul in *)
  let nqpq  = Buffer.sub buf 0ul  10ul in
  let nq    = Buffer.sub buf 10ul 10ul in
  let nqpq2 = Buffer.sub buf 20ul 10ul in
  let nq2   = Buffer.sub buf 30ul 10ul in
  let nqpqx = getx nqpq in
  let nqpqz = getz nqpq in
  let nqx = getx nq in
  let nqz = getz nq in
  let nqpqx2 = getx nqpq2 in
  let nqpqz2 = getz nqpq2 in
  let nqx2 = getx nq2 in
  let nqz2 = getz nq2 in
  nqpqz.(0ul) <- one;
  nqx.(0ul) <- one;
  nqpqz2.(0ul) <- one;
  nqz2.(0ul) <- one;
  blit q 0ul nqpqx 0ul 5ul;
  (* cmult_big_loop n nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q 32ul; *)
  cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul;
  copy result nq;
  (* blit nqx 0ul resultx 0ul 5ul; *)
  (* blit nqz 0ul resultz 0ul 5ul; *)
  pop_frame()
