module Hacl.Impl.AES_256.Bitsliced

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

// Code inspired by https://bearssl.org/gitweb/?p=BearSSL;a=tree;f=src/symcipher;h=f6bafa0ce21dccda8d4238e18b1df91f7fd9c596;hb=refs/heads/master

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

let state = lbuffer uint64 (size 8)
let state_idx = n:size_t{v n < 8}

val bitslice_sbox: st:state -> Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let bitslice_sbox state =
  let x0 = index state (size 7) in
  let x1 = index state (size 6) in
  let x2 = index state (size 5) in
  let x3 = index state (size 4) in
  let x4 = index state (size 3) in
  let x5 = index state (size 2) in
  let x6 = index state (size 1) in
  let x7 = index state (size 0) in
  (* Top linear transformation *)
  let y14 = x3 ^. x5 in
  let y13 = x0 ^. x6 in
  let y9 = x0 ^. x3 in
  let y8 = x0 ^. x5 in
  let t0 = x1 ^. x2 in
  let y1 = t0 ^. x7 in
  let y4 = y1 ^. x3 in
  let y12 = y13 ^. y14 in
  let y2 = y1 ^. x0 in
  let y5 = y1 ^. x6 in
  let y3 = y5 ^. y8 in
  let t1 = x4 ^. y12 in
  let y15 = t1 ^. x5 in
  let y20 = t1 ^. x1 in
  let y6 = y15 ^. x7 in
  let y10 = y15 ^. t0 in
  let y11 = y20 ^. y9 in
  let y7 = x7 ^. y11 in
  let y17 = y10 ^. y11 in
  let y19 = y10 ^. y8 in
  let y16 = t0 ^. y11 in
  let y21 = y13 ^. y16 in
  let y18 = x0 ^. y16 in
  (* Non-linear section *)
  let t2 = y12 &. y15 in
  let t3 = y3 &. y6 in
  let t4 = t3 ^. t2 in
  let t5 = y4 &. x7 in
  let t6 = t5 ^. t2 in
  let t7 = y13 &. y16 in
  let t8 = y5 &. y1 in
  let t9 = t8 ^. t7 in
  let t10 = y2 &. y7 in
  let t11 = t10 ^. t7 in
  let t12 = y9 &. y11 in
  let t13 = y14 &. y17 in
  let t14 = t13 ^. t12 in
  let t15 = y8 &. y10 in
  let t16 = t15 ^. t12 in
  let t17 = t4 ^. t14 in
  let t18 = t6 ^. t16 in
  let t19 = t9 ^. t14 in
  let t20 = t11 ^. t16 in
  let t21 = t17 ^. y20 in
  let t22 = t18 ^. y19 in
  let t23 = t19 ^. y21 in
  let t24 = t20 ^. y18 in
  let t25 = t21 ^. t22 in
  let t26 = t21 &. t23 in
  let t27 = t24 ^. t26 in
  let t28 = t25 &. t27 in
  let t29 = t28 ^. t22 in
  let t30 = t23 ^. t24 in
  let t31 = t22 ^. t26 in
  let t32 = t31 &. t30 in
  let t33 = t32 ^. t24 in
  let t34 = t23 ^. t33 in
  let t35 = t27 ^. t33 in
  let t36 = t24 &. t35 in
  let t37 = t36 ^. t34 in
  let t38 = t27 ^. t36 in
  let t39 = t29 &. t38 in
  let t40 = t25 ^. t39 in
  let t41 = t40 ^. t37 in
  let t42 = t29 ^. t33 in
  let t43 = t29 ^. t40 in
  let t44 = t33 ^. t37 in
  let t45 = t42 ^. t41 in
  let z0 = t44 &. y15 in
  let z1 = t37 &. y6 in
  let z2 = t33 &. x7 in
  let z3 = t43 &. y16 in
  let z4 = t40 &. y1 in
  let z5 = t29 &. y7 in
  let z6 = t42 &. y11 in
  let z7 = t45 &. y17 in
  let z8 = t41 &. y10 in
  let z9 = t44 &. y12 in
  let z10 = t37 &. y3 in
  let z11 = t33 &. y4 in
  let z12 = t43 &. y13 in
  let z13 = t40 &. y5 in
  let z14 = t29 &. y2 in
  let z15 = t42 &. y9 in
  let z16 = t45 &. y14 in
  let z17 = t41 &. y8 in
  (* Bottom linear transformation *)
  let t46 = z15 ^. z16 in
  let t47 = z10 ^. z11 in
  let t48 = z5 ^. z13 in
  let t49 = z9 ^. z10 in
  let t50 = z2 ^. z12 in
  let t51 = z2 ^. z5 in
  let t52 = z7 ^. z8 in
  let t53 = z0 ^. z3 in
  let t54 = z6 ^. z7 in
  let t55 = z16 ^. z17 in
  let t56 = z12 ^. t48 in
  let t57 = t50 ^. t53 in
  let t58 = z4 ^. t46 in
  let t59 = z3 ^. t54 in
  let t60 = t46 ^. t57 in
  let t61 = z14 ^. t57 in
  let t62 = t52 ^. t58 in
  let t63 = t49 ^. t58 in
  let t64 = z4 ^. t59 in
  let t65 = t61 ^. t62 in
  let t66 = z1 ^. t63 in
  let s0 = t59 ^. t63 in
  let s6 = t56 ^. ~.t62 in
  let s7 = t48 ^. ~.t60 in
  let t67 = t64 ^. t65 in
  let s3 = t53 ^. t66 in
  let s4 = t51 ^. t66 in
  let s5 = t47 ^. t65 in
  let s1 = t64 ^. ~.s3 in
  let s2 = t55 ^. ~.t67 in
  upd state (size 7) s0;
  upd state (size 6) s1;
  upd state (size 5) s2;
  upd state (size 4) s3;
  upd state (size 3) s4;
  upd state (size 2) s5;
  upd state (size 1) s6;
  upd state (size 0) s7

val bitslice_inv_sbox: st:state -> Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let bitslice_inv_sbox state =
  let q0 = ~. (index state (size 0)) in
  let q1 = ~. (index state (size 1)) in
  let q2 = index state (size 2) in
  let q3 = index state (size 3) in
  let q4 = index state (size 4) in
  let q5 = ~. (index state (size 5)) in
  let q6 = ~. (index state (size 6)) in
  let q7 = index state (size 7) in
  upd state (size 7) (q1 ^. q4 ^. q6);
  upd state (size 6) (q0 ^. q3 ^. q5);
  upd state (size 5) (q7 ^. q2 ^. q4);
  upd state (size 4) (q6 ^. q1 ^. q3);
  upd state (size 3) (q5 ^. q0 ^. q2);
  upd state (size 2) (q4 ^. q7 ^. q1);
  upd state (size 1) (q3 ^. q6 ^. q0);
  upd state (size 0) (q2 ^. q5 ^. q7);
  bitslice_sbox state;
  let q0 = ~. (index state (size 0)) in
  let q1 = ~. (index state (size 1)) in
  let q2 = index state (size 2) in
  let q3 = index state (size 3) in
  let q4 = index state (size 4) in
  let q5 = ~. (index state (size 5)) in
  let q6 = ~. (index state (size 6)) in
  let q7 = index state (size 7) in
  upd state (size 7) (q1 ^. q4 ^. q6);
  upd state (size 6) (q0 ^. q3 ^. q5);
  upd state (size 5) (q7 ^. q2 ^. q4);
  upd state (size 4) (q6 ^. q1 ^. q3);
  upd state (size 3) (q5 ^. q0 ^. q2);
  upd state (size 2) (q4 ^. q7 ^. q1);
  upd state (size 1) (q3 ^. q6 ^. q0);
  upd state (size 0) (q2 ^. q5 ^. q7)

inline_for_extraction noextract val swapn: cl:uint64 -> ch:uint64 -> s:rotval U64 -> state:state -> i:state_idx -> j:state_idx -> Stack unit
  (requires (fun h -> live h state))
  (ensures (fun h0 _ h1 -> modifies1 state h0 h1))
inline_for_extraction noextract let swapn cl ch s state i j =
  let a = index state i in
  let b = index state j in
  let x = (a &. cl) |. ((b &. cl) <<. s) in
  let y = ((a &. ch) >>. s) |. (b &. ch) in
  upd state i x;
  upd state j y

val swap2: state:state -> i:state_idx -> j:state_idx -> Stack unit
  (requires (fun h -> live h state))
  (ensures (fun h0 _ h1 -> modifies1 state h0 h1))
let swap2 state i j =
  swapn (u64 0x5555555555555555) (u64 0xAAAAAAAAAAAAAAAA) (size 1)
    state i j

val swap4: state:state -> i:state_idx -> j:state_idx -> Stack unit
  (requires (fun h -> live h state))
  (ensures (fun h0 _ h1 -> modifies1 state h0 h1))
let swap4 state i j =
  swapn (u64 0x3333333333333333) (u64 0xCCCCCCCCCCCCCCCC) (size 2)
    state i j

val swap8: state:state -> i:state_idx -> j:state_idx -> Stack unit
  (requires (fun h -> live h state))
  (ensures (fun h0 _ h1 -> modifies1 state h0 h1))
let swap8 state i j =
  swapn (u64 0x0F0F0F0F0F0F0F0F) (u64 0xF0F0F0F0F0F0F0F0) (size 4)
    state i j

val ortho: state:state -> Stack unit
  (requires (fun h -> live h state))
  (ensures (fun h0 _ h1 -> modifies1 state h0 h1))

#set-options "--z3rlimit 50"

let ortho state =
  swap2 state (size 0) (size 1);
  swap2 state (size 2) (size 3);
  swap2 state (size 4) (size 5);
  swap2 state (size 6) (size 7);

  swap4 state (size 0) (size 2);
  swap4 state (size 1) (size 3);
  swap4 state (size 4) (size 6);
  swap4 state (size 5) (size 7);

  swap8 state (size 0) (size 4);
  swap8 state (size 1) (size 5);
  swap8 state (size 2) (size 6);
  swap8 state (size 3) (size 7)

val interleave_in:
  q0: lbuffer uint64 (size 1) ->
  q1: lbuffer uint64 (size 1) ->
  w: lbuffer uint32 (size 4) ->
  Stack unit
    (requires (fun h -> live h q0 /\ live h q1 /\ live h w /\
      disjoint q0 q1 /\ disjoint q0 w /\ disjoint q1 w
    ))
    (ensures (fun h0 _ h1 -> modifies2 q0 q1 h0 h1))

let interleave_in q0 q1 w =
  let x0 = to_u64 (index w (size 0)) in
  let x1 = to_u64 (index w (size 1)) in
  let x2 = to_u64 (index w (size 2)) in
  let x3 = to_u64 (index w (size 3)) in
  let x0 = x0 |. (x0 <<. size 16) in
  let x1 = x1 |. (x1 <<. size 16) in
  let x2 = x2 |. (x2 <<. size 16) in
  let x3 = x3 |. (x3 <<. size 16) in
  let x0 = x0 &. (u64 0x0000FFFF0000FFFF) in
  let x1 = x1 &. (u64 0x0000FFFF0000FFFF) in
  let x2 = x2 &. (u64 0x0000FFFF0000FFFF) in
  let x3 = x3 &. (u64 0x0000FFFF0000FFFF) in
  let x0 = x0 |. (x0 <<. size 8) in
  let x1 = x1 |. (x1 <<. size 8) in
  let x2 = x2 |. (x2 <<. size 8) in
  let x3 = x3 |. (x3 <<. size 8) in
  let x0 = x0 &. (u64 0x00FF00FF00FF00FF) in
  let x1 = x1 &. (u64 0x00FF00FF00FF00FF) in
  let x2 = x2 &. (u64 0x00FF00FF00FF00FF) in
  let x3 = x3 &. (u64 0x00FF00FF00FF00FF) in
  upd q0 (size 0) (x0 |. (x2 <<. size 8));
  upd q1 (size 0) (x1 |. (x3 <<. size 8))

val interleave_out:
  w: lbuffer uint32 (size 4) ->
  q0: uint64 ->
  q1: uint64 ->
  Stack unit
    (requires (fun h -> live h w))
    (ensures (fun h0 _ h1 -> modifies1 w h0 h1))

let interleave_out w q0 q1 =
  let x0 = q0 &. (u64 0x00FF00FF00FF00FF) in
  let x1 = q1 &. (u64 0x00FF00FF00FF00FF) in
  let x2 = (q0 >>. size 8) &. (u64 0x00FF00FF00FF00FF) in
  let x3 = (q1 >>. size 8) &. (u64 0x00FF00FF00FF00FF) in
  let x0 = x0 |. (x0 >>. size 8) in
  let x1 = x1 |. (x1 >>. size 8) in
  let x2 = x2 |. (x2 >>. size 8) in
  let x3 = x3 |. (x3 >>. size 8) in
  let x0 = x0 &. (u64 0x0000FFFF0000FFFF) in
  let x1 = x1 &. (u64 0x0000FFFF0000FFFF) in
  let x2 = x2 &. (u64 0x0000FFFF0000FFFF) in
  let x3 = x3 &. (u64 0x0000FFFF0000FFFF) in
  upd w (size 0) ((to_u32 x0) |. (to_u32 (x0 >>. size 16)));
  upd w (size 1) ((to_u32 x1) |. (to_u32 (x1 >>. size 16)));
  upd w (size 2) ((to_u32 x2) |. (to_u32 (x2 >>. size 16)));
  upd w (size 3) ((to_u32 x3) |. (to_u32 (x3 >>. size 16)))

inline_for_extraction noextract let rcon_list : l:list uint8{List.Tot.Base.length l = 10} =
  [@inline_let]
  let l =
    [u8 0x01; u8 0x02; u8 0x04; u8 0x08; u8 0x10; u8 0x20; u8 0x40; u8 0x80; u8 0x1B; u8 0x36]
  in
  assert_norm (List.Tot.Base.length l = 10);
  normalize_term(l)

noextract let rcon_seq : Lib.Sequence.lseq uint8 10 = Lib.Sequence.createL rcon_list

let rcon : b:ilbuffer uint8 (size 10){recallable b /\ witnessed b rcon_seq} = createL_global rcon_list

val sub_word: x:uint32 -> Stack uint32
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies0 h0 h1))

let sub_word x =
  push_frame ();
  let q = create (size 8) (u64 0) in
  upd q (size 0) (to_u64 x);
  ortho q;
  bitslice_sbox q;
  ortho q;
  let x = index q (size 0) in
  pop_frame ();
  to_u32 x

val keysched:
  comp_skey: lbuffer uint64 (size 30) ->
  key:lbuffer uint8 (size 32) ->
  Stack unit
    (requires (fun h -> live h comp_skey /\ live h key /\ disjoint comp_skey key))
    (ensures (fun h0 _ h1 -> modifies1 comp_skey h0 h1))

#set-options "--z3rlimit 100"

let keysched comp_skey key =
  let num_rounds = size 14 in
  let nk = size 32 >>. size 2 in
  let nkf = (num_rounds +. size 1) <<. size 2 in
  push_frame ();
  let skey = create #uint32 (size 60) (u32 0) in
  uint32s_from_bytes_le #(size 8) (sub skey (size 0) (size 8)) key;
  (**) let h0 = ST.get () in
  loop_nospec #h0 #uint32 #(size 60) (nkf -. nk) skey (fun i ->
    let i = i +. nk in
    let j = i %. nk in
    let k = i /. nk -. size 1 in
    let tmp = index skey (i -. size 1) in
    let tmp =
      if j = size 0 then
        let tmp = (tmp <<. size 24) |. (tmp >>. size 8) in
	(**) recall_contents rcon rcon_seq;
        let tmp = sub_word tmp ^. (to_u32 (index rcon k)) in
        tmp
      else if j = size 4 then
        let tmp = sub_word tmp in
	tmp
      else
        tmp
    in
    let tmp = tmp ^. index skey (i -. nk) in
    upd skey i tmp
  );
  let q = create (size 8) (u64 0) in
  (**) let h1 = ST.get () in
  loop_nospec3 #h1 #uint64 #uint32 #uint64
    #(size 30) #(size 60) #(size 8)
    (nkf /. size 4) comp_skey skey q (fun i ->
    let j = size 2 *. i in
    let i = size 4 *. i in
    interleave_in
      (sub q (size 0) (size 1))
      (sub q (size 4) (size 1))
      (sub skey i (size 4));
    upd q (size 1) (index q (size 0));
    upd q (size 2) (index q (size 0));
    upd q (size 3) (index q (size 0));
    upd q (size 5) (index q (size 4));
    upd q (size 6) (index q (size 4));
    upd q (size 7) (index q (size 4));
    ortho q;
    let x0 = ((index q (size 0)) &. (u64 0x1111111111111111)) |.
     ((index q (size 1)) &. (u64 0x2222222222222222)) |.
     ((index q (size 2)) &. (u64 0x4444444444444444)) |.
     ((index q (size 3)) &. (u64 0x8888888888888888))
    in
    upd comp_skey j x0;
    let x1 = ((index q (size 4)) &. (u64 0x1111111111111111)) |.
     ((index q (size 5)) &. (u64 0x2222222222222222)) |.
     ((index q (size 6)) &. (u64 0x4444444444444444)) |.
     ((index q (size 7)) &. (u64 0x8888888888888888))
    in
    upd comp_skey (j +. size 1) x1
  );
  pop_frame ();
  ()

val skey_expand:
  skey: lbuffer uint64 (size 120) ->
  comp_skey: lbuffer uint64 (size 30) ->
  Stack unit
    (requires (fun h -> live h skey /\ live h comp_skey /\ disjoint skey comp_skey))
    (ensures (fun h0 _ h1 -> modifies1 skey h0 h1))

let skey_expand skey comp_skey =
  let n = (size 14 +. size 1) <<. size 1 in
  (**) let h0 = ST.get () in
  loop_nospec #h0 #uint64 #(size 120) n skey (fun u ->
    let x0 = index comp_skey u in
    let x1 = x0 in
    let x2 = x0 in
    let x3 = x0 in
    let x0 = x0 &. (u64 0x1111111111111111) in
    let x1 = x1 &. (u64 0x2222222222222222) in
    let x2 = x2 &. (u64 0x4444444444444444) in
    let x3 = x3 &. (u64 0x8888888888888888) in
    let x1 = x1 >>. size 1 in
    let x2 = x2 >>. size 2 in
    let x3 = x3 >>. size 3 in
    upd skey ((u *. size 4) +. size 0) ((x0 <<. size 4) -. x0);
    upd skey ((u *. size 4) +. size 1) ((x1 <<. size 4) -. x1);
    upd skey ((u *. size 4) +. size 2) ((x2 <<. size 4) -. x2);
    upd skey ((u *. size 4) +. size 3) ((x3 <<. size 4) -. x3)
  )

val add_round_key: q:state -> sk:state -> Stack unit
  (requires (fun h -> live h q /\ live h sk /\ disjoint q sk))
  (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let add_round_key q sk =
  upd q (size 0) (index q (size 0) ^. index sk (size 0));
  upd q (size 1) (index q (size 1) ^. index sk (size 1));
  upd q (size 2) (index q (size 2) ^. index sk (size 2));
  upd q (size 3) (index q (size 3) ^. index sk (size 3));
  upd q (size 4) (index q (size 4) ^. index sk (size 4));
  upd q (size 5) (index q (size 5) ^. index sk (size 5));
  upd q (size 6) (index q (size 6) ^. index sk (size 6));
  upd q (size 7) (index q (size 7) ^. index sk (size 7))

val shift_rows: q:state -> Stack unit
  (requires (fun h -> live h q))
  (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let shift_rows q =
  (**) let h0 = ST.get () in
  loop_nospec #h0 #uint64 #(size 8) (size 8) q (fun i ->
    let x = index q i in
    upd q i (x &. (u64 0x000000000000FFFF)
	|. ((x &. (u64 0x00000000FFF00000)) >>. size 4)
	|. ((x &. (u64 0x00000000000F0000)) <<. size 12)
	|. ((x &. (u64 0x0000FF0000000000)) >>. size 8)
	|. ((x &. (u64 0x000000FF00000000)) <<. size 8)
	|. ((x &. (u64 0xF000000000000000)) >>. size 12)
	|. ((x &. (u64 0x0FFF000000000000)) <<. size 4))
  )

val inv_shift_rows: q:state -> Stack unit
  (requires (fun h -> live h q))
  (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let inv_shift_rows q =
  (**) let h0 = ST.get () in
  loop_nospec #h0 #uint64 #(size 8) (size 8) q (fun i ->
    let x = index q i in
    upd q i ((x &. (u64 0x000000000000FFFF))
			|. ((x &. (u64 0x000000000FFF0000)) <<. size 4)
			|. ((x &. (u64 0x00000000F0000000)) >>. size 12)
			|. ((x &. (u64 0x000000FF00000000)) <<. size 8)
			|. ((x &. (u64 0x0000FF0000000000)) >>. size 8)
			|. ((x &. (u64 0x000F000000000000)) <<. size 12)
			|. ((x &. (u64 0xFFF0000000000000)) >>. size 4))
  )


let rotr32 (x: uint64) : Tot uint64 =
  (x <<. size 32) |. (x >>. size 32)

val mix_columns: q:state -> Stack unit
  (requires (fun h -> live h q))
  (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let mix_columns q =
  let q0 = index q (size 0) in
  let q1 = index q (size 1) in
  let q2 = index q (size 2) in
  let q3 = index q (size 3) in
  let q4 = index q (size 4) in
  let q5 = index q (size 5) in
  let q6 = index q (size 6) in
  let q7 = index q (size 7) in
  let r0 = (q0 >>. size 16) |. (q0 <<. size 48) in
  let r1 = (q1 >>. size 16) |. (q1 <<. size 48) in
  let r2 = (q2 >>. size 16) |. (q2 <<. size 48) in
  let r3 = (q3 >>. size 16) |. (q3 <<. size 48) in
  let r4 = (q4 >>. size 16) |. (q4 <<. size 48) in
  let r5 = (q5 >>. size 16) |. (q5 <<. size 48) in
  let r6 = (q6 >>. size 16) |. (q6 <<. size 48) in
  let r7 = (q7 >>. size 16) |. (q7 <<. size 48) in

  upd q (size 0) (q7 ^. r7 ^. r0 ^. rotr32 (q0 ^. r0));
  upd q (size 1) (q0 ^. r0 ^. q7 ^. r7 ^. r1 ^. rotr32 (q1 ^. r1));
  upd q (size 2) (q1 ^. r1 ^. r2 ^. rotr32 (q2 ^. r2));
  upd q (size 3) (q2 ^. r2 ^. q7 ^. r7 ^. r3 ^. rotr32 (q3 ^. r3));
  upd q (size 4) (q3 ^. r3 ^. q7 ^. r7 ^. r4 ^. rotr32 (q4 ^. r4));
  upd q (size 5) (q4 ^. r4 ^. r5 ^. rotr32 (q5 ^. r5));
  upd q (size 6) (q5 ^. r5 ^. r6 ^. rotr32 (q6 ^. r6));
  upd q (size 7) (q6 ^. r6 ^. r7 ^. rotr32 (q7 ^. r7))

val inv_mix_columns: q:state -> Stack unit
  (requires (fun h -> live h q))
  (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let inv_mix_columns q =
  let q0 = index q (size 0) in
  let q1 = index q (size 1) in
  let q2 = index q (size 2) in
  let q3 = index q (size 3) in
  let q4 = index q (size 4) in
  let q5 = index q (size 5) in
  let q6 = index q (size 6) in
  let q7 = index q (size 7) in
  let r0 = (q0 >>. size 16) |. (q0 <<. size 48) in
  let r1 = (q1 >>. size 16) |. (q1 <<. size 48) in
  let r2 = (q2 >>. size 16) |. (q2 <<. size 48) in
  let r3 = (q3 >>. size 16) |. (q3 <<. size 48) in
  let r4 = (q4 >>. size 16) |. (q4 <<. size 48) in
  let r5 = (q5 >>. size 16) |. (q5 <<. size 48) in
  let r6 = (q6 >>. size 16) |. (q6 <<. size 48) in
  let r7 = (q7 >>. size 16) |. (q7 <<. size 48) in
  upd q (size 0) (q5 ^. q6 ^. q7 ^. r0 ^. r5 ^. r7 ^. rotr32 (q0 ^. q5 ^. q6 ^. r0 ^. r5));
  upd q (size 1) (q0 ^. q5 ^. r0 ^. r1 ^. r5 ^. r6 ^. r7 ^. rotr32 (q1 ^. q5 ^. q7 ^. r1 ^. r5 ^. r6));
  upd q (size 2) (q0 ^. q1 ^. q6 ^. r1 ^. r2 ^. r6 ^. r7 ^. rotr32(q0 ^. q2 ^. q6 ^. r2 ^. r6 ^. r7));
  upd q (size 3) (q0 ^. q1 ^. q2 ^. q5 ^. q6 ^. r0 ^. r2 ^. r3 ^. r5 ^. rotr32(q0 ^. q1 ^. q3 ^. q5 ^. q6 ^. q7 ^. r0 ^. r3 ^. r5 ^. r7));
  upd q (size 4) (q1 ^. q2 ^. q3 ^. q5 ^. r1 ^. r3 ^. r4 ^. r5 ^. r6 ^. r7 ^. rotr32(q1 ^. q2 ^. q4 ^. q5 ^. q7 ^. r1 ^. r4 ^. r5 ^. r6));
  upd q (size 5) (q2 ^. q3 ^. q4 ^. q6 ^. r2 ^. r4 ^. r5 ^. r6 ^. r7 ^. rotr32(q2 ^. q3 ^. q5 ^. q6 ^. r2 ^. r5 ^. r6 ^. r7));
  upd q (size 6) (q3 ^. q4 ^. q5 ^. q7 ^. r3 ^. r5 ^. r6 ^. r7 ^. rotr32(q3 ^. q4 ^. q6 ^. q7 ^. r3 ^. r6 ^. r7));
  upd q (size 7) (q4 ^. q5 ^. q6 ^. r4 ^. r6 ^. r7 ^. rotr32 (q4 ^. q5 ^. q7 ^. r4 ^. r7))

val encrypt:
  q:state ->
  skey: lbuffer uint64 (size 120) ->
  Stack unit
    (requires (fun h -> live h q /\ live h skey /\ disjoint q skey))
    (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let encrypt q skey =
  add_round_key q (sub skey (size 0) (size 8));
  (**) let h0 = ST.get () in
  loop_nospec #h0 #uint64 #(size 8) (size 14 -. size 1) q (fun u ->
    let u = u +. size 1 in
    bitslice_sbox q;
    shift_rows q;
    mix_columns q;
    add_round_key q (sub skey (u <<. size 3) (size 8))
  );
  bitslice_sbox q;
  shift_rows q;
  add_round_key q (sub skey ((size 14) <<. size 3) (size 8))

val decrypt:
  q:state ->
  skey: lbuffer uint64 (size 120) ->
  Stack unit
    (requires (fun h -> live h q /\ live h skey /\ disjoint q skey))
    (ensures (fun h0 _ h1 -> modifies1 q h0 h1))

let decrypt q skey =
  add_round_key q (sub skey ((size 14) <<. size 3) (size 8));
  (**) let h0 = ST.get () in
  loop_nospec #h0 #uint64 #(size 8) (size 14 -. size 1) q (fun u ->
    let u = size 13 -. u in
    inv_shift_rows q;
    bitslice_inv_sbox q;
    add_round_key q (sub skey (u <<. size 3) (size 8));
    inv_mix_columns q
  );
  inv_shift_rows q;
  bitslice_inv_sbox q;
  add_round_key q (sub skey (size 0) (size 8))


val update_w_from_ivw_and_plaintext:
  w: lbuffer uint32 (size 4) ->
  ivw: lbuffer uint32 (size 4) ->
  plaintext: buffer uint8 ->
  len: size_t{length plaintext = v len /\ v len % 16 = 0} ->
  i: size_t{ i <. len /. size 16} ->
  Stack unit
    (requires (fun h -> live h w /\ live h ivw /\ live h plaintext /\
      disjoint w ivw /\ disjoint w plaintext
    ))
    (ensures (fun h0 _ h1 -> modifies1 w h0 h1))

let update_w_from_ivw_and_plaintext w ivw plaintext len i =
  upd w (size 0) (index ivw (size 0) ^.
    uint_from_bytes_le (sub #MUT #uint8 #len plaintext ((i *. size 16) +. size 0) (size 4)));
  upd w (size 1) (index ivw (size 1) ^.
    uint_from_bytes_le (sub #MUT #uint8 #len plaintext ((i *. size 16) +. size 4) (size 4)));
  upd w (size 2) (index ivw (size 2) ^.
    uint_from_bytes_le (sub #MUT #uint8 #len plaintext ((i *. size 16) +. size 8) (size 4)));
  upd w (size 3) (index ivw (size 3) ^.
    uint_from_bytes_le (sub #MUT #uint8 #len plaintext ((i *. size 16) +. size 12) (size 4)))

val update_out_from_w:
  w: lbuffer uint32 (size 4) ->
  out: buffer uint8 ->
  len: size_t{length out = v len /\ v len % 16 = 0} ->
  i: size_t{ i <. len /. size 16} ->
  Stack unit
    (requires (fun h -> live h w /\ live h out /\
      disjoint w out
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let update_out_from_w w out len i =
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i *. size 16) +. size 0) (size 4)) (index w (size 0));
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i *. size 16) +. size 4) (size 4)) (index w (size 1));
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i *. size 16) +. size 8) (size 4)) (index w (size 2));
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i*. size 16) +. size 12) (size 4)) (index w (size 3))


(** Loop combinator with just memory safety specification *)
inline_for_extraction noextract
val loop_nospec4:
    #h0:mem
  -> #a1:Type0
  -> #a2:Type0
  -> #a3:Type0
  -> #a4:Type0
  -> #len1:size_t
  -> #len2:size_t
  -> #len3:size_t
  -> #len4:size_t
  -> n:size_t
  -> buf1:lbuffer a1 len1
  -> buf2:lbuffer a2 len2
  -> buf3:lbuffer a3 len3
  -> buf4:lbuffer a4 len4
  -> impl: (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> modifies4 buf1 buf2 buf3 buf4 h0 h)
      (ensures  fun _ _ h1 -> modifies4 buf1 buf2 buf3 buf4 h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h0 buf1 /\ live h0 buf2 /\ live h0 buf3 /\ live h0 buf4)
    (ensures  fun _ _ h1 -> modifies4 buf1 buf2 buf3 buf4 h0 h1)

let loop_nospec4 #h0 #a1 #a2 #a3 #a4 #len1 #len2 #len3 #len4 n buf1 buf2 buf3 buf4 impl =
  let inv h1 j =
    modifies (union (loc buf4) (union (loc buf3) (union (loc buf1) (loc buf2)))) h0 h1
  in
  Lib.Loops.for (size 0) n inv impl

val encrypt_blocks_cbc:
  out: buffer uint8 ->
  key: lbuffer uint8 (size 32) ->
  iv: lbuffer uint8 (size 16) ->
  plaintext: buffer uint8 ->
  len: size_t{length out = v len /\ length plaintext = v len /\ v len % 16 = 0} ->
  Stack unit
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h plaintext /\
      disjoint out key /\ disjoint out iv /\ disjoint out plaintext
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

#set-options "--z3rlimit 200"

let encrypt_blocks_cbc out key iv plaintext len =
  push_frame ();
  let sk_exp = create (size 120) (u64 0) in
  let ivw = create (size 4) (u32 0) in
  let skey = create (size 30) (u64 0) in
  keysched skey key;
  skey_expand sk_exp skey;
  uint32s_from_bytes_le ivw iv;
  let w = create (size 4) (u32 0) in
  let q = create (size 8) (u64 0) in
  (**) let h0 = ST.get () in
  loop_nospec4 #h0
    #uint32 #uint32 #uint64 #uint8
    #(size 4) #(size 4) #(size 8) #len
    (len /. (size 16)) w ivw q out (fun i ->
    update_w_from_ivw_and_plaintext w ivw plaintext len i;
    interleave_in (sub q (size 0) (size 1)) (sub q (size 4) (size 1)) w;
    ortho q;
    encrypt q sk_exp;
    ortho q;
    interleave_out w (index q (size 0)) (index q (size 4));
    copy ivw w;
    update_out_from_w w out len i
  );
  pop_frame ();
  ()

val update_out_from_ivw_w:
  w: lbuffer uint32 (size 4) ->
  ivw: lbuffer uint32 (size 4) ->
  out: buffer uint8 ->
  len: size_t{length out = v len /\ v len % 16 = 0} ->
  i: size_t{ i <. len /. size 16} ->
  Stack unit
    (requires (fun h -> live h w /\ live h out /\ live h ivw /\
      disjoint w out /\ disjoint ivw out
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let update_out_from_ivw_w w ivw out len i =
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i *. size 16) +. size 0) (size 4))
    (index w (size 0) ^. index ivw (size 0));
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i *. size 16) +. size 4) (size 4))
    (index w (size 1) ^. index ivw (size 1));
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i *. size 16) +. size 8) (size 4))
    (index w (size 2) ^. index ivw (size 2));
  uint_to_bytes_le #U32 #SEC
    (sub #MUT #uint8 #len out ((i*. size 16) +. size 12) (size 4))
    (index w (size 3) ^. index ivw (size 3))

val decrypt_blocks_cbc:
  out: buffer uint8 ->
  key: lbuffer uint8 (size 32) ->
  iv: lbuffer uint8 (size 16) ->
  plaintext: buffer uint8 ->
  len: size_t{length out = v len /\ length plaintext = v len /\ v len % 16 = 0} ->
  Stack unit
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h plaintext /\
      disjoint out key /\ disjoint out iv /\ disjoint out plaintext
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let decrypt_blocks_cbc out key iv ciphertext len =
  push_frame ();
  let sk_exp = create (size 120) (u64 0) in
  let ivw = create (size 4) (u32 0) in
  let skey = create (size 30) (u64 0) in
  keysched skey key;
  skey_expand sk_exp skey;
  uint32s_from_bytes_le ivw iv;
  let w = create (size 4) (u32 0) in
  let q = create (size 8) (u64 0) in
  (**) let h0 = ST.get () in
  loop_nospec4 #h0
    #uint32 #uint32 #uint64 #uint8
    #(size 4) #(size 4) #(size 8) #len
    (len /. (size 16)) w ivw q out (fun i ->
    let cip_block = sub #MUT #uint8 #len ciphertext (i *. size 16) (size 16) in
    uint32s_from_bytes_le w cip_block;
    interleave_in (sub q (size 0) (size 1)) (sub q (size 4) (size 1)) w;
    ortho q;
    decrypt q sk_exp;
    ortho q;
    interleave_out w (index q (size 0)) (index q (size 4));
    update_out_from_ivw_w w ivw out len i;
    uint32s_from_bytes_le ivw cip_block
  );
  pop_frame ()
