module Hacl.Impl.AES.Bitsliced

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.Buffer
open Lib.Buffer.Lemmas

module ST = FStar.HyperStack.ST
module S = Lib.Sequence


///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
let op_String_Access #a #len m b = as_lseq #a #len b m


inline_for_extraction let size_block : size_nat = 16
inline_for_extraction let size_key : size_nat = 32
inline_for_extraction let size_key_w : size_nat = 16
inline_for_extraction let size_nonce : size_nat = 12
inline_for_extraction let size_state : size_nat = 16
inline_for_extraction let size_transpose : size_nat = 8

let block_t = lbuffer uint8 size_block
let key_t = lbuffer uint8 size_key
let key_w = lbuffer uint16 size_key_w
let nonce_t = lbuffer uint8 size_nonce
let state_t = lbuffer uint8 size_state
let transpose_t = lbuffer uint16 size_transpose


val to_transpose_step_right: uint8 -> i:size_t{v i < 8} -> j:size_t{v j < 16} -> Tot uint8
let to_transpose_step_right w i j =
  let is8 : shiftval U8 = size_to_uint32 i in
  let js8 : shiftval U8 = size_to_uint32 j in
  (w &. ((u8 1) <<. is8)) >>. (is8 -. js8)


val to_transpose_step_left: uint8 -> i:size_t{v i < 8} -> j:size_t{v j < 16} -> Tot uint8
let to_transpose_step_left w i j =
  let is8 : shiftval U8 = size_to_uint32 i in
  let js8 : shiftval U8 = size_to_uint32 j in
  (w &. ((u8 1) <<. is8)) <<. (is8 -. js8)


val to_transpose_step: output:transpose_t -> input:state_t -> i:size_t{v i < 8} -> j:size_t{v j < 16} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let to_transpose_step output input i j =
  let output_i : uint16 = output.(i) in
  let input_j : uint8 = input.(j) in
  let output_nv =
    if (i >. j) then
      output_i ^. (to_u16 #U8 (to_transpose_step_right input_j i j))
    else
      output_i ^. (to_u16 #U8 (to_transpose_step_left input_j i j))
  in
  upd output i output_nv


val to_transpose_loop_inner: output:transpose_t -> input:state_t -> i:size_t{v i < 8} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let to_transpose_loop_inner output input i =
  let h0 = ST.get () in
  loop_nospec #h0 (size 16) output
    (fun j -> to_transpose_step output input i j)


val to_transpose_loop: output:transpose_t -> input:state_t ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let to_transpose_loop output input =
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) output
    (fun i -> to_transpose_loop_inner output input i)


val to_transpose: output:transpose_t -> input:state_t ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let to_transpose output input =
  loop_set output (size 0) (size 16) (u16 0);
  to_transpose_loop output input


val from_transpose_step_right: uint16 -> i:size_t{v i < 16} -> j:size_t{v j < 8} -> Tot uint16
let from_transpose_step_right w i j =
  let i16 : shiftval U16 = size_to_uint32 i in
  let j16 : shiftval U16 = size_to_uint32 j in
  (w &. ((u16 1) <<. i16)) >>. (i16 -. j16)


val from_transpose_step_left: uint16 -> i:size_t{v i < 16} -> j:size_t{v j < 8} -> Tot uint16
let from_transpose_step_left w i j =
  let i16 : shiftval U16 = size_to_uint32 i in
  let j16 : shiftval U16 = size_to_uint32 j in
  (w &. ((u16 1) <<. i16)) <<. (i16 -. j16)


val from_transpose_step: state_t -> transpose_t -> i:size_t{v i < 16} -> j:size_t{v j < 8} ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let from_transpose_step output input i j =
  let output_i : uint8 = output.(i) in
  let input_j : uint16 = input.(j) in
  let output_nv =
    if (i >. j) then
      output_i ^. (to_u8 #U16 (from_transpose_step_right input_j i j))
    else
      output_i ^. (to_u8 #U16 (from_transpose_step_left input_j i j))
  in
  upd output i output_nv

val from_transpose_loop_inner: state_t -> transpose_t -> i:size_t{v i < 8} ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let from_transpose_loop_inner output input i =
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) output
    (fun j -> from_transpose_step output input i j)


val from_transpose_loop: state_t -> transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let from_transpose_loop output input =
  let h0 = ST.get () in
  loop_nospec #h0 (size 16) output
    (fun i -> from_transpose_loop_inner output input i)


val from_transpose: state_t -> transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let from_transpose output input =
  loop_set output (size 0) (size 16) (u8 0);
  from_transpose_loop output input


val sub_bytes: transpose_t ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let sub_bytes st =
  let u0 = st.(size 7) in
  let u1 = st.(size 6) in
  let u2 = st.(size 5) in
  let u3 = st.(size 4) in
  let u4 = st.(size 3) in
  let u5 = st.(size 2) in
  let u6 = st.(size 1) in
  let u7 = st.(size 0) in

  let t1 = u6 ^. u4 in
  let t2 = u3 ^. u0 in
  let t3 = u1 ^. u2 in
  let t6 = u1 ^. u5 in
  let t7 = u0 ^. u6 in
  let t13 = u2 ^. u5 in
  let t16 = u0 ^. u5 in
  let t18 = u6 ^. u5 in

  let t4 = u7 ^. t3 in
  let t5 = t1 ^. t2 in
  let t8 = t1 ^. t6 in
  let t9 = u6 ^. t4 in

  let t10 = u3 ^. t4 in
  let t11 = u7 ^. t5 in
  let t12 = t5 ^. t6 in
  let t14 = t3 ^. t5 in
  let t15 = u5 ^. t7 in
  let t17 = u7 ^. t8 in
  let t19 = t2 ^. t18 in
  let t22 = u0 ^. t4 in
  let t54 = t2 &. t8 in
  let t50 = t9 &. t4 in

  let t20 = t4 ^. t15 in
  let t21 = t1 ^. t13 in
  let t39 = t21 ^. t5 in
  let t40 = t21 ^. t7 in
  let t41 = t7 ^. t19 in
  let t42 = t16 ^. t14 in
  let t43 = t22 ^. t17 in
  let t44 = t19 &. t5 in
  let t45 = t20 &. t11 in
  let t47 = t10 &. u7 in
  let t57 = t16 &. t14 in

  let t46 = t12 ^. t44 in
  let t48 = t47 ^. t44 in
  let t49 = t7 &. t21 in
  let t51 = t40 ^. t49 in
  let t52 = t22 &. t17 in
  let t53 = t52 ^. t49 in

  let t55 = t41 &. t39 in
  let t56 = t55 ^. t54 in
  let t58 = t57 ^. t54 in
  let t59 = t46 ^. t45 in
  let t60 = t48 ^. t42 in
  let t61 = t51 ^. t50 in
  let t62 = t53 ^. t58 in
  let t63 = t59 ^. t56 in
  let t64 = t60 ^. t58 in
  let t65 = t61 ^. t56 in
  let t66 = t62 ^. t43 in
  let t67 = t65 ^. t66 in
  let t68 = t65 &. t63 in
  let t69 = t64 ^. t68 in
  let t70 = t63 ^. t64 in
  let t71 = t66 ^. t68 in
  let t72 = t71 &. t70 in
  let t73 = t69 &. t67 in
  let t74 = t63 &. t66 in
  let t75 = t70 &. t74 in
  let t76 = t70 ^. t68 in
  let t77 = t64 &. t65 in
  let t78 = t67 &. t77 in
  let t79 = t67 ^. t68 in
  let t80 = t64 ^. t72 in
  let t81 = t75 ^. t76 in
  let t82 = t66 ^. t73 in
  let t83 = t78 ^. t79 in
  let t84 = t81 ^. t83 in
  let t85 = t80 ^. t82 in
  let t86 = t80 ^. t81 in
  let t87 = t82 ^. t83 in
  let t88 = t85 ^. t84 in
  let t89 = t87 &. t5 in
  let t90 = t83 &. t11 in
  let t91 = t82 &. u7 in
  let t92 = t86 &. t21 in
  let t93 = t81 &. t4 in
  let t94 = t80 &. t17 in
  let t95 = t85 &. t8 in
  let t96 = t88 &. t39 in
  let t97 = t84 &. t14 in
  let t98 = t87 &. t19 in
  let t99 = t83 &. t20 in
  let t100 = t82 &. t10 in
  let t101 = t86 &. t7 in
  let t102 = t81 &. t9 in
  let t103 = t80 &. t22 in
  let t104 = t85 &. t2 in
  let t105 = t88 &. t41 in
  let t106 = t84 &. t16 in
  let t107 = t104 ^. t105 in
  let t108 = t93 ^. t99 in
  let t109 = t96 ^. t107 in
  let t110 = t98 ^. t108 in
  let t111 = t91 ^. t101 in
  let t112 = t89 ^. t92 in
  let t113 = t107 ^. t112 in
  let t114 = t90 ^. t110 in
  let t115 = t89 ^. t95 in
  let t116 = t94 ^. t102 in
  let t117 = t97 ^. t103  in
  let t118 = t91 ^. t114 in
  let t119 = t111 ^. t117 in
  let t120 = t100 ^. t108 in
  let t121 = t92 ^. t95 in
  let t122 = t110 ^. t121 in
  let t123 = t106 ^. t119 in
  let t124 = t104 ^. t115 in
  let t125 = t111 ^. t116 in
  upd st (size 7) (t109 ^. t122);
  upd st (size 5) (lognot (t123 ^. t124));
  let t128 = t94 ^. t107 in
  upd st (size 4) (t113 ^. t114);
  upd st (size 3) (t118 ^. t128);
  let t131 = t93 ^. t101 in
  let t132 = t112 ^. t120 in
  upd st (size 0) (lognot (t113 ^. t125));
  let t134 = t97 ^. t116 in
  let t135 = t131 ^. t134 in
  let t136 = t93 ^. t115 in
  upd st (size 1) (lognot (t109 ^. t135));
  let t138 = t119 ^. t132 in
  upd st (size 2) (t109 ^. t138);
  let t140 = t114 ^. t136 in
  upd st (size 6) (lognot (t109 ^. t140))


val shift_row_inner: transpose_t -> uint16 -> uint16 -> shiftval U16 -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let shift_row_inner st st_mask nst_mask sh i =
  let st_i = st.(i) in
  let r16 : shiftval U16 = size_to_uint32 (size 16) in
  let row0 : uint16 = st_i &. st_mask in
  let row = (row0 >>. sh) |. (row0 <<. (r16 -. sh)) in
  let nv = (st_i &. nst_mask) ^. row in
  upd st i nv


val shift_row_loop: transpose_t -> uint16 -> uint16 -> shiftval U16 ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let shift_row_loop st st_mask nst_mask sh =
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) st
    (fun i -> shift_row_inner st st_mask nst_mask sh i)


val shift_row: transpose_t -> size_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let shift_row st i shift =
  let i16 : shiftval U16 = size_to_uint32 i in
  let shift16 : shiftval U16 = size_to_uint32 shift in
  let st_mask = u16 0x1111 <<. i16 in
  let nst_mask = lognot st_mask in
  let sh = (size_to_uint32 (size 4)) *. shift16 in
  shift_row_loop st st_mask nst_mask sh


val shift_rows: transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let shift_rows st =
  shift_row st (size 1) (size 1);
  shift_row st (size 2) (size 2);
  shift_row st (size 3) (size 3)



val xtime_inner: transpose_t -> lbuffer uint16 1 -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let xtime_inner st bprev i =
  let prev = bprev.(size 0) in
  let p = st.(i +. (size 1)) in
  upd st (i +. (size 1)) prev;
  upd bprev (size 0) p


val xtime_loop: transpose_t -> lbuffer uint16 1 ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let xtime_loop st bprev =
  let h0 = ST.get () in
  loop_nospec #h0 (size 7) st
  (fun i -> xtime_inner st bprev i)


val xtime: transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let xtime st =
  (**) let h0 = ST.get () in
  alloc_nospec #h0 (size 1) (u16 0) st
  (fun bprev ->
    xtime_loop st bprev;
    let prev = bprev.(size 0) in
    upd st (size 0) prev;
    let st0 = st.(size 0) in
    upd st (size 0) (st0 ^. prev);
    let st1 = st.(size 1) in
    upd st (size 1) (st1 ^. prev);
    let st3 = st.(size 3) in
    upd st (size 3) (st3 ^. prev);
    let st4 = st.(size 4) in
    upd st (size 4) (st4 ^. prev)
  )


val mix_column_inner1: transpose_t -> uint16 -> lbuffer uint16 8 -> lbuffer uint16 8 -> size_t ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let mix_column_inner1 st st_mask st1 st2 i =
  let st_i = st.(i) in
  let col = st_i &. st_mask in
  let col_rshift_1 = col >>. (size_to_uint32 (size 1)) in
  let col_lshift_1 = col <<. (size_to_uint32 (size 1)) in
  let col_rshift_2 = col >>. (size_to_uint32 (size 2)) in
  let col_lshift_2 = col <<. (size_to_uint32 (size 2)) in
  let col_rshift_3 = col >>. (size_to_uint32 (size 3)) in
  let col_lshift_3 = col <<. (size_to_uint32 (size 3)) in
  let col1 = (col_rshift_1 |. col_lshift_3) &. st_mask in
  let col2 = (col_rshift_2 |. col_lshift_2) &. st_mask in
  let col3 = (col_rshift_3 |. col_lshift_1) &. st_mask in
  upd st1 i (col ^. col1);
  upd st2 i (col1 ^. col2 ^. col3)


val mix_column_loop1: transpose_t -> uint16 -> lbuffer uint16 8 -> lbuffer uint16 8 ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let mix_column_loop1 st st_mask st1 st2 =
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) st
  (fun i -> mix_column_inner1 st st_mask st1 st2 i)


val mix_column_inner2: transpose_t -> uint16 -> lbuffer uint16 8 -> lbuffer uint16 8 -> size_t ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let mix_column_inner2 st nst_mask st1 st2 i =
  let st_i = st.(i) in
  let st1_i = st1.(i) in
  let st2_i = st2.(i) in
  let nv = (st_i &. nst_mask) ^. st2_i ^. st1_i in
  upd st i nv


val mix_column_loop2: transpose_t -> uint16 -> lbuffer uint16 8 -> lbuffer uint16 8 ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let mix_column_loop2 st nst_mask st1 st2 =
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) st
  (fun i -> mix_column_inner2 st nst_mask st1 st2 i)


val mix_column: transpose_t -> size_t ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let mix_column st c =
  let st_mask = (u16 0xf) <<. size_to_uint32 ((size 4) *. c) in
  let nst_mask = lognot st_mask in
  (**) let h0 = ST.get () in
  alloc_nospec #h0 (size 8) (u16 0) st
  (fun st1 ->
    (**) let h0 = ST.get () in
    alloc_nospec #h0 (size 8) (u16 0) st
    (fun st2 ->
      mix_column_loop1 st st_mask st1 st2;
      xtime st;
      mix_column_loop2 st nst_mask st1 st2
    )
  )


val mix_columns: transpose_t ->
  Stack unit
  (fun h -> True)
  (fun h0 _ h1 -> True)

let mix_columns st =
  mix_column st (size 0);
  mix_column st (size 1);
  mix_column st (size 2);
  mix_column st (size 3)


val add_round_key: transpose_t -> transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let add_round_key st k =
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) st
  (fun i ->
    let st_i = st.(i) in
    let k_i = k.(i) in
    upd st i (st_i ^. k_i)
  )


val aes_enc: transpose_t -> transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes_enc st k =
  sub_bytes st;
  shift_rows st;
  mix_columns st;
  add_round_key st k


val aes_enc_last: transpose_t -> transpose_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes_enc_last st k =
  sub_bytes st;
  shift_rows st;
  add_round_key st k


val rounds_step: transpose_t -> key_w -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let rounds_step st key i =
  let sub_key = sub key (i *. (size 8)) (size 8) in
  aes_enc st sub_key


val rounds: transpose_t -> key_w ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let rounds st key =
  let h0 = ST.get () in
  loop_nospec #h0 (size 9) st
  (fun i -> rounds_step st key i)


val block_cipher: state_t -> state_t -> key_w ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let block_cipher output input key =
  (**) let h0 = ST.get () in
  alloc_nospec #h0 (size 8) (u16 0) output
  (fun st ->
    let k0 = sub key (size 0) (size size_key_w) in
    let k = sub key (size 1) ((size size_key_w) -. (size 1)) in
    let kn = sub key (size 5) ((size size_key_w) -. (size 5)) in
    to_transpose st input;
    add_round_key st k0;
    rounds st k;
    aes_enc_last st kn;
    from_transpose output st
  )


inline_for_extraction val create_const_rcon: unit -> StackInline (lbuffer uint8 11)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1))

inline_for_extraction let create_const_rcon () =
  createL [
    u8 0x8d; u8 0x01; u8 0x02; u8 0x04;
    u8 0x08; u8 0x10; u8 0x20; u8 0x40;
    u8 0x80; u8 0x1b; u8 0x36 ]


val key_expansion_inner: transpose_t -> transpose_t -> uint8 ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let key_expansion_inner next prev rcon =
  copy next (size 16) prev;
  sub_bytes next;
  let h0 = ST.get () in
  loop_nospec #h0 (size 8) next
  (fun i ->
    let n_i = next.(i) in
    let n = n_i >>. (size_to_uint32 (size 12)) in
    let n = ((n >>. (size_to_uint32 (size 1))) |. (n <<. (size_to_uint32 (size 3)))) &. (u16 0xf) in
    let n = n ^. (((to_u16 #U8 rcon) >>. (size_to_uint32 i)) &. (u16 1)) in
    let n = n ^. (n <<. (size_to_uint32 (size 4))) ^. (n <<. (size_to_uint32 (size 8))) ^. (n <<. (size_to_uint32 (size 12))) in
    let p = prev.(i) in
    let p = p ^. (p <<. (size_to_uint32 (size 4))) ^. (p <<. (size_to_uint32 (size 8))) ^. (p <<. (size_to_uint32 (size 12))) in
    upd next i (n ^. p)
  )


val key_expansion_step: transpose_t -> lbuffer uint8 11 -> i:size_t{1 < v i} ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let key_expansion_step output rcon i =
  let idx : size_t = i -. (size 1) in
  let sub_out0 = sub output i (size 8) in
  let sub_out1 = sub output i (size 8) in
  let rcon_i = rcon.(i) in
  key_expansion_inner sub_out1 sub_out0 rcon_i


val key_expansion: transpose_t -> state_t -> lbuffer uint8 11 ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let key_expansion output key rcon =
  to_transpose output key;
  let h0 = ST.get () in
  loop_nospec #h0 (size 10) output
  (fun i -> key_expansion_step output rcon (i +. (size 1)))


val aes128_block: state_t -> key_w -> nonce_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_block output kex n c =
  (**) let h0 = ST.get () in
  alloc_nospec #h0 (size 16) (u8 0) output
  (fun input ->
    let sub_input = sub input (size 0) (size 12) in
    copy sub_input (size 12) n;
    upd input (size 12) ((to_u8 c) >>. (size_to_uint32 (size 24)));
    upd input (size 13) ((to_u8 c) >>. (size_to_uint32 (size 16)));
    upd input (size 14) ((to_u8 c) >>. (size_to_uint32 (size 8)));
    upd input (size 15) (to_u8 c);
    block_cipher output input kex
  )


val aes128_ctr_loop_inner_step: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> lbuffer uint8 16 -> size_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_ctr_loop_inner_step #vlen output input kb i j =
  let idx = ((size 16) *. i) +. j in
  let in_idx = input.(idx) in
  let kb_j = kb.(j) in
  upd output i (in_idx ^. kb_j)


val aes128_ctr_loop1_inner: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> lbuffer uint8 16 -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_ctr_loop1_inner #vlen output input kb i =
  let h0 = ST.get () in
  loop_nospec #h0 (size 16) output
  (fun j -> aes128_ctr_loop_inner_step #vlen output input kb i j)


val aes128_ctr_loop1: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> key_w -> lbuffer uint8 12 -> lbuffer uint8 16 -> size_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_ctr_loop1 #vlen output input kex nonce kb nblocks c =
  let h0 = ST.get () in
  loop_nospec #h0 nblocks output
  (fun i ->
    aes128_block kb kex nonce (c +. i);
    aes128_ctr_loop1_inner #vlen output input kb i)


val aes128_ctr_loop2: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> lbuffer uint8 16 -> size_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_ctr_loop2 #vlen output input kb nblocks rem =
  let h0 = ST.get () in
  loop_nospec #h0 rem output
  (fun j -> aes128_ctr_loop_inner_step #vlen output input kb nblocks j)


val aes128_ctr: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> size_t -> state_t -> nonce_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_ctr #vlen output input len key nonce c =
  let rcon = create_const_rcon () in
  (**) let h0 = ST.get () in
  alloc_nospec #h0 (size 8 *. size 11) (u16 0) output
  (fun kex ->
    (**) let h0 = ST.get () in
    alloc_nospec #h0 (size 16) (u8 0) output
    (fun kb ->
      (**) let h0 = ST.get () in
      alloc_nospec #h0 (size size_key_w) (u16 0) output
      (fun kexw ->
        key_expansion kex key rcon;
        let nblocks = len /. (size size_block) in
        let rem = len %. (size size_block) in
        aes128_ctr_loop1 #vlen output input kexw nonce kb nblocks c;
        if rem >=. (size 0) then
          aes128_block kb kexw nonce (c +. nblocks);
          aes128_ctr_loop2 #vlen output input kb nblocks rem
      )
    )
  )


val aes128_encrypt: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> size_t -> state_t -> nonce_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_encrypt #vlen output input len key nonce c = aes128_ctr #vlen output input len key nonce c


val aes128_decrypt: #vlen:size_nat -> block_t -> lbuffer uint8 vlen -> size_t -> state_t -> nonce_t -> size_t ->
  Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

let aes128_decrypt #vlen output input len key nonce c = aes128_ctr #vlen output input len key nonce c
