module Hacl.Spec.AES_128.BitSlice

open Lib.IntTypes


let transpose_bits64 (x:uint64) : Tot uint64 =
  (x &. u64 0x8040201008040201)    |.
  ((x &. u64 0x4020100804020100) >>. size 7) |.
  ((x &. u64 0x2010080402010000) >>. size 14) |.
  ((x &. u64 0x1008040201000000) >>. size 21) |.
  ((x &. u64 0x0804020100000000) >>. size 28) |.
  ((x &. u64 0x0402010000000000) >>. size 35) |.
  ((x &. u64 0x0201000000000000) >>. size 42) |.
  ((x &. u64 0x0100000000000000) >>. size 49) |.
  ((x <<. size  7) &. u64 0x4020100804020100) |.
  ((x <<. size 14) &. u64 0x2010080402010000) |.
  ((x <<. size 21) &. u64 0x1008040201000000) |.
  ((x <<. size 28) &. u64 0x0804020100000000) |.
  ((x <<. size 35) &. u64 0x0402010000000000) |.
  ((x <<. size 42) &. u64 0x0201000000000000) |.
  ((x <<. size 49) &. u64 0x0100000000000000)


inline_for_extraction
val transpose_bits64x8:
  i0:uint64 -> i1:uint64 -> i2: uint64 -> i3:uint64 ->
  i4:uint64 -> i5:uint64 -> i6: uint64 -> i7:uint64 ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let transpose_bits64x8 i0 i1 i2 i3 i4 i5 i6 i7 =
  let t0 = (i0 &. u64 0xffffffff) ^. (i4 <<. size 32) in
  let t1 = (i1 &. u64 0xffffffff) ^. (i5 <<. size 32) in
  let t2 = (i2 &. u64 0xffffffff) ^. (i6 <<. size 32) in
  let t3 = (i3 &. u64 0xffffffff) ^. (i7 <<. size 32) in
  let t4 = (i4 &. u64 0xffffffff00000000) ^. (i0 >>. size  32) in
  let t5 = (i5 &. u64 0xffffffff00000000) ^. (i1 >>. size  32) in
  let t6 = (i6 &. u64 0xffffffff00000000) ^. (i2 >>. size  32) in
  let t7 = (i7 &. u64 0xffffffff00000000) ^. (i3 >>. size  32) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t3 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in

  let t0 = (t0 &. u64 0x0000ffff0000ffff) ^. ((t2 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t1 = (t1 &. u64 0x0000ffff0000ffff) ^. ((t3 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t2 = (t2 &. u64 0xffff0000ffff0000) ^. ((t0_ &. u64 0xffff0000ffff0000) >>. size  16) in
  let t3 = (t3 &. u64 0xffff0000ffff0000) ^. ((t1_ &. u64 0xffff0000ffff0000) >>. size  16) in
  let t4 = (t4 &. u64 0x0000ffff0000ffff) ^. ((t6 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t5 = (t5 &. u64 0x0000ffff0000ffff) ^. ((t7 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t6 = (t6 &. u64 0xffff0000ffff0000) ^. ((t4_ &. u64 0xffff0000ffff0000) >>. size  16) in
  let t7 = (t7 &. u64 0xffff0000ffff0000) ^. ((t5_ &. u64 0xffff0000ffff0000) >>. size  16) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t2 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in

  let t0 = (t0 &. u64 0x00ff00ff00ff00ff) ^. ((t1 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t1 = (t1 &. u64 0xff00ff00ff00ff00) ^. ((t0_ &. u64 0xff00ff00ff00ff00) >>. size  8) in
  let t2 = (t2 &. u64 0x00ff00ff00ff00ff) ^. ((t3 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t3 = (t3 &. u64 0xff00ff00ff00ff00) ^. ((t2_ &. u64 0xff00ff00ff00ff00) >>. size  8) in
  let t4 = (t4 &. u64 0x00ff00ff00ff00ff) ^. ((t5 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t5 = (t5 &. u64 0xff00ff00ff00ff00) ^. ((t4_ &. u64 0xff00ff00ff00ff00) >>. size  8) in
  let t6 = (t6 &. u64 0x00ff00ff00ff00ff) ^. ((t7 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t7 = (t7 &. u64 0xff00ff00ff00ff00) ^. ((t6_ &. u64 0xff00ff00ff00ff00) >>. size  8) in

  let t0 = transpose_bits64(t0) in
  let t1 = transpose_bits64(t1) in
  let t2 = transpose_bits64(t2) in
  let t3 = transpose_bits64(t3) in
  let t4 = transpose_bits64(t4) in
  let t5 = transpose_bits64(t5) in
  let t6 = transpose_bits64(t6) in
  let t7 = transpose_bits64(t7) in

  (t0,t1,t2,t3,t4,t5,t6,t7)


(* Boyar and Peralta circuit: depth 16, gates 125 *)
inline_for_extraction
val sub_bytes64x8_boyar:
    uint64 -> uint64 -> uint64 -> uint64
  -> uint64 -> uint64 -> uint64 -> uint64 ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let sub_bytes64x8_boyar (st0:uint64) (st1:uint64) (st2:uint64) (st3:uint64) (st4:uint64) (st5:uint64) (st6:uint64) (st7:uint64) =
  let u0 = st7 in
  let u1 = st6 in
  let u2 = st5 in
  let u3 = st4 in
  let u4 = st3 in
  let u5 = st2 in
  let u6 = st1 in
  let u7 = st0 in

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
  let t15 = u5 ^. t7 in
  let t19 = t2 ^. t18 in
  let t21 = t1 ^. t13 in

  let t9 = u6 ^. t4 in
  let t10 = u3 ^. t4 in
  let t11 = u7 ^. t5 in
  let t12 = t5 ^. t6 in
  let t14 = t3 ^. t5 in
  let t17 = u7 ^. t8 in
  let t22 = u0 ^. t4 in
  let t54 = t2 &. t8 in
  let t20 = t4 ^. t15 in
  let t39 = t21 ^. t5 in
  let t40 = t21 ^. t7 in
  let t41 = t7 ^. t19 in
  let t44 = t19 &. t5 in
  let t49 = t7 &. t21 in

  let t50 = t9 &. t4 in
  let t42 = t16 ^. t14 in
  let t43 = t22 ^. t17 in
  let t45 = t20 &. t11 in
  let t47 = t10 &. u7 in
  let t57 = t16 &. t14 in
  let t46 = t12 ^. t44 in
  let t55 = t41 &. t39 in

  let t48 = t47 ^. t44 in
  let t51 = t40 ^. t49 in
  let t52 = t22 &. t17 in
  let t53 = t52 ^. t49 in
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
  let st7 = t109 ^. t122 in
  let st5 = lognot (t123 ^. t124) in
  let t128 = t94 ^. t107 in
  let st4 = t113 ^. t114 in
  let st3 = t118 ^. t128 in
  let t131 = t93 ^. t101 in
  let t132 = t112 ^. t120 in
  let st0 = lognot (t113 ^. t125) in
  let t134 = t97 ^. t116 in
  let t135 = t131 ^. t134 in
  let t136 = t93 ^. t115 in
  let st1 = lognot (t109 ^. t135) in
  let t138 = t119 ^. t132 in
  let st2 = t109 ^. t138 in
  let t140 = t114 ^. t136 in
  let st6 = lognot (t109 ^. t140) in
  (st0,st1,st2,st3,st4,st5,st6,st7)


(* A slightly faster circuit from Cagdas Calik: depth 27, gates 113 *)
inline_for_extraction
val sub_bytes64x8:
    uint64 -> uint64 -> uint64 -> uint64
  -> uint64 -> uint64 -> uint64 -> uint64 ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let sub_bytes64x8 (st0:uint64) (st1:uint64) (st2:uint64) (st3:uint64) (st4:uint64) (st5:uint64) (st6:uint64) (st7:uint64) =
  let u0 = st7 in
  let u1 = st6 in
  let u2 = st5 in
  let u3 = st4 in
  let u4 = st3 in
  let u5 = st2 in
  let u6 = st1 in
  let u7 = st0 in

  let y14 = u3 ^. u5 in
  let y13 = u0 ^. u6 in
  let y9 = u0 ^. u3 in
  let y8 = u0 ^. u5 in
  let t0 = u1 ^. u2 in
  let y1 = t0 ^. u7 in
  let y4 = y1 ^. u3 in
  let y12 = y13 ^. y14 in
  let y2 = y1 ^. u0 in
  let y5 = y1 ^. u6 in
  let y3 = y5 ^. y8 in
  let t1 = u4 ^. y12 in
  let y15 = t1 ^. u5 in
  let y20 = t1 ^. u1 in
  let y6 = y15 ^. u7 in
  let y10 = y15 ^. t0 in
  let y11 = y20 ^. y9 in
  let y7 = u7 ^. y11 in
  let y17 = y10 ^. y11 in
  let y19 = y10 ^. y8 in
  let y16 = t0 ^. y11 in
  let y21 = y13 ^. y16 in
  let y18 = u0 ^. y16 in
  let t2 = y12 &. y15 in
  let t3 = y3 &. y6 in
  let t4 = t3 ^. t2 in
  let t5 = y4 &. u7 in
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
  let t17 = t4 ^. y20 in
  let t18 = t6 ^. t16 in
  let t19 = t9 ^. t14 in
  let t20 = t11 ^. t16 in
  let t21 = t17 ^. t14 in
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
  let z2 = t33 &. u7 in
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
  let s6 = t56 ^. lognot t62 in
  let s7 = t48 ^. lognot t60 in
  let t67 = t64 ^. t65 in
  let s3 = t53 ^. t66 in
  let s4 = t51 ^. t66 in
  let s5 = t47 ^. t65 in
  let s1 = t64 ^. lognot s3 in
  let s2 = t55 ^. lognot t67 in
  (s7,s6,s5,s4,s3,s2,s1,s0)


inline_for_extraction
let shift_row64 (u:uint64) =
  let u = (u &. u64 0x1111111111111111) |.
          ((u &. u64 0x2220222022202220) >>. size 4) |.
          ((u &. u64 0x0002000200020002) <<. size 12) |.
          ((u &. u64 0x4400440044004400) >>. size 8) |.
          ((u &. u64 0x0044004400440044) <<. size 8) |.
          ((u &. u64 0x8000800080008000) >>. size 12) |.
          ((u &. u64 0x0888088808880888) <<. size 4) in
  u
