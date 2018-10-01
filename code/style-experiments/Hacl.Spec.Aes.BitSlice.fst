module Hacl.Spec.Aes.BitSlice

open Lib.IntTypes
open Lib.Utils

inline_for_extraction
let transpose_bits64 (x:uint64) : Tot uint64 = 
     (x &. u64 0x8040201008040201)    |.
    ((x &. u64 0x4020100804020100) >>. u32 7) |.
    ((x &. u64 0x2010080402010000) >>. u32 14) |.
    ((x &. u64 0x1008040201000000) >>. u32 21) |.
    ((x &. u64 0x0804020100000000) >>. u32 28) |.
    ((x &. u64 0x0402010000000000) >>. u32 35) |.
    ((x &. u64 0x0201000000000000) >>. u32 42) |.
    ((x &. u64 0x0100000000000000) >>. u32 49) |.
    ((x <<. u32  7) &. u64 0x4020100804020100) |.
    ((x <<. u32 14) &. u64 0x2010080402010000) |.
    ((x <<. u32 21) &. u64 0x1008040201000000) |.
    ((x <<. u32 28) &. u64 0x0804020100000000) |.
    ((x <<. u32 35) &. u64 0x0402010000000000) |.
    ((x <<. u32 42) &. u64 0x0201000000000000) |.
    ((x <<. u32 49) &. u64 0x0100000000000000)


inline_for_extraction
val transpose_bits64x8: i0:uint64 -> i1:uint64 -> i2: uint64 -> i3:uint64 ->
		     i4:uint64 -> i5:uint64 -> i6: uint64 -> i7:uint64 ->
		     Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
let transpose_bits64x8 i0 i1 i2 i3 i4 i5 i6 i7 = 
  let t0 = (i0 &. u64 0xffffffff) ^. (i4 <<. u32 32) in
  let t1 = (i1 &. u64 0xffffffff) ^. (i5 <<. u32 32) in
  let t2 = (i2 &. u64 0xffffffff) ^. (i6 <<. u32 32) in
  let t3 = (i3 &. u64 0xffffffff) ^. (i7 <<. u32 32) in
  let t4 = (i4 &. u64 0xffffffff00000000) ^. (i0 >>. u32  32) in
  let t5 = (i5 &. u64 0xffffffff00000000) ^. (i1 >>. u32  32) in
  let t6 = (i6 &. u64 0xffffffff00000000) ^. (i2 >>. u32  32) in
  let t7 = (i7 &. u64 0xffffffff00000000) ^. (i3 >>. u32  32) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t3 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in
  
  let t0 = (t0 &. u64 0x0000ffff0000ffff) ^. ((t2 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t1 = (t1 &. u64 0x0000ffff0000ffff) ^. ((t3 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t2 = (t2 &. u64 0xffff0000ffff0000) ^. ((t0_ &. u64 0xffff0000ffff0000) >>. u32  16) in
  let t3 = (t3 &. u64 0xffff0000ffff0000) ^. ((t1_ &. u64 0xffff0000ffff0000) >>. u32  16) in
  let t4 = (t4 &. u64 0x0000ffff0000ffff) ^. ((t6 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t5 = (t5 &. u64 0x0000ffff0000ffff) ^. ((t7 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t6 = (t6 &. u64 0xffff0000ffff0000) ^. ((t4_ &. u64 0xffff0000ffff0000) >>. u32  16) in
  let t7 = (t7 &. u64 0xffff0000ffff0000) ^. ((t5_ &. u64 0xffff0000ffff0000) >>. u32  16) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t2 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in

  let t0 = (t0 &. u64 0x00ff00ff00ff00ff) ^. ((t1 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t1 = (t1 &. u64 0xff00ff00ff00ff00) ^. ((t0_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in
  let t2 = (t2 &. u64 0x00ff00ff00ff00ff) ^. ((t3 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t3 = (t3 &. u64 0xff00ff00ff00ff00) ^. ((t2_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in
  let t4 = (t4 &. u64 0x00ff00ff00ff00ff) ^. ((t5 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t5 = (t5 &. u64 0xff00ff00ff00ff00) ^. ((t4_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in
  let t6 = (t6 &. u64 0x00ff00ff00ff00ff) ^. ((t7 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t7 = (t7 &. u64 0xff00ff00ff00ff00) ^. ((t6_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in

  let t0 = transpose_bits64(t0) in
  let t1 = transpose_bits64(t1) in
  let t2 = transpose_bits64(t2) in
  let t3 = transpose_bits64(t3) in
  let t4 = transpose_bits64(t4) in
  let t5 = transpose_bits64(t5) in
  let t6 = transpose_bits64(t6) in
  let t7 = transpose_bits64(t7) in

  (t0,t1,t2,t3,t4,t5,t6,t7)

inline_for_extraction 
val sub_bytes64x8: uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
let sub_bytes64x8 (st0:uint64) (st1:uint64) (st2:uint64) (st3:uint64) (st4:uint64) (st5:uint64) (st6:uint64) (st7:uint64) = 
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

inline_for_extraction 
let shift_row64 (u:uint64) = 
    let u = (u &. u64 0x1111111111111111) |.
      ((u &. u64 0x2220222022202220) >>. u32 4) |. 
      ((u &. u64 0x0002000200020002) <<. u32 12) |.
      ((u &. u64 0x4400440044004400) >>. u32 8) |. 
      ((u &. u64 0x0044004400440044) <<. u32 8) |.
      ((u &. u64 0x8000800080008000) >>. u32 12) |. 
      ((u &. u64 0x0888088808880888) <<. u32 4) in
    u





