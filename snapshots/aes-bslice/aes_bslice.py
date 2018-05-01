#!/usr/bin/python3

from speclib import *

blocksize = 16
block_t  = bytes_t(16)
subblock_t  = refine(vlbytes_t, lambda x: array.length(x) <= blocksize)

rowindex_t = range_t(0,4)
expindex_t = range_t(0,48)
word_t = bytes_t(4)
key_t    = bytes_t(32)
nonce_t  = bytes_t(12)


transpose_t = array_t(uint16_t,8)

def to_transpose(b:block_t) -> transpose_t:
    t = array.create(8,uint16(0))
    for i in range(8):
        for j in range(16):
            if i > j:
                t[i] ^= uint16(b[j] & uint8(1 << i)) >> (i - j)
            else:
                t[i] ^= uint16(b[j] & uint8(1 << i)) << (j - i)
    return t

def from_transpose(t:transpose_t) -> block_t:
    b = array.create(16,uint8(0))
    for i in range(16):
        for j in range(8):
            if i > j:
                b[i] ^= uint8((t[j] & uint16(1 << i)) >> (i - j))
            else:
                b[i] ^= uint8((t[j] & uint16(1 << i)) << (j - i))
    return b

def subBytes(u:transpose_t) -> transpose_t:
  u0 = u[7]
  u1 = u[6]
  u2 = u[5]
  u3 = u[4]
  u4 = u[3]
  u5 = u[2]
  u6 = u[1]
  u7 = u[0]

  t1 = u6 ^ u4 
  t2 = u3 ^ u0
  t3 = u1 ^ u2
  t6 = u1 ^ u5 
  t7 = u0 ^ u6 
  t13 = u2 ^ u5 
  t16 = u0 ^ u5
  t18 = u6 ^ u5
  
  t4 = u7 ^ t3
  t5 = t1 ^ t2 
  t8 = t1 ^ t6
  t9 = u6 ^ t4
    
  t10 = u3 ^ t4
  t11 = u7 ^ t5
  t12 = t5 ^ t6
  t14 = t3 ^ t5
  t15 = u5 ^ t7 
  t17 = u7 ^ t8  
  t19 = t2 ^ t18
  t22 = u0 ^ t4
  t54 = t2 & t8
  t50 = t9 & t4
    
  t20 = t4 ^ t15 
  t21 = t1 ^ t13
  t39 = t21 ^ t5
  t40 = t21 ^ t7  
  t41 = t7 ^ t19
  t42 = t16 ^ t14
  t43 = t22 ^ t17
  t44 = t19 & t5
  t45 = t20 & t11
  t47 = t10 & u7
  t57 = t16 & t14
  
  t46 = t12 ^ t44  
  t48 = t47 ^ t44
  t49 = t7 & t21
  t51 = t40 ^ t49
  t52 = t22 & t17
  t53 = t52 ^ t49

  t55 = t41 & t39
  t56 = t55 ^ t54
  t58 = t57 ^ t54
  t59 = t46 ^ t45
  t60 = t48 ^ t42
  t61 = t51 ^ t50
  t62 = t53 ^ t58
  t63 = t59 ^ t56
  t64 = t60 ^ t58
  t65 = t61 ^ t56
  t66 = t62 ^ t43
  t67 = t65 ^ t66 
  t68 = t65 & t63
  t69 = t64 ^ t68
  t70 = t63 ^ t64
  t71 = t66 ^ t68 
  t72 = t71 & t70
  t73 = t69 & t67
  t74 = t63 & t66
  t75 = t70 & t74
  t76 = t70 ^ t68
  t77 = t64 & t65
  t78 = t67 & t77
  t79 = t67 ^ t68
  t80 = t64 ^ t72
  t81 = t75 ^ t76
  t82 = t66 ^ t73
  t83 = t78 ^ t79
  t84 = t81 ^ t83
  t85 = t80 ^ t82
  t86 = t80 ^ t81
  t87 = t82 ^ t83
  t88 = t85 ^ t84
  t89 = t87 & t5
  t90 = t83 & t11
  t91 = t82 & u7
  t92 = t86 & t21
  t93 = t81 & t4
  t94 = t80 & t17
  t95 = t85 & t8
  t96 = t88 & t39
  t97 = t84 & t14
  t98 = t87 & t19
  t99 = t83 & t20
  t100 = t82 & t10
  t101 = t86 & t7
  t102 = t81 & t9
  t103 = t80 & t22
  t104 = t85 & t2
  t105 = t88 & t41
  t106 = t84 & t16
  t107 = t104 ^ t105
  t108 = t93 ^ t99
  t109 = t96 ^ t107
  t110 = t98 ^ t108
  t111 = t91 ^ t101
  t112 = t89 ^ t92
  t113 = t107 ^ t112
  t114 = t90 ^ t110
  t115 = t89 ^ t95
  t116 = t94 ^ t102
  t117 = t97 ^ t103 
  t118 = t91 ^ t114
  t119 = t111 ^ t117
  t120 = t100 ^ t108
  t121 = t92 ^ t95
  t122 = t110 ^ t121
  t123 = t106 ^ t119
  t124 = t104 ^ t115
  t125 = t111 ^ t116

  s = array.create(8,uint16(0))
  s[7] = t109 ^ t122
  s[5] = ~(t123 ^ t124)
  t128 = t94 ^ t107
  s[4] = t113 ^ t114
  s[3] = t118 ^ t128
  t131 = t93 ^ t101
  t132 = t112 ^ t120
  s[0] = ~(t113 ^ t125)
  t134 = t97 ^ t116
  t135 = t131 ^ t134
  t136 = t93 ^ t115
  s[1] = ~(t109 ^ t135)
  t138 = t119 ^ t132
  s[2] = t109 ^ t138
  t140 = t114 ^ t136
  s[6] = ~(t109 ^ t140)
  
  return s

        
def shiftRow(i:rowindex_t,shift:rowindex_t,state:transpose_t) -> transpose_t:
    st = array.copy(state)
    st_mask = uint16(0x1111) << i
    nst_mask = ~st_mask
    for i in range(8):
        row = st[i] & st_mask
        row = uint16.rotate_right(row,4*shift)
        st[i] = (st[i] & nst_mask) ^ row
    return st

st : block_t = array([
    uint8(1), uint8(2), uint8(4), uint8(8), 
    uint8(16), uint8(32), uint8(64), uint8(128), 
    uint8(1), uint8(2), uint8(4), uint8(8), 
    uint8(16), uint8(32), uint8(64), uint8(128)
    ])

def shiftRows(state:transpose_t) -> transpose_t:
    state = shiftRow(1,1,state)
    state = shiftRow(2,2,state)
    state = shiftRow(3,3,state)
    return state

def xtime(t:transpose_t) -> transpose_t:
    x = array.create(8,uint16(0))
    for i in range(7):
        x[i+1] = t[i]
    x[0] = t[7]
    x[1] ^= t[7]
    x[3] ^= t[7]
    x[4] ^= t[7]
    return x

def mixColumn(c:rowindex_t,state:transpose_t) -> transpose_t:
    st_mask = uint16(0xf) << (4 * c)
    nst_mask = ~st_mask
    st1 = array.copy(state)
    st2 = array.copy(state)
    for i in range(8):
        col = state[i] & st_mask
        col1 = ((col >> 1) | (col << 3)) & st_mask
        col2 = ((col >> 2) | (col << 2)) & st_mask
        col3 = ((col >> 3) | (col << 1)) & st_mask
        st1[i] = col ^ col1
        st2[i] = col1 ^ col2 ^ col3
    st1 = xtime(st1)
    for i in range(8):
        st2[i] ^= st1[i]
        st2[i] = (state[i] & nst_mask) ^ st2[i]
    return st2    

def mixColumns(st:transpose_t) -> transpose_t:
    st = mixColumn(0,st)
    st = mixColumn(1,st)
    st = mixColumn(2,st)
    st = mixColumn(3,st)
    return st

def addRoundKey(key:transpose_t,state:transpose_t) -> transpose_t:
    out = array.copy(state)
    for i in range(8):
        out[i] ^= key[i]
    return out

def round(key:transpose_t,st:transpose_t) -> transpose_t:
    st = subBytes(st)
    st = shiftRows(st)
    st = mixColumns(st)
    st = addRoundKey(key,st)
    return st

def rounds(key:array_t(uint16_t,9*8),state:transpose_t) -> transpose_t:
    out = array.copy(state)
    for i in range(9):
        out = round(key[8*i:8*i+8],out)
    return out

def block_cipher(key:array_t(uint16_t,11*8),input:block_t) -> block_t:
    st = to_transpose(input)
    k0 = key[0:8]
    k  = key[8:10*8]
    kn = key[10*8:11*8]
    st = addRoundKey(k0,st)
    st = rounds(k,st)
    st = subBytes(st)
    st = shiftRows(st)
    st = addRoundKey(kn,st)
    return from_transpose(st)

def rotate_word(w:word_t) -> word_t:
    out = array.copy(w)
    out[0] = w[1]
    out[1] = w[2]
    out[2] = w[3]
    out[3] = w[0]
    return out

def sub_word(w:word_t) -> word_t:
    tmp = array.create(16,uint8(0))
    tmp[0:4] = w
    st = to_transpose(tmp)
    st = subBytes(st)
    tmp = from_transpose(st)
    return tmp[0:4]

rcon : bytes_t(11) = array([
    uint8(0x8d), uint8(0x01), uint8(0x02), uint8(0x04),
    uint8(0x08), uint8(0x10), uint8(0x20), uint8(0x40),
    uint8(0x80), uint8(0x1b), uint8(0x36)])

def aes_keygen_assist(w:word_t,rcon:uint8_t) -> word_t:
    k = rotate_word(w)
    k = sub_word(k)
    k[0] ^= rcon
    return k

def key_expansion_word(w0:word_t, w1:word_t, i:expindex_t) -> word_t:
    k = array.copy(w1)
    if i % 4 == 0:
        k = aes_keygen_assist(k,rcon[i//4])
    for i in range(4):
        k[i] ^= w0[i]
    return k

def key_expansion(key:block_t) -> array_t(uint16_t,11*8):
    key_ex = array.create(11*16,uint8(0))
    key_ex[0:16] = key
    for j in range(40):
        i = j + 4
        key_ex[4*i:4*i+4] = key_expansion_word(key_ex[4*i-16:4*i-12],key_ex[4*i-4:4*i],i)
    out = array.create(11*8,uint16(0))
    for i in range(11):
        out[i*8:i*8+8] = to_transpose(key_ex[i*16:i*16+16])
    return out

def aes128_block(k:key_t,n:nonce_t,c:uint32_t) -> block_t:
    input = array.create(16,uint8(0))
    input[0:12] = n
    input[12:16] = bytes.from_uint32_be(c)
    key_ex = key_expansion(k)
    out = block_cipher(key_ex,input)
    return out

def xor_block(block:subblock_t, keyblock:block_t) -> subblock_t:
    out = vlbytes.copy(block)
    for i in range(array.length(block)):
        out[i] ^= keyblock[i]
    return out

def aes128_counter_mode(key: key_t, nonce: nonce_t, counter: uint32_t, msg:vlbytes_t) -> vlbytes_t:
    blocks,last = vlarray.split_blocks(msg,blocksize)
    keyblock = array.create(blocksize,uint8(0))
    ctr = counter
    for i in range(array.length(blocks)):
        keyblock = aes128_block(key,nonce,ctr)
        blocks[i] = xor_block(blocks[i],keyblock)
        ctr += uint32(1)
    keyblock = aes128_block(key,nonce,ctr)
    last = xor_block(last,keyblock)
    return vlarray.concat_blocks(blocks,last)

def aes128_encrypt(key: key_t, nonce: nonce_t, counter: uint32_t, msg:vlbytes_t) -> vlbytes_t:
    return aes128_counter_mode(key,nonce,counter,msg)

def aes128_decrypt(key: key_t, nonce: nonce_t, counter: uint32_t, msg:vlbytes_t) -> vlbytes_t:
    return aes128_counter_mode(key,nonce,counter,msg)


