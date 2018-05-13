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


index_t  = range_t(0,16)
rotval_t = range_t(1,32)
state_t  = array_t(uint32_t,16)


sbox : array_t(uint8_t,256) = array([
    uint8(0x63), uint8(0x7C), uint8(0x77), uint8(0x7B), uint8(0xF2), uint8(0x6B), uint8(0x6F), uint8(0xC5), uint8(0x30), uint8(0x01), uint8(0x67), uint8(0x2B), uint8(0xFE), uint8(0xD7), uint8(0xAB), uint8(0x76),
    uint8(0xCA), uint8(0x82), uint8(0xC9), uint8(0x7D), uint8(0xFA), uint8(0x59), uint8(0x47), uint8(0xF0), uint8(0xAD), uint8(0xD4), uint8(0xA2), uint8(0xAF), uint8(0x9C), uint8(0xA4), uint8(0x72), uint8(0xC0),
    uint8(0xB7), uint8(0xFD), uint8(0x93), uint8(0x26), uint8(0x36), uint8(0x3F), uint8(0xF7), uint8(0xCC), uint8(0x34), uint8(0xA5), uint8(0xE5), uint8(0xF1), uint8(0x71), uint8(0xD8), uint8(0x31), uint8(0x15),
    uint8(0x04), uint8(0xC7), uint8(0x23), uint8(0xC3), uint8(0x18), uint8(0x96), uint8(0x05), uint8(0x9A), uint8(0x07), uint8(0x12), uint8(0x80), uint8(0xE2), uint8(0xEB), uint8(0x27), uint8(0xB2), uint8(0x75),
    uint8(0x09), uint8(0x83), uint8(0x2C), uint8(0x1A), uint8(0x1B), uint8(0x6E), uint8(0x5A), uint8(0xA0), uint8(0x52), uint8(0x3B), uint8(0xD6), uint8(0xB3), uint8(0x29), uint8(0xE3), uint8(0x2F), uint8(0x84),
    uint8(0x53), uint8(0xD1), uint8(0x00), uint8(0xED), uint8(0x20), uint8(0xFC), uint8(0xB1), uint8(0x5B), uint8(0x6A), uint8(0xCB), uint8(0xBE), uint8(0x39), uint8(0x4A), uint8(0x4C), uint8(0x58), uint8(0xCF),
    uint8(0xD0), uint8(0xEF), uint8(0xAA), uint8(0xFB), uint8(0x43), uint8(0x4D), uint8(0x33), uint8(0x85), uint8(0x45), uint8(0xF9), uint8(0x02), uint8(0x7F), uint8(0x50), uint8(0x3C), uint8(0x9F), uint8(0xA8),
    uint8(0x51), uint8(0xA3), uint8(0x40), uint8(0x8F), uint8(0x92), uint8(0x9D), uint8(0x38), uint8(0xF5), uint8(0xBC), uint8(0xB6), uint8(0xDA), uint8(0x21), uint8(0x10), uint8(0xFF), uint8(0xF3), uint8(0xD2),
    uint8(0xCD), uint8(0x0C), uint8(0x13), uint8(0xEC), uint8(0x5F), uint8(0x97), uint8(0x44), uint8(0x17), uint8(0xC4), uint8(0xA7), uint8(0x7E), uint8(0x3D), uint8(0x64), uint8(0x5D), uint8(0x19), uint8(0x73),
    uint8(0x60), uint8(0x81), uint8(0x4F), uint8(0xDC), uint8(0x22), uint8(0x2A), uint8(0x90), uint8(0x88), uint8(0x46), uint8(0xEE), uint8(0xB8), uint8(0x14), uint8(0xDE), uint8(0x5E), uint8(0x0B), uint8(0xDB),
    uint8(0xE0), uint8(0x32), uint8(0x3A), uint8(0x0A), uint8(0x49), uint8(0x06), uint8(0x24), uint8(0x5C), uint8(0xC2), uint8(0xD3), uint8(0xAC), uint8(0x62), uint8(0x91), uint8(0x95), uint8(0xE4), uint8(0x79),
    uint8(0xE7), uint8(0xC8), uint8(0x37), uint8(0x6D), uint8(0x8D), uint8(0xD5), uint8(0x4E), uint8(0xA9), uint8(0x6C), uint8(0x56), uint8(0xF4), uint8(0xEA), uint8(0x65), uint8(0x7A), uint8(0xAE), uint8(0x08),
    uint8(0xBA), uint8(0x78), uint8(0x25), uint8(0x2E), uint8(0x1C), uint8(0xA6), uint8(0xB4), uint8(0xC6), uint8(0xE8), uint8(0xDD), uint8(0x74), uint8(0x1F), uint8(0x4B), uint8(0xBD), uint8(0x8B), uint8(0x8A),
    uint8(0x70), uint8(0x3E), uint8(0xB5), uint8(0x66), uint8(0x48), uint8(0x03), uint8(0xF6), uint8(0x0E), uint8(0x61), uint8(0x35), uint8(0x57), uint8(0xB9), uint8(0x86), uint8(0xC1), uint8(0x1D), uint8(0x9E),
    uint8(0xE1), uint8(0xF8), uint8(0x98), uint8(0x11), uint8(0x69), uint8(0xD9), uint8(0x8E), uint8(0x94), uint8(0x9B), uint8(0x1E), uint8(0x87), uint8(0xE9), uint8(0xCE), uint8(0x55), uint8(0x28), uint8(0xDF),
    uint8(0x8C), uint8(0xA1), uint8(0x89), uint8(0x0D), uint8(0xBF), uint8(0xE6), uint8(0x42), uint8(0x68), uint8(0x41), uint8(0x99), uint8(0x2D), uint8(0x0F), uint8(0xB0), uint8(0x54), uint8(0xBB), uint8(0x16)
])


def subBytes(state:block_t) -> block_t:
    st = array.copy(state)
    for i in range(16):
        st[i] = sbox[uint8.to_int(state[i])]
    return st

def shiftRow(i:rowindex_t,shift:rowindex_t,state:block_t) -> block_t:
    out = array.copy(state)
    out[i] = state[i + (4 * (shift % 4))]
    out[i+4] = state[i + (4 * ((shift + 1) % 4))]
    out[i+8] = state[i + (4 * ((shift + 2) % 4))]
    out[i+12] = state[i + (4 * ((shift + 3) % 4))]
    return out

def shiftRows(state:block_t) -> block_t:
    state = shiftRow(1,1,state)
    state = shiftRow(2,2,state)
    state = shiftRow(3,3,state)
    return state

def xtime(x:uint8_t) -> uint8_t:
    x1 = x << 1
    x7 = x >> 7
    x71 = x7 & uint8(1)
    x711b = x71 * uint8(0x1b)
    return x1 ^ x711b

def mixColumn(c:rowindex_t,state:block_t) -> block_t:
    i0 = 4 * c
    s0 = state[i0]
    s1 = state[i0+1]
    s2 = state[i0+2]
    s3 = state[i0+3]
    st = array.copy(state)
    tmp = s0 ^ s1 ^ s2 ^ s3
    st[i0]   = s0 ^ tmp ^ (xtime (s0 ^ s1))
    st[i0+1] = s1 ^ tmp ^ (xtime (s1 ^ s2))
    st[i0+2] = s2 ^ tmp ^ (xtime (s2 ^ s3))
    st[i0+3] = s3 ^ tmp ^ (xtime (s3 ^ s0))
    return st

def mixColumns(state:block_t) -> block_t:
    state = mixColumn(0,state)
    state = mixColumn(1,state)
    state = mixColumn(2,state)
    state = mixColumn(3,state)
    return state

def addRoundKey(state:block_t,key:block_t) -> block_t:
    out = array.copy(state)
    for i in range(16):
        out[i] ^= key[i]
    return out

def aes_enc(state:block_t,round_key:block_t) -> block_t:
    state = subBytes(state)
    state = shiftRows(state)
    state = mixColumns(state)
    state = addRoundKey(state,round_key)
    return state

def aes_enc_last(state:block_t,round_key:block_t) -> block_t:
    state = subBytes(state)
    state = shiftRows(state)
    state = addRoundKey(state,round_key)
    return state

def rounds(state:block_t,key:bytes_t(9*16)) -> block_t:
    out = array.copy(state)
    for i in range(9):
        out = aes_enc(out,key[16*i:16*i+16])
    return out

def block_cipher(input:block_t,key:bytes_t(11*16)) -> block_t:
    state = array.copy(input)
    k0 = key[0:16]
    k  = key[16:10*16]
    kn = key[10*16:11*16]
    state = addRoundKey(state,k0)
    state = rounds(state,k)
    state = aes_enc_last(state,kn)
    return state

def rotate_word(w:word_t) -> word_t:
    out = array.copy(w)
    out[0] = w[1]
    out[1] = w[2]
    out[2] = w[3]
    out[3] = w[0]
    return out

def sub_word(w:word_t) -> word_t:
    out = array.copy(w)
    out[0] = sbox[uint8.to_int(w[0])]
    out[1] = sbox[uint8.to_int(w[1])]
    out[2] = sbox[uint8.to_int(w[2])]
    out[3] = sbox[uint8.to_int(w[3])]
    return out

rcon : bytes_t(11) = array([uint8(0x8d), uint8(0x01), uint8(0x02), uint8(0x04), uint8(0x08), uint8(0x10), uint8(0x20), uint8(0x40), uint8(0x80), uint8(0x1b), uint8(0x36)])

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

def key_expansion(key:block_t) -> bytes_t(11*16):
    key_ex = array.create(11*16,uint8(0))
    key_ex[0:16] = key
    for j in range(40):
        i = j + 4
        key_ex[4*i:4*i+4] = key_expansion_word(key_ex[4*i-16:4*i-12],key_ex[4*i-4:4*i],i)
    return key_ex

def aes128_block(k:key_t,n:nonce_t,c:uint32_t) -> block_t:
    input = array.create(16,uint8(0))
    input[0:12] = n
    input[12:16] = bytes.from_uint32_be(c)
    key_ex = key_expansion(k)
    out = block_cipher(input,key_ex)
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


