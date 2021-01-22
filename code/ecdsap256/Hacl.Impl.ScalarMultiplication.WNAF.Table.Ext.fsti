module Hacl.Impl.ScalarMultiplication.WNAF.Table.Ext	

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul


val getUInt64: index: size_t {v index < 3456 - 4} -> Stack (lbuffer uint64 (size 4))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)


(* 

prime = 2**256 - 2**224 + 2**192 + 2**96 -1

def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

def toD(x):
    return x * power_mod (2 ** 256, 1, prime) % prime

def fromD(x):
    return x * power_mod (2 ** 256, prime - 2, prime) % prime

def toFakeAffine(p):
    x, y = p 
    multiplier = power_mod (2 ** 256, prime - 2, prime) 
    x = x * multiplier * multiplier % prime
    y = y * multiplier * multiplier * multiplier % prime
    return (x, y)

p256 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
a256 = p256 - 3
b256 = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
qq = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
FF = GF(p256)

EC = EllipticCurve([FF(a256), FF(b256)])

EC.set_order(qq)

G = EC(FF(gx), FF(gy))

import __future__ 
def printf(p):
    x, y = p 
    for i in range(4):
        print(str(hex((Integer(x) >> (i * 64)) % 2 ** 64)) + "U; ", end = "")
    print("")
    for i in range(4):
        print(str (hex((Integer(y) >> (i * 64)) % 2 ** 64)) + "U; ", end = "")
    print("\n")
    
for j in range(27):
    print("")
    for i in range(1, 33, 2):
        pxD = (2 ** (j * 10) * i * G).xy()[0]
        pyD = (2 ** (j * 10) * i * G).xy()[1]
        printf (toFakeAffine((toD (pxD), toD (pyD)))) *)