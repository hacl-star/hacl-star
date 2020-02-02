"""
Examples of Merkle path verification
"""

import binascii # hexlify
import struct # endianness conversions

constants = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def compress(block):
    """
    Compression function of SHA256

    :param block: block to compress
    """
    s = [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
          0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

    cws = [ 0 ] * 64
    for i in range(16):
        cws[i] = struct.unpack(">I", block[i*4:(i+1)*4])[0]
    for i in range(16, 64):
        t16, t15, t7, t2 = cws[i - 16], cws[i - 15], cws[i - 7], cws[i - 2]
        s1 = (t2 >> 17 | t2 << 15) ^ ((t2 >> 19 | t2 << 13) ^ t2 >> 10)
        s0 = (t15 >> 7 | t15 << 25) ^ ((t15 >> 18 | t15 << 14) ^ t15 >> 3)
        cws[i] = (s1 + t7 + s0 + t16) & 0xffffffff

    h = list(s)
    for i in range(64):
        [a0, b0, c0, d0, e0, f0, g0, h03] = h
        w = cws[i]
        t1 = h03 + ((e0 >> 6 | e0 << 26) ^ ((e0 >> 11 | e0 << 21) ^ (e0 >> 25 | e0 << 7))) + ((e0 & f0) ^ (~e0 & g0)) + constants[i] + w
        t2 = ((a0 >> 2 | a0 << 30) ^ ((a0 >> 13 | a0 << 19) ^ (a0 >> 22 | a0 << 10))) + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)))
        h = [ (t1 + t2) & 0xffffffff, a0 & 0xffffffff, b0 & 0xffffffff, c0 & 0xffffffff,
              (d0 + t1) & 0xffffffff, e0 & 0xffffffff, f0 & 0xffffffff, g0 & 0xffffffff ]

    r = bytearray()
    for i in range(8):
        r += struct.pack(">I",(s[i] + h[i]) & 0xffffffff)
    return r

def recompute_rec(i, n, path, pi, tag, actd):
    """
    Recursive recomputation of tag

    :param i: index to recompute
    :param n: size of the tree
    :param path: neighbouring hashes along branches
    :param pi: current path index
    :param tag: current tag
    :param actd: flag
    :returns: recomputed tag
    """
    if n < 0 or i > n or not len(path) or pi < 0 or pi > len(path):
        return []

    # print([str(i), str(n), str(pi), binascii.hexlify(tag)])
    if n == 0:
        return tag
    nactd = actd or n % 2 == 1
    if i % 2 == 0:
        if n == i or (n == i + 1 and not actd):
            return recompute_rec(i // 2, n // 2, path, pi, tag, nactd)
        tag = compress(tag + path[pi])
    else:
        tag = compress(path[pi] + tag)
    return recompute_rec(i // 2, n // 2, path, pi + 1, tag, nactd)

def recompute(i, n, path):
    """
    Iterative recomputation of tag

    :param i: index to recompute
    :param n: size of the tree
    :param path: neighbouring hashes along branches
    """
    if n < 0 or i > n or not len(path):
        return []

    tag = path[0]
    pi = 1
    inside = True
    while n > 0:
        # print([str(i), str(n), str(pi), binascii.hexlify(tag)])
        left = i % 2 == 1 # going up to the left
        skip = i == n or (i + 1 == n and inside) # no more hashes to the right
        if left or not skip:
            assert (pi < len(path))
            if left:
                tag = compress(path[pi] + tag)
            else:
                tag = compress(tag + path[pi])
            pi += 1
        inside &= n % 2 == 0
        i //= 2
        n //= 2
    return tag

def verify(offset, i, n, path, root):
    """
    Merkle path verification

    :param offset: 64-bit offset of the internal 32-bit tree
    :param i: index to verify
    :param n: size of the tree
    :param path: neighbouring hashes along branches
    :param root: root of the tree
    :returns: True for success, False otherwise.
    """
    io = i - offset
    no = n - offset
    tag_rec = recompute_rec(io, no, path, 1, path[0], False)
    tag = recompute(io, no, path)
    assert(tag_rec == tag)
    return tag == root

def tests():
    """Various test inputs"""

    root = bytearray.fromhex("50b2a21d29533d9ab25cbde1776c76db2c4eef059ad300e20335605942edb4a9")

    path = [ bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000000"),
             bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000001"),
             bytearray.fromhex("0fff9b7f003a6cffbe9db48e026410191e893f0e8519cc39262df228cde1f5d2") ]
    v1 = verify(0, 0, 4, path, root)

    path = [ bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000001"),
             bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000000"),
             bytearray.fromhex("0fff9b7f003a6cffbe9db48e026410191e893f0e8519cc39262df228cde1f5d2") ]
    v2 = verify(0, 1, 4, path, root)

    path = [ bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000002"),
             bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000003"),
             bytearray.fromhex("b40f7ca600e9693557a6a01a2a9288c200d14c5e76329d4d0d069cae776a096d") ]
    v3 = verify(0, 2, 4, path, root)

    path = [ bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000003"),
             bytearray.fromhex("0000000000000000000000000000000000000000000000000000000000000002"),
             bytearray.fromhex("b40f7ca600e9693557a6a01a2a9288c200d14c5e76329d4d0d069cae776a096d") ]
    v4 = verify(0, 3, 4, path, root)

    if v1 and v2 and v3 and v4:
        print("All ok.")
    else:
        print("Verification failure.")

if __name__ == '__main__':
    tests()
