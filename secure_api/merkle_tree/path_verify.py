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
    s = [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
          0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

    cws = [ 0 ] * 64
    for i in range(16):
        cws[i] = int.from_bytes(block[i*4:(i+1)*4], byteorder='big')
    for i in range(16, 64):
        t16, t15, t7, t2 = cws[i - 16], cws[i - 15], cws[i - 7], cws[i - 2]
        s1 = (t2 >> 17 | t2 << 15) ^ ((t2 >> 19 | t2 << 13) ^ t2 >> 10)
        s0 = (t15 >> 7 | t15 << 25) ^ ((t15 >> 18 | t15 << 14) ^ t15 >> 3)
        cws[i] = (s1 + t7 + s0 + t16) & 0xffffffff

    h = s.copy()
    for i in range(64):
        [a0, b0, c0, d0, e0, f0, g0, h03] = h
        w = cws[i]
        t1 = h03 + ((e0 >> 6 | e0 << 26) ^ ((e0 >> 11 | e0 << 21) ^ (e0 >> 25 | e0 << 7))) + ((e0 & f0) ^ (~e0 & g0)) + constants[i] + w
        t2 = ((a0 >> 2 | a0 << 30) ^ ((a0 >> 13 | a0 << 19) ^ (a0 >> 22 | a0 << 10))) + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)))
        h = [ (t1 + t2) & 0xffffffff, a0 & 0xffffffff, b0 & 0xffffffff, c0 & 0xffffffff,
              (d0 + t1) & 0xffffffff, e0 & 0xffffffff, f0 & 0xffffffff, g0 & 0xffffffff ]

    r = bytes()
    for i in range(8):
        r += ((s[i] + h[i]) & 0xffffffff).to_bytes(4, byteorder='big')
    return r

def recompute(k1, j1, path, ppos, acc, actd):
    # print([str(k1), str(j1), str(ppos), acc.hex()])
    if j1 != 0:
        nactd = actd or j1 % 2 == 1
        if k1 % 2 == 0:
            if j1 == k1 or (j1 == k1 + 1 and not actd):
                return recompute(k1 // 2, j1 // 2, path, ppos, acc, nactd)
            phash = path[ppos]
            acc = compress(acc + phash)
            return recompute(k1 // 2, j1 // 2, path, ppos + 1, acc, nactd)
        phash = path[ppos]
        acc = compress(phash + acc)
        return recompute(k1 // 2, j1 // 2, path, ppos + 1, acc, nactd)
    else:
        return acc

# offset = mtv.offset
def verify(offset, k1, j1, path, root):
  k2 = k1 - offset
  j2 = j1 - offset
  tmp = recompute(k2, j2, path, 1, path[0], False)
  return tmp == root


root = bytes.fromhex("50b2a21d29533d9ab25cbde1776c76db2c4eef059ad300e20335605942edb4a9")

path = [ bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000000"),
         bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000001"),
         bytes.fromhex("0fff9b7f003a6cffbe9db48e026410191e893f0e8519cc39262df228cde1f5d2") ]
print(verify(0, 0, 4, path, root))

path = [ bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000001"),
         bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000000"),
         bytes.fromhex("0fff9b7f003a6cffbe9db48e026410191e893f0e8519cc39262df228cde1f5d2") ]
print(verify(0, 1, 4, path, root))

path = [ bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000002"),
         bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000003"),
         bytes.fromhex("b40f7ca600e9693557a6a01a2a9288c200d14c5e76329d4d0d069cae776a096d") ]
print(verify(0, 2, 4, path, root))

path = [ bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000003"),
         bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000002"),
         bytes.fromhex("b40f7ca600e9693557a6a01a2a9288c200d14c5e76329d4d0d069cae776a096d") ]
print(verify(0, 3, 4, path, root))
