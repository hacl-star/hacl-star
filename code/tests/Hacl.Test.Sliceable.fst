module Hacl.Test.Sliceable

open FStar.UInt
open Lib.Sliceable

#set-options "--fuel 0 --ifuel 0 --z3rlimit 0"

private val circ : circuit 8 160
let circ =
fun i -> match i with
| 0 -> Input 7 | 1 -> Input 6 | 2 -> Input 5 | 3 -> Input 4 | 4 -> Input 3 | 5 -> Input 2
| 6 -> Input 1 | 7 -> Input 0 | 8 -> Xor 6 4 | 9 -> Xor 3 0 | 10 -> Xor 1 2 | 11 -> Xor 7 10
| 12 -> Xor 8 9 | 13 -> Xor 1 5 | 14 -> Xor 0 6 | 15 -> Xor 8 13 | 16 -> Xor 6 11 | 17 -> Xor 3 11 
| 18 -> Xor 7 12 | 19 -> Xor 12 13 | 20 -> Xor 2 5 | 21 -> Xor 10 12 | 22 -> Xor 5 14 | 23 -> Xor 0 5
| 24 -> Xor 7 15 | 25 -> Xor 6 5 | 26 -> Xor 9 25 | 27 -> Xor 11 22 | 28 -> Xor 8 20 | 29 -> Xor 0 11
| 30 -> Zeros | 31 -> Zeros | 32 -> Zeros | 33 -> Zeros | 34 -> Zeros | 35 -> Zeros
| 36 -> Zeros | 37 -> Zeros | 38 -> Zeros | 39 -> Zeros | 40 -> Zeros | 41 -> Zeros
| 42 -> Zeros | 43 -> Zeros | 44 -> Zeros | 45 -> Zeros | 46 -> Xor 28 12 | 47 -> Xor 28 14
| 48 -> Xor 14 26 | 49 -> Xor 23 21 | 50 -> Xor 29 24 | 51 -> And 26 12 | 52 -> And 27 18 | 53 -> Xor 19 51
| 54 -> And 17 7 | 55 -> Xor 54 51 | 56 -> And 14 28 | 57 -> And 16 11 | 58 -> Xor 47 56 | 59 -> And 29 24
| 60 -> Xor 59 56 | 61 -> And 9 15 | 62 -> And 48 46 | 63 -> Xor 62 61 | 64 -> And 23 21 | 65 -> Xor 64 61
| 66 -> Xor 53 52 | 67 -> Xor 55 49 | 68 -> Xor 58 57 | 69 -> Xor 60 65 | 70 -> Xor 66 63 | 71 -> Xor 67 65 
| 72 -> Xor 68 63 | 73 -> Xor 69 50 | 74 -> Xor 72 73 | 75 -> And 72 70 | 76 -> Xor 71 75 | 77 -> Xor 70 71 
| 78 -> Xor 73 75 | 79 -> And 78 77 | 80 -> And 76 74 | 81 -> And 70 73 | 82 -> And 77 81 | 83 -> Xor 77 75 
| 84 -> And 71 72 | 85 -> And 74 84 | 86 -> Xor 74 75 | 87 -> Xor 71 79 | 88 -> Xor 82 83 | 89 -> Xor 73 80 
| 90 -> Xor 85 86 | 91 -> Xor 88 90 | 92 -> Xor 87 89 | 93 -> Xor 87 88 | 94 -> Xor 89 90 | 95 -> Xor 92 91 
| 96 -> And 94 12 | 97 -> And 90 18 | 98 -> And 89 7 | 99 -> And 93 28 | 100 -> And 88 11 | 101 -> And 87 24 
| 102 -> And 92 15 | 103 -> And 95 46 | 104 -> And 91 21 | 105 -> And 94 26 | 106 -> And 90 27 | 107 -> And 89 17 
| 108 -> And 93 14 | 109 -> And 88 16 | 110 -> And 87 29 | 111 -> And 92 9 | 112 -> And 95 48 | 113 -> And 91 23 
| 114 -> Xor 111 112 | 115 -> Xor 100 106 | 116 -> Xor 103 114 | 117 -> Xor 105 115 | 118 -> Xor 98 108 | 119 -> Xor 96 99 
| 120 -> Xor 114 119 | 121 -> Xor 97 117 | 122 -> Xor 96 102 | 123 -> Xor 101 109 | 124 -> Xor 104 110  | 125 -> Xor 98 121 
| 126 -> Xor 118 124 | 127 -> Xor 107 115 | 128 -> Xor 99 102 | 129 -> Xor 117 128 | 130 -> Xor 113 126 | 131 -> Xor 111 122 
| 132 -> Xor 118 123 | 133 -> Zeros | 134 -> Zeros | 135 -> Xor 101 114 | 136 -> Zeros | 137 -> Zeros
| 138 -> Xor 100 108 | 139 -> Xor 119 127 | 140 -> Zeros | 141 -> Xor 104 123 | 142 -> Xor 138 141 | 143 -> Xor 100 122 
| 144 -> Zeros | 145 -> Xor 126 139 | 146 -> Zeros | 147 -> Xor 121 143 | 148 -> Xor 120 132 | 149 -> Not 148
| 150 -> Xor 116 142 | 151 -> Not 150 | 152 -> Xor 116 145 | 153 -> Xor 125 135 | 154 -> Xor 120 121 | 155 -> Xor 130 131
| 156 -> Not 155 | 157 -> Xor 116 147 | 158 -> Not 157 | 159 -> Xor 116 129

private val outputs : (i:nat{i<8}) -> (j:nat{j<160})
let outputs i =
match i with
| 0 -> 149
| 1 -> 151
| 2 -> 152
| 3 -> 153
| 4 -> 154
| 5 -> 156
| 6 -> 158
| 7 -> 159

private val subBytes_def (#n:nat) (#xN:sig n) (x:xNxM xN 8) : xNxM xN 8
let subBytes_def x = reduce_output (circuit_spec circ) 8 outputs x

private val sliceable_subBytes_def (_:unit) : Lemma (sliceable subBytes_def)
let sliceable_subBytes_def () = sliceable_feq (reduce_output (circuit_spec circ) 8 outputs) subBytes_def

let subBytes (#n:nat) (#xN:sig n) (x:xNxM xN 8) : xNxM xN 8 =
let a0 = index x 7 in let a1 = index x 6 in let a2 = index x 5 in let a3 = index x 4 in
let a4 = index x 3 in let a5 = index x 2 in let a6 = index x 1 in let a7 = index x 0 in
let a8 = xN.xor_ a6 a4 in let a9 = xN.xor_ a3 a0 in let a10 = xN.xor_ a1 a2 in let a11 = xN.xor_ a7 a10 in
let a12 = xN.xor_ a8 a9 in let a13 = xN.xor_ a1 a5 in let a14 = xN.xor_ a0 a6 in let a15 = xN.xor_ a8 a13 in
let a16 = xN.xor_ a6 a11 in let a17 = xN.xor_ a3 a11 in let a18 = xN.xor_ a7 a12 in let a19 = xN.xor_ a12 a13 in
let a20 = xN.xor_ a2 a5 in let a21 = xN.xor_ a10 a12 in let a22 = xN.xor_ a5 a14 in let a23 = xN.xor_ a0 a5 in
let a24 = xN.xor_ a7 a15 in let a25 = xN.xor_ a6 a5 in let a26 = xN.xor_ a9 a25 in let a27 = xN.xor_ a11 a22 in
let a28 = xN.xor_ a8 a20 in let a29 = xN.xor_ a0 a11 in let a30 = xN.zeros_ in let a31 = xN.zeros_ in
let a32 = xN.zeros_ in let a33 = xN.zeros_ in let a34 = xN.zeros_ in let a35 = xN.zeros_ in
let a36 = xN.zeros_ in let a37 = xN.zeros_ in let a38 = xN.zeros_ in let a39 = xN.zeros_ in
let a40 = xN.zeros_ in let a41 = xN.zeros_ in let a42 = xN.zeros_ in let a43 = xN.zeros_ in
let a44 = xN.zeros_ in let a45 = xN.zeros_ in let a46 = xN.xor_ a28 a12 in let a47 = xN.xor_ a28 a14 in
let a48 = xN.xor_ a14 a26 in let a49 = xN.xor_ a23 a21 in let a50 = xN.xor_ a29 a24 in let a51 = xN.and_ a26 a12 in
let a52 = xN.and_ a27 a18 in let a53 = xN.xor_ a19 a51 in let a54 = xN.and_ a17 a7 in let a55 = xN.xor_ a54 a51 in
let a56 = xN.and_ a14 a28 in let a57 = xN.and_ a16 a11 in let a58 = xN.xor_ a47 a56 in let a59 = xN.and_ a29 a24 in
let a60 = xN.xor_ a59 a56 in let a61 = xN.and_ a9 a15 in let a62 = xN.and_ a48 a46 in let a63 = xN.xor_ a62 a61 in
let a64 = xN.and_ a23 a21 in let a65 = xN.xor_ a64 a61 in let a66 = xN.xor_ a53 a52 in let a67 = xN.xor_ a55 a49 in
let a68 = xN.xor_ a58 a57 in let a69 = xN.xor_ a60 a65 in let a70 = xN.xor_ a66 a63 in let a71 = xN.xor_ a67 a65 in
let a72 = xN.xor_ a68 a63 in let a73 = xN.xor_ a69 a50 in let a74 = xN.xor_ a72 a73 in let a75 = xN.and_ a72 a70 in
let a76 = xN.xor_ a71 a75 in let a77 = xN.xor_ a70 a71 in let a78 = xN.xor_ a73 a75 in let a79 = xN.and_ a78 a77 in
let a80 = xN.and_ a76 a74 in let a81 = xN.and_ a70 a73 in let a82 = xN.and_ a77 a81 in let a83 = xN.xor_ a77 a75 in
let a84 = xN.and_ a71 a72 in let a85 = xN.and_ a74 a84 in let a86 = xN.xor_ a74 a75 in let a87 = xN.xor_ a71 a79 in
let a88 = xN.xor_ a82 a83 in let a89 = xN.xor_ a73 a80 in let a90 = xN.xor_ a85 a86 in let a91 = xN.xor_ a88 a90 in
let a92 = xN.xor_ a87 a89 in let a93 = xN.xor_ a87 a88 in let a94 = xN.xor_ a89 a90 in let a95 = xN.xor_ a92 a91 in
let a96 = xN.and_ a94 a12 in let a97 = xN.and_ a90 a18 in let a98 = xN.and_ a89 a7 in let a99 = xN.and_ a93 a28 in
let a100 = xN.and_ a88 a11 in let a101 = xN.and_ a87 a24 in let a102 = xN.and_ a92 a15 in let a103 = xN.and_ a95 a46 in
let a104 = xN.and_ a91 a21 in let a105 = xN.and_ a94 a26 in let a106 = xN.and_ a90 a27 in let a107 = xN.and_ a89 a17 in
let a108 = xN.and_ a93 a14 in let a109 = xN.and_ a88 a16 in let a110 = xN.and_ a87 a29 in let a111 = xN.and_ a92 a9 in
let a112 = xN.and_ a95 a48 in let a113 = xN.and_ a91 a23 in let a114 = xN.xor_ a111 a112 in let a115 = xN.xor_ a100 a106 in
let a116 = xN.xor_ a103 a114 in let a117 = xN.xor_ a105 a115 in let a118 = xN.xor_ a98 a108 in let a119 = xN.xor_ a96 a99 in
let a120 = xN.xor_ a114 a119 in let a121 = xN.xor_ a97 a117 in let a122 = xN.xor_ a96 a102 in let a123 = xN.xor_ a101 a109 in
let a124 = xN.xor_ a104 a110 in let a125 = xN.xor_ a98 a121 in let a126 = xN.xor_ a118 a124 in let a127 = xN.xor_ a107 a115 in
let a128 = xN.xor_ a99 a102 in let a129 = xN.xor_ a117 a128 in let a130 = xN.xor_ a113 a126 in let a131 = xN.xor_ a111 a122 in
let a132 = xN.xor_ a118 a123 in let a133 = xN.zeros_ in let a134 = xN.zeros_ in let a135 = xN.xor_ a101 a114 in
let a136 = xN.zeros_ in let a137 = xN.zeros_ in let a138 = xN.xor_ a100 a108 in let a139 = xN.xor_ a119 a127 in
let a140 = xN.zeros_ in let a141 = xN.xor_ a104 a123 in let a142 = xN.xor_ a138 a141 in let a143 = xN.xor_ a100 a122 in
let a144 = xN.zeros_ in let a145 = xN.xor_ a126 a139 in let a146 = xN.zeros_ in let a147 = xN.xor_ a121 a143 in
let a148 = xN.xor_ a120 a132 in let a149 = xN.not_ a148 in let a150 = xN.xor_ a116 a142 in let a151 = xN.not_ a150 in
let a152 = xN.xor_ a116 a145 in let a153 = xN.xor_ a125 a135 in let a154 = xN.xor_ a120 a121 in let a155 = xN.xor_ a130 a131 in
let a156 = xN.not_ a155 in let a157 = xN.xor_ a116 a147 in let a158 = xN.not_ a157 in let a159 = xN.xor_ a116 a129 in
let f (i:nat{i<8}) : xN.t =
  match i with
  | 0 -> a149 | 1 -> a151 | 2 -> a152 | 3 -> a153
  | 4 -> a154 | 5 -> a156 | 6 -> a158 | 7 -> a159
in
xNxM_mk xN 8 f

val subBytes_eq_def (_:unit) : Lemma (forall (n:nat) (xN:sig n) (x:xNxM xN 8) (i:nat{i<8}). subBytes x == subBytes_def x)
let subBytes_eq_def () = admit ()

val subBytes_sliceable (_:unit) : Lemma (sliceable subBytes)
#push-options "--fuel 1"
let subBytes_sliceable () =
  subBytes_eq_def ();
  sliceable_subBytes_def ();
  sliceable_feq subBytes_def subBytes
#pop-options

val sbox (i:nat{i<256}) : (r:nat{r<256})
let sbox i = match i with
|   0 -> 0x63 |   1 -> 0x7c |   2 -> 0x77 |   3 -> 0x7b |   4 -> 0xf2 |   5 -> 0x6b |   6 -> 0x6f |   7 -> 0xc5
|   8 -> 0x30 |   9 -> 0x01 |  10 -> 0x67 |  11 -> 0x2b |  12 -> 0xfe |  13 -> 0xd7 |  14 -> 0xab |  15 -> 0x76
|  16 -> 0xca |  17 -> 0x82 |  18 -> 0xc9 |  19 -> 0x7d |  20 -> 0xfa |  21 -> 0x59 |  22 -> 0x47 |  23 -> 0xf0
|  24 -> 0xad |  25 -> 0xd4 |  26 -> 0xa2 |  27 -> 0xaf |  28 -> 0x9c |  29 -> 0xa4 |  30 -> 0x72 |  31 -> 0xc0
|  32 -> 0xb7 |  33 -> 0xfd |  34 -> 0x93 |  35 -> 0x26 |  36 -> 0x36 |  37 -> 0x3f |  38 -> 0xf7 |  39 -> 0xcc
|  40 -> 0x34 |  41 -> 0xa5 |  42 -> 0xe5 |  43 -> 0xf1 |  44 -> 0x71 |  45 -> 0xd8 |  46 -> 0x31 |  47 -> 0x15
|  48 -> 0x04 |  49 -> 0xc7 |  50 -> 0x23 |  51 -> 0xc3 |  52 -> 0x18 |  53 -> 0x96 |  54 -> 0x05 |  55 -> 0x9a
|  56 -> 0x07 |  57 -> 0x12 |  58 -> 0x80 |  59 -> 0xe2 |  60 -> 0xeb |  61 -> 0x27 |  62 -> 0xb2 |  63 -> 0x75
|  64 -> 0x09 |  65 -> 0x83 |  66 -> 0x2c |  67 -> 0x1a |  68 -> 0x1b |  69 -> 0x6e |  70 -> 0x5a |  71 -> 0xa0
|  72 -> 0x52 |  73 -> 0x3b |  74 -> 0xd6 |  75 -> 0xb3 |  76 -> 0x29 |  77 -> 0xe3 |  78 -> 0x2f |  79 -> 0x84
|  80 -> 0x53 |  81 -> 0xd1 |  82 -> 0x00 |  83 -> 0xed |  84 -> 0x20 |  85 -> 0xfc |  86 -> 0xb1 |  87 -> 0x5b
|  88 -> 0x6a |  89 -> 0xcb |  90 -> 0xbe |  91 -> 0x39 |  92 -> 0x4a |  93 -> 0x4c |  94 -> 0x58 |  95 -> 0xcf
|  96 -> 0xd0 |  97 -> 0xef |  98 -> 0xaa |  99 -> 0xfb | 100 -> 0x43 | 101 -> 0x4d | 102 -> 0x33 | 103 -> 0x85
| 104 -> 0x45 | 105 -> 0xf9 | 106 -> 0x02 | 107 -> 0x7f | 108 -> 0x50 | 109 -> 0x3c | 110 -> 0x9f | 111 -> 0xa8
| 112 -> 0x51 | 113 -> 0xa3 | 114 -> 0x40 | 115 -> 0x8f | 116 -> 0x92 | 117 -> 0x9d | 118 -> 0x38 | 119 -> 0xf5
| 120 -> 0xbc | 121 -> 0xb6 | 122 -> 0xda | 123 -> 0x21 | 124 -> 0x10 | 125 -> 0xff | 126 -> 0xf3 | 127 -> 0xd2
| 128 -> 0xcd | 129 -> 0x0c | 130 -> 0x13 | 131 -> 0xec | 132 -> 0x5f | 133 -> 0x97 | 134 -> 0x44 | 135 -> 0x17
| 136 -> 0xc4 | 137 -> 0xa7 | 138 -> 0x7e | 139 -> 0x3d | 140 -> 0x64 | 141 -> 0x5d | 142 -> 0x19 | 143 -> 0x73
| 144 -> 0x60 | 145 -> 0x81 | 146 -> 0x4f | 147 -> 0xdc | 148 -> 0x22 | 149 -> 0x2a | 150 -> 0x90 | 151 -> 0x88
| 152 -> 0x46 | 153 -> 0xee | 154 -> 0xb8 | 155 -> 0x14 | 156 -> 0xde | 157 -> 0x5e | 158 -> 0x0b | 159 -> 0xdb
| 160 -> 0xe0 | 161 -> 0x32 | 162 -> 0x3a | 163 -> 0x0a | 164 -> 0x49 | 165 -> 0x06 | 166 -> 0x24 | 167 -> 0x5c
| 168 -> 0xc2 | 169 -> 0xd3 | 170 -> 0xac | 171 -> 0x62 | 172 -> 0x91 | 173 -> 0x95 | 174 -> 0xe4 | 175 -> 0x79
| 176 -> 0xe7 | 177 -> 0xc8 | 178 -> 0x37 | 179 -> 0x6d | 180 -> 0x8d | 181 -> 0xd5 | 182 -> 0x4e | 183 -> 0xa9
| 184 -> 0x6c | 185 -> 0x56 | 186 -> 0xf4 | 187 -> 0xea | 188 -> 0x65 | 189 -> 0x7a | 190 -> 0xae | 191 -> 0x08
| 192 -> 0xba | 193 -> 0x78 | 194 -> 0x25 | 195 -> 0x2e | 196 -> 0x1c | 197 -> 0xa6 | 198 -> 0xb4 | 199 -> 0xc6
| 200 -> 0xe8 | 201 -> 0xdd | 202 -> 0x74 | 203 -> 0x1f | 204 -> 0x4b | 205 -> 0xbd | 206 -> 0x8b | 207 -> 0x8a
| 208 -> 0x70 | 209 -> 0x3e | 210 -> 0xb5 | 211 -> 0x66 | 212 -> 0x48 | 213 -> 0x03 | 214 -> 0xf6 | 215 -> 0x0e
| 216 -> 0x61 | 217 -> 0x35 | 218 -> 0x57 | 219 -> 0xb9 | 220 -> 0x86 | 221 -> 0xc1 | 222 -> 0x1d | 223 -> 0x9e
| 224 -> 0xe1 | 225 -> 0xf8 | 226 -> 0x98 | 227 -> 0x11 | 228 -> 0x69 | 229 -> 0xd9 | 230 -> 0x8e | 231 -> 0x94
| 232 -> 0x9b | 233 -> 0x1e | 234 -> 0x87 | 235 -> 0xe9 | 236 -> 0xce | 237 -> 0x55 | 238 -> 0x28 | 239 -> 0xdf
| 240 -> 0x8c | 241 -> 0xa1 | 242 -> 0x89 | 243 -> 0x0d | 244 -> 0xbf | 245 -> 0xe6 | 246 -> 0x42 | 247 -> 0x68
| 248 -> 0x41 | 249 -> 0x99 | 250 -> 0x2d | 251 -> 0x0f | 252 -> 0xb0 | 253 -> 0x54 | 254 -> 0xbb | 255 -> 0x16

val subBytes_spec (#n:nat) (#xN:sig n) (x:xNxM xN 8) (j:nat{j<n}) :
  Lemma (column j (subBytes x) == of_uint (sbox (to_uint (column j x))))
let subBytes_spec x j =
  subBytes_sliceable ();
  assert_norm(bruteforce subBytes sbox)
