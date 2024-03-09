module Hacl.Impl.AES.SubBytes
friend Lib.Sequence
friend Lib.LoopCombinators
friend FStar.Seq.Base

module B = Lib.Buffer
module IT = Lib.IntTypes
module S = Lib.Sliceable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Tactics

#set-options "--fuel 0 --ifuel 0"

inline_for_extraction noextract
let sbox s =
match s with
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

inline_for_extraction noextract
let sbox_inv s =
match s with
|   0 -> 0x52 |   1 -> 0x09 |   2 -> 0x6a |   3 -> 0xd5 |   4 -> 0x30 |   5 -> 0x36 |   6 -> 0xa5 |   7 -> 0x38
|   8 -> 0xbf |   9 -> 0x40 |  10 -> 0xa3 |  11 -> 0x9e |  12 -> 0x81 |  13 -> 0xf3 |  14 -> 0xd7 |  15 -> 0xfb
|  16 -> 0x7c |  17 -> 0xe3 |  18 -> 0x39 |  19 -> 0x82 |  20 -> 0x9b |  21 -> 0x2f |  22 -> 0xff |  23 -> 0x87
|  24 -> 0x34 |  25 -> 0x8e |  26 -> 0x43 |  27 -> 0x44 |  28 -> 0xc4 |  29 -> 0xde |  30 -> 0xe9 |  31 -> 0xcb
|  32 -> 0x54 |  33 -> 0x7b |  34 -> 0x94 |  35 -> 0x32 |  36 -> 0xa6 |  37 -> 0xc2 |  38 -> 0x23 |  39 -> 0x3d
|  40 -> 0xee |  41 -> 0x4c |  42 -> 0x95 |  43 -> 0x0b |  44 -> 0x42 |  45 -> 0xfa |  46 -> 0xc3 |  47 -> 0x4e
|  48 -> 0x08 |  49 -> 0x2e |  50 -> 0xa1 |  51 -> 0x66 |  52 -> 0x28 |  53 -> 0xd9 |  54 -> 0x24 |  55 -> 0xb2
|  56 -> 0x76 |  57 -> 0x5b |  58 -> 0xa2 |  59 -> 0x49 |  60 -> 0x6d |  61 -> 0x8b |  62 -> 0xd1 |  63 -> 0x25
|  64 -> 0x72 |  65 -> 0xf8 |  66 -> 0xf6 |  67 -> 0x64 |  68 -> 0x86 |  69 -> 0x68 |  70 -> 0x98 |  71 -> 0x16
|  72 -> 0xd4 |  73 -> 0xa4 |  74 -> 0x5c |  75 -> 0xcc |  76 -> 0x5d |  77 -> 0x65 |  78 -> 0xb6 |  79 -> 0x92
|  80 -> 0x6c |  81 -> 0x70 |  82 -> 0x48 |  83 -> 0x50 |  84 -> 0xfd |  85 -> 0xed |  86 -> 0xb9 |  87 -> 0xda
|  88 -> 0x5e |  89 -> 0x15 |  90 -> 0x46 |  91 -> 0x57 |  92 -> 0xa7 |  93 -> 0x8d |  94 -> 0x9d |  95 -> 0x84
|  96 -> 0x90 |  97 -> 0xd8 |  98 -> 0xab |  99 -> 0x00 | 100 -> 0x8c | 101 -> 0xbc | 102 -> 0xd3 | 103 -> 0x0a
| 104 -> 0xf7 | 105 -> 0xe4 | 106 -> 0x58 | 107 -> 0x05 | 108 -> 0xb8 | 109 -> 0xb3 | 110 -> 0x45 | 111 -> 0x06
| 112 -> 0xd0 | 113 -> 0x2c | 114 -> 0x1e | 115 -> 0x8f | 116 -> 0xca | 117 -> 0x3f | 118 -> 0x0f | 119 -> 0x02
| 120 -> 0xc1 | 121 -> 0xaf | 122 -> 0xbd | 123 -> 0x03 | 124 -> 0x01 | 125 -> 0x13 | 126 -> 0x8a | 127 -> 0x6b
| 128 -> 0x3a | 129 -> 0x91 | 130 -> 0x11 | 131 -> 0x41 | 132 -> 0x4f | 133 -> 0x67 | 134 -> 0xdc | 135 -> 0xea
| 136 -> 0x97 | 137 -> 0xf2 | 138 -> 0xcf | 139 -> 0xce | 140 -> 0xf0 | 141 -> 0xb4 | 142 -> 0xe6 | 143 -> 0x73
| 144 -> 0x96 | 145 -> 0xac | 146 -> 0x74 | 147 -> 0x22 | 148 -> 0xe7 | 149 -> 0xad | 150 -> 0x35 | 151 -> 0x85
| 152 -> 0xe2 | 153 -> 0xf9 | 154 -> 0x37 | 155 -> 0xe8 | 156 -> 0x1c | 157 -> 0x75 | 158 -> 0xdf | 159 -> 0x6e
| 160 -> 0x47 | 161 -> 0xf1 | 162 -> 0x1a | 163 -> 0x71 | 164 -> 0x1d | 165 -> 0x29 | 166 -> 0xc5 | 167 -> 0x89
| 168 -> 0x6f | 169 -> 0xb7 | 170 -> 0x62 | 171 -> 0x0e | 172 -> 0xaa | 173 -> 0x18 | 174 -> 0xbe | 175 -> 0x1b
| 176 -> 0xfc | 177 -> 0x56 | 178 -> 0x3e | 179 -> 0x4b | 180 -> 0xc6 | 181 -> 0xd2 | 182 -> 0x79 | 183 -> 0x20
| 184 -> 0x9a | 185 -> 0xdb | 186 -> 0xc0 | 187 -> 0xfe | 188 -> 0x78 | 189 -> 0xcd | 190 -> 0x5a | 191 -> 0xf4
| 192 -> 0x1f | 193 -> 0xdd | 194 -> 0xa8 | 195 -> 0x33 | 196 -> 0x88 | 197 -> 0x07 | 198 -> 0xc7 | 199 -> 0x31
| 200 -> 0xb1 | 201 -> 0x12 | 202 -> 0x10 | 203 -> 0x59 | 204 -> 0x27 | 205 -> 0x80 | 206 -> 0xec | 207 -> 0x5f
| 208 -> 0x60 | 209 -> 0x51 | 210 -> 0x7f | 211 -> 0xa9 | 212 -> 0x19 | 213 -> 0xb5 | 214 -> 0x4a | 215 -> 0x0d
| 216 -> 0x2d | 217 -> 0xe5 | 218 -> 0x7a | 219 -> 0x9f | 220 -> 0x93 | 221 -> 0xc9 | 222 -> 0x9c | 223 -> 0xef
| 224 -> 0xa0 | 225 -> 0xe0 | 226 -> 0x3b | 227 -> 0x4d | 228 -> 0xae | 229 -> 0x2a | 230 -> 0xf5 | 231 -> 0xb0
| 232 -> 0xc8 | 233 -> 0xeb | 234 -> 0xbb | 235 -> 0x3c | 236 -> 0x83 | 237 -> 0x53 | 238 -> 0x99 | 239 -> 0x61
| 240 -> 0x17 | 241 -> 0x2b | 242 -> 0x04 | 243 -> 0x7e | 244 -> 0xba | 245 -> 0x77 | 246 -> 0xd6 | 247 -> 0x26
| 248 -> 0xe1 | 249 -> 0x69 | 250 -> 0x14 | 251 -> 0x63 | 252 -> 0x55 | 253 -> 0x21 | 254 -> 0x0c | 255 -> 0x7d

let sbox_inv_theorem s = assert_norm (S.bruteforce_aux 8 (fun i -> sbox_inv (sbox i) = i) == true)

// http://cs-www.cs.yale.edu/homes/peralta/CircuitStuff/CMT.html
inline_for_extraction noextract
let sub_bytes_circ_size : nat = 121
inline_for_extraction noextract
private let sub_bytes_circ : S.circuit 8 sub_bytes_circ_size =
fun i -> match i with
| 0 -> S.Input 7 | 1 -> S.Input 6 | 2 -> S.Input 5 | 3 -> S.Input 4
| 4 -> S.Input 3 | 5 -> S.Input 2 | 6 -> S.Input 1 | 7 -> S.Input 0
|   8 ->  S.Xor   3   5 |   9 ->  S.Xor   0   6 |  10 ->  S.Xor   0   3 |  11 ->  S.Xor   0   5
|  12 ->  S.Xor   1   2 |  13 ->  S.Xor  12   7 |  14 ->  S.Xor  13   3 |  15 ->  S.Xor   9   8
|  16 ->  S.Xor  13   0 |  17 ->  S.Xor  13   6 |  18 ->  S.Xor  17  11 |  19 ->  S.Xor   4  15
|  20 ->  S.Xor  19   5 |  21 ->  S.Xor  19   1 |  22 ->  S.Xor  20   7 |  23 ->  S.Xor  20  12
|  24 ->  S.Xor  21  10 |  25 ->  S.Xor   7  24 |  26 ->  S.Xor  23  24 |  27 ->  S.Xor  23  11
|  28 ->  S.Xor  12  24 |  29 ->  S.Xor   9  28 |  30 ->  S.Xor   0  28 |  31 ->  S.And  15  20
|  32 ->  S.And  18  22 |  33 ->  S.Xor  32  31 |  34 ->  S.And  14   7 |  35 ->  S.Xor  34  31
|  36 ->  S.And   9  28 |  37 ->  S.And  17  13 |  38 ->  S.Xor  37  36 |  39 ->  S.And  16  25
|  40 ->  S.Xor  39  36 |  41 ->  S.And  10  24 |  42 ->  S.And   8  26 |  43 ->  S.Xor  42  41
|  44 ->  S.And  11  23 |  45 ->  S.Xor  44  41 |  46 ->  S.Xor  33  21 |  47 ->  S.Xor  35  45
|  48 ->  S.Xor  38  43 |  49 ->  S.Xor  40  45 |  50 ->  S.Xor  46  43 |  51 ->  S.Xor  47  27
|  52 ->  S.Xor  48  29 |  53 ->  S.Xor  49  30 |  54 ->  S.Xor  50  51 |  55 ->  S.And  50  52
|  56 ->  S.Xor  53  55 |  57 ->  S.And  54  56 |  58 ->  S.Xor  57  51 |  59 ->  S.Xor  52  53
|  60 ->  S.Xor  51  55 |  61 ->  S.And  60  59 |  62 ->  S.Xor  61  53 |  63 ->  S.Xor  52  62
|  64 ->  S.Xor  56  62 |  65 ->  S.And  53  64 |  66 ->  S.Xor  65  63 |  67 ->  S.Xor  56  65
|  68 ->  S.And  58  67 |  69 ->  S.Xor  54  68 |  70 ->  S.Xor  69  66 |  71 ->  S.Xor  58  62
|  72 ->  S.Xor  58  69 |  73 ->  S.Xor  62  66 |  74 ->  S.Xor  71  70 |  75 ->  S.And  73  20
|  76 ->  S.And  66  22 |  77 ->  S.And  62   7 |  78 ->  S.And  72  28 |  79 ->  S.And  69  13
|  80 ->  S.And  58  25 |  81 ->  S.And  71  24 |  82 ->  S.And  74  26 |  83 ->  S.And  70  23
|  84 ->  S.And  73  15 |  85 ->  S.And  66  18 |  86 ->  S.And  62  14 |  87 ->  S.And  72   9
|  88 ->  S.And  69  17 |  89 ->  S.And  58  16 |  90 ->  S.And  71  10 |  91 ->  S.And  74   8
|  92 ->  S.And  70  11 |  93 ->  S.Xor  90  91 |  94 ->  S.Xor  85  93 |  95 ->  S.Xor  84  94
|  96 ->  S.Xor  75  77 |  97 ->  S.Xor  76  75 |  98 ->  S.Xor  78  79 |  99 ->  S.Xor  87  96
| 100 ->  S.Xor  82  98 | 101 ->  S.Xor  83  99 | 102 ->  S.Xor 100 101 | 103 ->  S.Xor  98  97
| 104 ->  S.Xor  78  80 | 105 ->  S.Xor  88  93 | 106 ->  S.Xor  96 104 | 107 ->  S.Xor  95 103
| 108 ->  S.Xor  81 100 | 109 ->  S.Xor  89 102 | 110 ->  S.Xor 105 106 | 111 -> S.Xnor  87 110
| 112 ->  S.Xor  90 108 | 113 ->  S.Xor  94  86 | 114 ->  S.Xor  95 108 | 115 -> S.Xnor 102 110
| 116 ->  S.Xor 106 107 | 117 -> S.Xnor 107 108 | 118 ->  S.Xor 109 112 | 119 -> S.Xnor 118  92
| 120 ->  S.Xor 113 109
inline_for_extraction noextract
let sub_bytes_circ_outputs (i:nat{i<8}) : (j:nat{j<sub_bytes_circ_size}) =
match i with
| 0 -> 111
| 1 -> 115
| 2 -> 120
| 3 -> 116
| 4 -> 107
| 5 -> 119
| 6 -> 117
| 7 -> 114

inline_for_extraction noextract
let sub_bytes #n #xN x =
  S.reduce_output (S.circuit_spec sub_bytes_circ) 8 sub_bytes_circ_outputs x

let sub_bytes_sliceable : squash (S.sliceable sub_bytes) =
  S.reduce_output_sliceable (S.circuit_spec sub_bytes_circ) 8 sub_bytes_circ_outputs

let sub_bytes_bruteforce_lemma (_:unit) : Lemma (
    S.bruteforce_rev sub_bytes sbox == true
  ) =
  assert (
    S.bruteforce_rev sub_bytes sbox == true
  ) by (
    norm [ delta; zeta; primops; iota; nbe ];
    trefl ()
  )

let sub_bytes_theorem (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) (j:nat{j<n})
  =
  sub_bytes_bruteforce_lemma ();
  S.bruteforce_rev_lemma sub_bytes sbox

#push-options "--z3rlimit 20"
let sub_bytes64x8 st0 st1 st2 st3 st4 st5 st6 st7 =
  push_frame();
  let input : B.lbuffer u64.t 8ul = B.create _ u64.zeros_ in
  B.create8 input st0 st1 st2 st3 st4 st5 st6 st7;
  let output : B.lbuffer u64.t 8ul = B.create _ u64.zeros_ in
  let h0 = FStar.HyperStack.ST.get () in
  S.reduce_output_lowstar
    (S.circuit_spec sub_bytes_circ) u64
    (S.circuit_lowstar sub_bytes_circ u64)
    8 sub_bytes_circ_outputs
    input output;
  let h1 = FStar.HyperStack.ST.get () in
  assert(S.xNxM_of_lbuffer h1 output == sub_bytes (S.xNxM_of_lbuffer h0 input));
  let o0:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 0}) = B.index output 0ul in
  let o1:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 1}) = B.index output 1ul in
  let o2:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 2}) = B.index output 2ul in
  let o3:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 3}) = B.index output 3ul in
  let o4:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 4}) = B.index output 4ul in
  let o5:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 5}) = B.index output 5ul in
  let o6:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 6}) = B.index output 6ul in
  let o7:(v:u64.t{v == S.index (sub_bytes (S.xNxM_of_lbuffer h0 input)) 7}) = B.index output 7ul in
  S.xNxM_eq_intro
    (S.xNxM_of_lbuffer h0 input)
    (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7);
  S.xNxM_eq_intro
    (S.uNx8_mk o0 o1 o2 o3 o4 o5 o6 o7)
    (sub_bytes (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7));
  pop_frame();
  (o0, o1, o2, o3, o4, o5, o6, o7)
#pop-options

// http://cs-www.cs.yale.edu/homes/peralta/CircuitStuff/CMT.html
inline_for_extraction noextract
let sub_bytes_inv_circ_size : nat = 129
inline_for_extraction noextract
private let sub_bytes_inv_circ : S.circuit 8 sub_bytes_inv_circ_size =
fun i -> match i with
| 0 -> S.Input 0 | 1 -> S.Input 1 | 2 -> S.Input 2 | 3 -> S.Input 3
| 4 -> S.Input 4 | 5 -> S.Input 5 | 6 -> S.Input 6 | 7 -> S.Input 7
|   8 -> S.Xor    0   3 |   9 -> S.Xnor   1   3 |  10 -> S.Xor    0   9 |  11 -> S.Xor    6   7
|  12 -> S.Xor    9  11 |  13 -> S.Xnor   2  12 |  14 -> S.Xor    3   4 |  15 -> S.Xnor   7  14
|  16 -> S.Xor   12  14 |  17 -> S.Xnor   0   2 |  18 -> S.Xor    5  17 |  19 -> S.Xor    8   9
|  20 -> S.Xor   12  16 |  21 -> S.Xor   10  15 |  22 -> S.Xor   18  13 |  23 -> S.Xor    8  12
|  24 -> S.Xor    9  16 |  25 -> S.Xor   20  19 |  26 -> S.Xor   10  18 |  27 -> S.Xor   15  13
|  28 -> S.Xor   22  21 |  29 -> S.Xor   20  22 |  30 -> S.Xor   24  27 |  31 -> S.Xor   16  13
|  32 -> S.Xor   19  21 |  33 -> S.And   23  26 |  34 -> S.And    8  10 |  35 -> S.Xor   29  33
|  36 -> S.And   12  18 |  37 -> S.Xor   36  33 |  38 -> S.And   24  27 |  39 -> S.And    9  15
|  40 -> S.Xor   30  38 |  41 -> S.And   16  13 |  42 -> S.Xor   41  38 |  43 -> S.And   20  22
|  44 -> S.And   25  28 |  45 -> S.Xor   44  43 |  46 -> S.And   19  21 |  47 -> S.Xor   46  43
|  48 -> S.Xor   35  34 |  49 -> S.Xor   37  32 |  50 -> S.Xor   40  39 |  51 -> S.Xor   42  47
|  52 -> S.Xor   48  45 |  53 -> S.Xor   49  47 |  54 -> S.Xor   50  45 |  55 -> S.Xor   51  31
|  56 -> S.Xor   54  55 |  57 -> S.And   54  52 |  58 -> S.Xor   53  57 |  59 -> S.Xor   52  53
|  60 -> S.Xor   55  57 |  61 -> S.And   60  59 |  62 -> S.And   58  56 |  63 -> S.Xor   55  62
|  64 -> S.Xor   53  61 |  65 -> S.And   52  55 |  66 -> S.And   59  65 |  67 -> S.Xor   59  57
|  68 -> S.Xor   66  67 |  69 -> S.And   53  54 |  70 -> S.And   56  69 |  71 -> S.Xor   56  57
|  72 -> S.Xor   70  71 |  73 -> S.Xor   68  72 |  74 -> S.Xor   64  63 |  75 -> S.Xor   64  68
|  76 -> S.Xor   63  72 |  77 -> S.Xor   74  73 |  78 -> S.And   76  26 |  79 -> S.And   72  10
|  80 -> S.And   63  18 |  81 -> S.And   75  27 |  82 -> S.And   68  15 |  83 -> S.And   64  13
|  84 -> S.And   74  22 |  85 -> S.And   77  28 |  86 -> S.And   73  21 |  87 -> S.And   76  23
|  88 -> S.And   72   8 |  89 -> S.And   63  12 |  90 -> S.And   75  24 |  91 -> S.And   68   9
|  92 -> S.And   64  16 |  93 -> S.And   74  20 |  94 -> S.And   77  25 |  95 -> S.And   73  19
|  96 -> S.Xor   79  78 |  97 -> S.Xor   80  78 |  98 -> S.Xor   82  81 |  99 -> S.Xor   83  81
| 100 -> S.Xor   85  84 | 101 -> S.Xor   86  84 | 102 -> S.Xor   96 100 | 103 -> S.Xor   97 101
| 104 -> S.Xor   98 100 | 105 -> S.Xor   99 101 | 106 -> S.Xor   88  87 | 107 -> S.Xor   89  87
| 108 -> S.Xor   91  90 | 109 -> S.Xor   92  90 | 110 -> S.Xor   94  93 | 111 -> S.Xor   95  93
| 112 -> S.Xor  106 110 | 113 -> S.Xor  107 111 | 114 -> S.Xor  108 110 | 115 -> S.Xor  109 111
| 116 -> S.Xor  103 114 | 117 -> S.Xor  104 114 | 118 -> S.Xor  105 114 | 119 -> S.Xor  102 104
| 120 -> S.Xor  118 119 | 121 -> S.Xor  112 115 | 122 -> S.Xor  119 121 | 123 -> S.Xor  116 122
| 124 -> S.Xor  103 113 | 125 -> S.Xor  122 124 | 126 -> S.Xor  102 112 | 127 -> S.Xor  120 124
| 128 -> S.Xor  126 127
inline_for_extraction noextract
let sub_bytes_inv_circ_outputs (i:nat{i<8}) : (j:nat{j<sub_bytes_inv_circ_size}) =
match i with
| 0 -> 118
| 1 -> 123
| 2 -> 125
| 3 -> 116
| 4 -> 128
| 5 -> 120
| 6 -> 117
| 7 -> 113

inline_for_extraction noextract
let sub_bytes_inv #n #xN x =
  S.reduce_output (S.circuit_spec sub_bytes_inv_circ) 8 sub_bytes_inv_circ_outputs x

let sub_bytes_inv_sliceable : squash (S.sliceable sub_bytes_inv) =
  S.reduce_output_sliceable (S.circuit_spec sub_bytes_inv_circ) 8 sub_bytes_inv_circ_outputs

let sub_bytes_inv_bruteforce_lemma (_:unit) : Lemma (
    S.bruteforce sub_bytes_inv sbox_inv == true
  ) =
  assert (
    S.bruteforce sub_bytes_inv sbox_inv == true
  ) by (
    norm [ delta; zeta; primops; iota; nbe ];
    trefl ()
  )

#push-options "--z3rlimit 20"
let sub_bytes_inv_theorem (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) (j:nat{j<n})
  =
  sub_bytes_inv_bruteforce_lemma ();
  S.bruteforce_lemma sub_bytes_inv sbox_inv
#pop-options

#push-options "--z3rlimit 20"
let sub_bytes_inv64x8 st0 st1 st2 st3 st4 st5 st6 st7 =
  push_frame();
  let input : B.lbuffer u64.t 8ul = B.create _ u64.zeros_ in
  B.create8 input st0 st1 st2 st3 st4 st5 st6 st7;
  let output : B.lbuffer u64.t 8ul = B.create _ u64.zeros_ in
  let h0 = FStar.HyperStack.ST.get () in
  S.reduce_output_lowstar
    (S.circuit_spec sub_bytes_inv_circ) u64
    (S.circuit_lowstar sub_bytes_inv_circ u64)
    8 sub_bytes_inv_circ_outputs
    input output;
  let h1 = FStar.HyperStack.ST.get () in
  assert(S.xNxM_of_lbuffer h1 output == sub_bytes_inv (S.xNxM_of_lbuffer h0 input));
  let o0:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 0}) = B.index output 0ul in
  let o1:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 1}) = B.index output 1ul in
  let o2:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 2}) = B.index output 2ul in
  let o3:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 3}) = B.index output 3ul in
  let o4:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 4}) = B.index output 4ul in
  let o5:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 5}) = B.index output 5ul in
  let o6:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 6}) = B.index output 6ul in
  let o7:(v:u64.t{v == S.index (sub_bytes_inv (S.xNxM_of_lbuffer h0 input)) 7}) = B.index output 7ul in
  S.xNxM_eq_intro
    (S.xNxM_of_lbuffer h0 input)
    (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7);
  S.xNxM_eq_intro
    (S.uNx8_mk o0 o1 o2 o3 o4 o5 o6 o7)
    (sub_bytes_inv (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7));
  pop_frame();
  (o0, o1, o2, o3, o4, o5, o6, o7)
#pop-options
