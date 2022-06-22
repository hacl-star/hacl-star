module Hacl.Impl.AES.SubBytes
friend Lib.Sequence
friend Lib.LoopCombinators
friend FStar.Seq.Base

open FStar.HyperStack.ST
open FStar.HyperStack

module IT = Lib.IntTypes
module B = Lib.Buffer
module S = Lib.Sliceable

#set-options "--fuel 1 --ifuel 1"

inline_for_extraction noextract
let sbox (s:nat{s<256}) : (r:nat{r<256}) =
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

// http://cs-www.cs.yale.edu/homes/peralta/CircuitStuff/CMT.html
inline_for_extraction noextract
let circ_size : nat = 121
inline_for_extraction noextract
private let circ : S.circuit 8 circ_size =
fun i -> match i with
| 0 -> S.Input 0 | 1 -> S.Input 1 | 2 -> S.Input 2 | 3 -> S.Input 3
| 4 -> S.Input 4 | 5 -> S.Input 5 | 6 -> S.Input 6 | 7 -> S.Input 7
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
let circ_outputs (i:nat{i<8}) : (j:nat{j<circ_size}) =
match i with
| 0 -> 114
| 1 -> 117
| 2 -> 119
| 3 -> 107
| 4 -> 116
| 5 -> 120
| 6 -> 115
| 7 -> 111

inline_for_extraction noextract
let sub_bytes_spec (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) : S.xNxM xN 8 =
  S.reduce_output (S.circuit_spec circ) 8 circ_outputs x

open FStar.Tactics

let sub_bytes_sliceable : squash (S.sliceable sub_bytes_spec) =
  S.reduce_output_sliceable (S.circuit_spec circ) 8 circ_outputs

let sub_bytes_bruteforce_lemma (_:unit) : Lemma (
    S.bruteforce sub_bytes_spec sbox == true
  ) =
  assert (
    S.bruteforce sub_bytes_spec sbox == true
  ) by (
    norm [ delta; zeta; primops; iota; nbe ];
    trefl ()
  )

let sub_bytes_spec_theorem (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) (j:nat{j<n})
  : Lemma ( S.column j (sub_bytes_spec x) == S.of_uint (sbox (S.to_uint (S.column j x))) )
  =
  sub_bytes_bruteforce_lemma ()

inline_for_extraction noextract
private let u64 = S.uN IT.U64 IT.SEC

#push-options "--z3rlimit 200"
let sub_bytes64x8
  (st0:u64.t) (st1:u64.t) (st2:u64.t) (st3:u64.t)
  (st4:u64.t) (st5:u64.t) (st6:u64.t) (st7:u64.t) :
    Stack
      (u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t)
      (fun _ -> True)
      (fun h0 (o0,o1,o2,o3,o4,o5,o6,o7) h1 ->
        B.modifies LowStar.Monotonic.Buffer.loc_none h0 h1
        ///\ S.uNx8_mk o0 o1 o2 o3 o4 o5 o6 o7
        //  == sub_bytes_spec (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7)
      )
  =
  push_frame();
  let input = B.create (IT.size 8) (u64.zeros_) in
  B.upd input (IT.size 0) st0;
  B.upd input (IT.size 1) st1;
  B.upd input (IT.size 2) st2;
  B.upd input (IT.size 3) st3;
  B.upd input (IT.size 4) st4;
  B.upd input (IT.size 5) st5;
  B.upd input (IT.size 6) st6;
  B.upd input (IT.size 7) st7;
  let output = B.create (IT.size circ_size) (u64.zeros_) in
  S.circuit_lowstar circ u64 input output;
  let o0 = B.index output (IT.size (circ_outputs 0)) in
  let o1 = B.index output (IT.size (circ_outputs 1)) in
  let o2 = B.index output (IT.size (circ_outputs 2)) in
  let o3 = B.index output (IT.size (circ_outputs 3)) in
  let o4 = B.index output (IT.size (circ_outputs 4)) in
  let o5 = B.index output (IT.size (circ_outputs 5)) in
  let o6 = B.index output (IT.size (circ_outputs 6)) in
  let o7 = B.index output (IT.size (circ_outputs 7)) in
  pop_frame();
  (o0, o1, o2, o3, o4, o5, o6, o7)
#pop-options
