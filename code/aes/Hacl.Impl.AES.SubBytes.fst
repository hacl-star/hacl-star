module Hacl.Impl.AES.SubBytes

open FStar.HyperStack.ST
open FStar.HyperStack

module IT = Lib.IntTypes
module B = Lib.Buffer
module S = Lib.Sliceable

inline_for_extraction noextract
private let circ : S.circuit 8 137 =
fun i -> match i with
|   0 -> S.Input   7   |   1 -> S.Input   6   |   2 -> S.Input   5   |   3 -> S.Input   4
|   4 -> S.Input   3   |   5 -> S.Input   2   |   6 -> S.Input   1   |   7 -> S.Input   0
|   8 -> S.Xor   6   4 |   9 -> S.Xor   3   0 |  10 -> S.Xor   1   2 |  11 -> S.Xor   7  10
|  12 -> S.Xor   8   9 |  13 -> S.Xor   1   5 |  14 -> S.Xor   0   6 |  15 -> S.Xor   8  13
|  16 -> S.Xor   6  11 |  17 -> S.Xor   3  11 |  18 -> S.Xor   7  12 |  19 -> S.Xor  12  13
|  20 -> S.Xor   2   5 |  21 -> S.Xor  10  12 |  22 -> S.Xor   5  14 |  23 -> S.Xor   0   5
|  24 -> S.Xor   7  15 |  25 -> S.Xor   6   5 |  26 -> S.Xor   9  25 |  27 -> S.Xor  11  22
|  28 -> S.Xor   8  20 |  29 -> S.Xor   0  11 |  30 -> S.Xor  28  12 |  31 -> S.Xor  28  14
|  32 -> S.Xor  14  26 |  33 -> S.Xor  23  21 |  34 -> S.Xor  29  24 |  35 -> S.And  26  12
|  36 -> S.And  27  18 |  37 -> S.Xor  19  35 |  38 -> S.And  17   7 |  39 -> S.Xor  38  35
|  40 -> S.And  14  28 |  41 -> S.And  16  11 |  42 -> S.Xor  31  40 |  43 -> S.And  29  24
|  44 -> S.Xor  43  40 |  45 -> S.And   9  15 |  46 -> S.And  32  30 |  47 -> S.Xor  46  45
|  48 -> S.And  23  21 |  49 -> S.Xor  48  45 |  50 -> S.Xor  37  36 |  51 -> S.Xor  39  33
|  52 -> S.Xor  42  41 |  53 -> S.Xor  44  49 |  54 -> S.Xor  50  47 |  55 -> S.Xor  51  49
|  56 -> S.Xor  52  47 |  57 -> S.Xor  53  34 |  58 -> S.Xor  56  57 |  59 -> S.And  56  54
|  60 -> S.Xor  55  59 |  61 -> S.Xor  54  55 |  62 -> S.Xor  57  59 |  63 -> S.And  62  61
|  64 -> S.And  60  58 |  65 -> S.And  54  57 |  66 -> S.And  61  65 |  67 -> S.Xor  61  59
|  68 -> S.And  55  56 |  69 -> S.And  58  68 |  70 -> S.Xor  58  59 |  71 -> S.Xor  55  63
|  72 -> S.Xor  66  67 |  73 -> S.Xor  57  64 |  74 -> S.Xor  69  70 |  75 -> S.Xor  72  74
|  76 -> S.Xor  71  73 |  77 -> S.Xor  71  72 |  78 -> S.Xor  73  74 |  79 -> S.Xor  76  75
|  80 -> S.And  78  12 |  81 -> S.And  74  18 |  82 -> S.And  73   7 |  83 -> S.And  77  28
|  84 -> S.And  72  11 |  85 -> S.And  71  24 |  86 -> S.And  76  15 |  87 -> S.And  79  30
|  88 -> S.And  75  21 |  89 -> S.And  78  26 |  90 -> S.And  74  27 |  91 -> S.And  73  17
|  92 -> S.And  77  14 |  93 -> S.And  72  16 |  94 -> S.And  71  29 |  95 -> S.And  76   9
|  96 -> S.And  79  32 |  97 -> S.And  75  23 |  98 -> S.Xor  95  96 |  99 -> S.Xor  84  90
| 100 -> S.Xor  87  98 | 101 -> S.Xor  89  99 | 102 -> S.Xor  82  92 | 103 -> S.Xor  80  83
| 104 -> S.Xor  98 103 | 105 -> S.Xor  81 101 | 106 -> S.Xor  80  86 | 107 -> S.Xor  85  93
| 108 -> S.Xor  88  94 | 109 -> S.Xor  82 105 | 110 -> S.Xor 102 108 | 111 -> S.Xor  91  99
| 112 -> S.Xor  83  86 | 113 -> S.Xor 101 112 | 114 -> S.Xor  97 110 | 115 -> S.Xor  95 106
| 116 -> S.Xor 102 107 | 117 -> S.Xor  85  98 | 118 -> S.Xor  84  92 | 119 -> S.Xor 103 111
| 120 -> S.Xor  88 107 | 121 -> S.Xor 118 120 | 122 -> S.Xor  84 106 | 123 -> S.Xor 110 119
| 124 -> S.Xor 105 122 | 125 -> S.Xor 104 116 | 126 -> S.Not 125     | 127 -> S.Xor 100 121
| 128 -> S.Not 127     | 129 -> S.Xor 100 123 | 130 -> S.Xor 109 117 | 131 -> S.Xor 104 105
| 132 -> S.Xor 114 115 | 133 -> S.Not 132     | 134 -> S.Xor 100 124 | 135 -> S.Not 134
| 136 -> S.Xor 100 113

inline_for_extraction noextract
private let u64 = S.uN IT.U64 IT.SEC

#push-options "--z3rlimit 50"
let sub_bytes64x8
  (st0:u64.t) (st1:u64.t) (st2:u64.t) (st3:u64.t)
  (st4:u64.t) (st5:u64.t) (st6:u64.t) (st7:u64.t) :
    Stack
      (u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t)
      (fun _ -> True)
      (fun h0 _ h1 -> B.modifies LowStar.Monotonic.Buffer.loc_none h0 h1)
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
  let output = B.create (IT.size 137) (u64.zeros_) in
  S.circuit_lowstar circ u64 input output;
  let o0 = B.index output (IT.size 129) in
  let o1 = B.index output (IT.size 130) in
  let o2 = B.index output (IT.size 131) in
  let o3 = B.index output (IT.size 132) in
  let o4 = B.index output (IT.size 133) in
  let o5 = B.index output (IT.size 134) in
  let o6 = B.index output (IT.size 135) in
  let o7 = B.index output (IT.size 136) in
  pop_frame();
  (o0, o1, o2, o3, o4, o5, o6, o7)
#pop-options
