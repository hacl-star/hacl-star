module Hacl.Circuit

open Lib.Sliceable
open FStar.HyperStack.ST
open FStar.HyperStack

module IT = Lib.IntTypes
module B = Lib.Buffer

inline_for_extraction noextract
let circ : circuit 8 137 =
fun i -> match i with
|   0 -> Input   7 |   1 -> Input   6 |   2 -> Input   5 |   3 -> Input   4
|   4 -> Input   3 |   5 -> Input   2 |   6 -> Input   1 |   7 -> Input   0
|   8 -> Xor   6   4 |   9 -> Xor   3   0 |  10 -> Xor   1   2 |  11 -> Xor   7  10
|  12 -> Xor   8   9 |  13 -> Xor   1   5 |  14 -> Xor   0   6 |  15 -> Xor   8  13
|  16 -> Xor   6  11 |  17 -> Xor   3  11 |  18 -> Xor   7  12 |  19 -> Xor  12  13
|  20 -> Xor   2   5 |  21 -> Xor  10  12 |  22 -> Xor   5  14 |  23 -> Xor   0   5
|  24 -> Xor   7  15 |  25 -> Xor   6   5 |  26 -> Xor   9  25 |  27 -> Xor  11  22
|  28 -> Xor   8  20 |  29 -> Xor   0  11 |  30 -> Xor  28  12 |  31 -> Xor  28  14
|  32 -> Xor  14  26 |  33 -> Xor  23  21 |  34 -> Xor  29  24 |  35 -> And  26  12
|  36 -> And  27  18 |  37 -> Xor  19  35 |  38 -> And  17   7 |  39 -> Xor  38  35
|  40 -> And  14  28 |  41 -> And  16  11 |  42 -> Xor  31  40 |  43 -> And  29  24
|  44 -> Xor  43  40 |  45 -> And   9  15 |  46 -> And  32  30 |  47 -> Xor  46  45
|  48 -> And  23  21 |  49 -> Xor  48  45 |  50 -> Xor  37  36 |  51 -> Xor  39  33
|  52 -> Xor  42  41 |  53 -> Xor  44  49 |  54 -> Xor  50  47 |  55 -> Xor  51  49
|  56 -> Xor  52  47 |  57 -> Xor  53  34 |  58 -> Xor  56  57 |  59 -> And  56  54
|  60 -> Xor  55  59 |  61 -> Xor  54  55 |  62 -> Xor  57  59 |  63 -> And  62  61
|  64 -> And  60  58 |  65 -> And  54  57 |  66 -> And  61  65 |  67 -> Xor  61  59
|  68 -> And  55  56 |  69 -> And  58  68 |  70 -> Xor  58  59 |  71 -> Xor  55  63
|  72 -> Xor  66  67 |  73 -> Xor  57  64 |  74 -> Xor  69  70 |  75 -> Xor  72  74
|  76 -> Xor  71  73 |  77 -> Xor  71  72 |  78 -> Xor  73  74 |  79 -> Xor  76  75
|  80 -> And  78  12 |  81 -> And  74  18 |  82 -> And  73   7 |  83 -> And  77  28
|  84 -> And  72  11 |  85 -> And  71  24 |  86 -> And  76  15 |  87 -> And  79  30
|  88 -> And  75  21 |  89 -> And  78  26 |  90 -> And  74  27 |  91 -> And  73  17
|  92 -> And  77  14 |  93 -> And  72  16 |  94 -> And  71  29 |  95 -> And  76   9
|  96 -> And  79  32 |  97 -> And  75  23 |  98 -> Xor  95  96 |  99 -> Xor  84  90
| 100 -> Xor  87  98 | 101 -> Xor  89  99 | 102 -> Xor  82  92 | 103 -> Xor  80  83
| 104 -> Xor  98 103 | 105 -> Xor  81 101 | 106 -> Xor  80  86 | 107 -> Xor  85  93
| 108 -> Xor  88  94 | 109 -> Xor  82 105 | 110 -> Xor 102 108 | 111 -> Xor  91  99
| 112 -> Xor  83  86 | 113 -> Xor 101 112 | 114 -> Xor  97 110 | 115 -> Xor  95 106
| 116 -> Xor 102 107 | 117 -> Xor  85  98 | 118 -> Xor  84  92 | 119 -> Xor 103 111
| 120 -> Xor  88 107 | 121 -> Xor 118 120 | 122 -> Xor  84 106 | 123 -> Xor 110 119
| 124 -> Xor 105 122 | 125 -> Xor 104 116 | 126 -> Not 125     | 127 -> Xor 100 121
| 128 -> Not 127     | 129 -> Xor 100 123 | 130 -> Xor 109 117 | 131 -> Xor 104 105
| 132 -> Xor 114 115 | 133 -> Not 132     | 134 -> Xor 100 124 | 135 -> Not 134
| 136 -> Xor 100 113

inline_for_extraction noextract
let u64 = uN IT.U64 IT.SEC

#push-options "--z3rlimit 20"
let sub_bytes64x8
  (st0:u64.t) (st1:u64.t) (st2:u64.t) (st3:u64.t)
  (st4:u64.t) (st5:u64.t) (st6:u64.t) (st7:u64.t) :
    Stack
      (u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t)
      (fun _ -> True)
      (fun _ _ _ -> True)
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
  circuit_lowstar circ u64 input output;
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
