module Views_s

open Words_s

let nat8s_to_nat64 (v1 v2 v3 v4 v5 v6 v7 v8:nat8) : nat64 =
    v1 +
    v2 `op_Multiply` 0x100 +
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000 +
    v5 `op_Multiply` 0x100000000 +
    v6 `op_Multiply` 0x10000000000 +
    v7 `op_Multiply` 0x1000000000000 +
    v8 `op_Multiply` 0x100000000000000

let nat8s_to_nat32 (v1 v2 v3 v4:nat8) : nat32 =
    v1 +
    v2 `op_Multiply` 0x100 +
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000
