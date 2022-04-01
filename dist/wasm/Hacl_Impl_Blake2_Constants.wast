(module
  (type $0 (func))
  (type $1 (func (param i32) (result i32)))
  (type $2 (func (param i32) (result i32)))
  (type $3 (func (param i32) (result i32)))
  (type $4 (func (param i32) (result i32)))
  (type $5 (func (param i32) (result i32)))
  (type $6 (func (param i64) (result i64)))
  (type $7 (func (param i32 i32 i32) (result i32)))
  (type $8 (func (param i32 i32 i32 i32) (result i32)))
  (type $9 (func (param i32 i32 i32 i32) (result i32)))
  (type $10 (func (param i64 i64 i64 i32) (result i64)))
  (type $11 (func (param i64 i64 i64 i32) (result i64)))
  (type $12 (func (param i32) (result i32)))
  (type $13 (func (param i32) (result i32)))
  (type $14 (func (param i32) (result i32)))
  (type $15 (func (param i32) (result i32)))
  (type $16 (func))
  (import "Kremlin" "mem" (memory $0 16))
  (import "Kremlin" "data_start" (global $0 i32))
  (import "Kremlin" "debug" (func $0 (type 0)))
  (import "WasmSupport" "WasmSupport_trap" (func $1 (type 1)))
  (import "WasmSupport" "WasmSupport_malloc" (func $2 (type 2)))
  (import "WasmSupport" "WasmSupport_align_64" (func $3 (type 3)))
  (import "WasmSupport" "WasmSupport_check_buffer_size" (func $4 (type 4)))
  (import "WasmSupport" "WasmSupport_betole32" (func $5 (type 5)))
  (import "WasmSupport" "WasmSupport_betole64" (func $6 (type 6)))
  (import "WasmSupport" "WasmSupport_memzero" (func $7 (type 7)))
  (import
    "Hacl_IntTypes_Intrinsics"
    "Hacl_IntTypes_Intrinsics_add_carry_u32"
    (func $8 (type 8))
  )
  (import
    "Hacl_IntTypes_Intrinsics"
    "Hacl_IntTypes_Intrinsics_sub_borrow_u32"
    (func $9 (type 9))
  )
  (import
    "Hacl_IntTypes_Intrinsics"
    "Hacl_IntTypes_Intrinsics_add_carry_u64"
    (func $10 (type 10))
  )
  (import
    "Hacl_IntTypes_Intrinsics"
    "Hacl_IntTypes_Intrinsics_sub_borrow_u64"
    (func $11 (type 11))
  )
  (import "FStar" "FStar_UInt128_u32_64" (global $1 i32))
  (import "FStar" "FStar_UInt128_u32_32" (global $2 i32))
  (import "LowStar" "LowStar_Monotonic_Buffer_is_null" (func $12 (type 12)))
  (global $3 (mut i32) (i32.const 0))
  (global $4 (mut i32) (i32.const 0))
  (global $5 (mut i32) (i32.const 0))
  (global $6 i32 (i32.const 861))
  (func $13
    (type 13)
    (local i64 i64 i32 i32)
    (i32.const 0)
    (i32.load align=1)
    (global.get 3)
    (local.set 3)
    (local.set 4)
    (local.get 3)
    (local.get 4)
    (i32.const 0)
    (local.set 3)
    (local.set 4)
    (local.get 3)
    (local.get 4)
    (i32.store align=1)
  )
  (func $14
    (type 14)
    (local i64 i64 i32 i32)
    (i32.const 0)
    (i32.load align=1)
    (global.get 4)
    (local.set 3)
    (local.set 4)
    (local.get 3)
    (local.get 4)
    (i32.const 0)
    (local.set 3)
    (local.set 4)
    (local.get 3)
    (local.get 4)
    (i32.store align=1)
  )
  (func $15
    (type 15)
    (local i64 i64 i32 i32)
    (i32.const 0)
    (i32.load align=1)
    (global.get 5)
    (local.set 3)
    (local.set 4)
    (local.get 3)
    (local.get 4)
    (i32.const 0)
    (local.set 3)
    (local.set 4)
    (local.get 3)
    (local.get 4)
    (i32.store align=1)
  )
  (func $16
    (type 16)
    (global.get 0)
    (i32.const 122)
    (i32.add)
    (global.set 3)
    (global.get 0)
    (i32.const 763)
    (i32.add)
    (global.set 4)
    (global.get 0)
    (i32.const 796)
    (i32.add)
    (global.set 5)
  )
  (export "Hacl_Impl_Blake2_Constants___get_sigmaTable" (func 13))
  (export "Hacl_Impl_Blake2_Constants___get_ivTable_S" (func 14))
  (export "Hacl_Impl_Blake2_Constants___get_ivTable_B" (func 15))
  (export "data_size" (global 6))
  (start 16)
  (data
    0
    (offset (global.get 0))
    "\5a\65\72\6f\2d\73\69\7a\65\64\20\61\72\72\61\79"
    "\73\20\61\72\65\20\6e\6f\74\20\73\75\70\70\6f\72"
    "\74\65\64\20\69\6e\20\43\20\61\6e\64\20\69\6e\20"
    "\57\41\53\4d\20\65\69\74\68\65\72\2e\20\53\65\65"
    "\20\57\61\73\6d\53\75\70\70\6f\72\74\2e\66\73\74"
    "\00\4f\76\65\72\66\6c\6f\77\20\69\6e\20\6d\65\6d"
    "\7a\65\72\6f\3b\20\73\65\65\20\57\61\73\6d\53\75"
    "\70\70\6f\72\74\2e\66\73\74\00\00\00\00\00\01\00"
    "\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00"
    "\00\00\06\00\00\00\07\00\00\00\08\00\00\00\09\00"
    "\00\00\0a\00\00\00\0b\00\00\00\0c\00\00\00\0d\00"
    "\00\00\0e\00\00\00\0f\00\00\00\0e\00\00\00\0a\00"
    "\00\00\04\00\00\00\08\00\00\00\09\00\00\00\0f\00"
    "\00\00\0d\00\00\00\06\00\00\00\01\00\00\00\0c\00"
    "\00\00\00\00\00\00\02\00\00\00\0b\00\00\00\07\00"
    "\00\00\05\00\00\00\03\00\00\00\0b\00\00\00\08\00"
    "\00\00\0c\00\00\00\00\00\00\00\05\00\00\00\02\00"
    "\00\00\0f\00\00\00\0d\00\00\00\0a\00\00\00\0e\00"
    "\00\00\03\00\00\00\06\00\00\00\07\00\00\00\01\00"
    "\00\00\09\00\00\00\04\00\00\00\07\00\00\00\09\00"
    "\00\00\03\00\00\00\01\00\00\00\0d\00\00\00\0c\00"
    "\00\00\0b\00\00\00\0e\00\00\00\02\00\00\00\06\00"
    "\00\00\05\00\00\00\0a\00\00\00\04\00\00\00\00\00"
    "\00\00\0f\00\00\00\08\00\00\00\09\00\00\00\00\00"
    "\00\00\05\00\00\00\07\00\00\00\02\00\00\00\04\00"
    "\00\00\0a\00\00\00\0f\00\00\00\0e\00\00\00\01\00"
    "\00\00\0b\00\00\00\0c\00\00\00\06\00\00\00\08\00"
    "\00\00\03\00\00\00\0d\00\00\00\02\00\00\00\0c\00"
    "\00\00\06\00\00\00\0a\00\00\00\00\00\00\00\0b\00"
    "\00\00\08\00\00\00\03\00\00\00\04\00\00\00\0d\00"
    "\00\00\07\00\00\00\05\00\00\00\0f\00\00\00\0e\00"
    "\00\00\01\00\00\00\09\00\00\00\0c\00\00\00\05\00"
    "\00\00\01\00\00\00\0f\00\00\00\0e\00\00\00\0d\00"
    "\00\00\04\00\00\00\0a\00\00\00\00\00\00\00\07\00"
    "\00\00\06\00\00\00\03\00\00\00\09\00\00\00\02\00"
    "\00\00\08\00\00\00\0b\00\00\00\0d\00\00\00\0b\00"
    "\00\00\07\00\00\00\0e\00\00\00\0c\00\00\00\01\00"
    "\00\00\03\00\00\00\09\00\00\00\05\00\00\00\00\00"
    "\00\00\0f\00\00\00\04\00\00\00\08\00\00\00\06\00"
    "\00\00\02\00\00\00\0a\00\00\00\06\00\00\00\0f\00"
    "\00\00\0e\00\00\00\09\00\00\00\0b\00\00\00\03\00"
    "\00\00\00\00\00\00\08\00\00\00\0c\00\00\00\02\00"
    "\00\00\0d\00\00\00\07\00\00\00\01\00\00\00\04\00"
    "\00\00\0a\00\00\00\05\00\00\00\0a\00\00\00\02\00"
    "\00\00\08\00\00\00\04\00\00\00\07\00\00\00\06\00"
    "\00\00\01\00\00\00\05\00\00\00\0f\00\00\00\0b\00"
    "\00\00\09\00\00\00\0e\00\00\00\03\00\00\00\0c\00"
    "\00\00\0d\00\00\00\00\00\00\00\00\67\e6\09\6a\85"
    "\ae\67\bb\72\f3\6e\3c\3a\f5\4f\a5\7f\52\0e\51\8c"
    "\68\05\9b\ab\d9\83\1f\19\cd\e0\5b\00\08\c9\bc\f3"
    "\67\e6\09\6a\3b\a7\ca\84\85\ae\67\bb\2b\f8\94\fe"
    "\72\f3\6e\3c\f1\36\1d\5f\3a\f5\4f\a5\d1\82\e6\ad"
    "\7f\52\0e\51\1f\6c\3e\2b\8c\68\05\9b\6b\bd\41\fb"
    "\ab\d9\83\1f\79\21\7e\13\19\cd\e0\5b\00"
  )
)
