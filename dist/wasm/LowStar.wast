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
  (global $3 i32 (i32.const 122))
  (export "data_size" (global 3))
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
    "\70\70\6f\72\74\2e\66\73\74\00"
  )
)
