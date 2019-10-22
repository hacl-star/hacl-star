module Vale.Arch.HeapImpl
open FStar.Mul

(**
Define abstract (or mostly abstract) types for use by Vale.X64.Decls.fsti.

Note: the untrusted memory definitions are split among 3 modules:
- Vale.Arch.HeapImpl
- Vale.Arch.Heap
- Vale.X64.Memory
This splitting is done to avoid circular module dependencies.
*)

val vale_heap : Type u#1

let vale_heap_impl = vale_heap

