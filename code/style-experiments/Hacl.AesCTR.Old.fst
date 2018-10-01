module Hacl.AesCTR.Old

let aes128_ctr_encrypt out inp in_len k n c = 
  Hacl.Impl.Aes.BitSlice.Old.aes128_encrypt out inp in_len k n c

let aes128_ctr_decrypt out inp in_len k n c = 
  Hacl.Impl.Aes.BitSlice.Old.aes128_decrypt out inp in_len k n c
