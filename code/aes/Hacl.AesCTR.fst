module Hacl.AesCTR

let aes128_ctr_encrypt out inp in_len k n c = 
  Hacl.Impl.Aes.NI.aes128_encrypt out inp in_len k n c
