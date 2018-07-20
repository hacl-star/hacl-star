open Bytes
open Nocrypto

val aes_gcm_encrypt: key:bytes -> iv:bytes -> ad:bytes -> input:bytes -> output:bytes
let aes_gcm_encrypt key iv ad input = AES.GCM.encrypt key iv ad input

val aes_gcm_decrypt: key:bytes -> iv:bytes -> ad:bytes -> input:bytes -> output:bytes
let aes_gcm_decrypt key iv ad input = AES.GCM.decrypt key iv ad input
