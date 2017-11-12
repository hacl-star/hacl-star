module Spec.HMAC

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

module Hash = Spec.Hash

val wrap_key: (a:Hash.algorithm) -> (len:size_t{len < Hash.max_input a}) -> (key:lbytes len) -> Tot (okey:lbytes (Hash.size_block a))

val init: (a:Hash.algorithm) -> (len:size_t{len < Hash.max_input a}) -> (key:lbytes len) -> Tot (tuple2 (Hash.hash_w a) (lbytes (Hash.size_block a)))

val init': (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> Tot (tuple2 (Hash.hash_w a) (lbytes (Hash.size_block a)))

val update_block: (a:Hash.algorithm) -> (data:lbytes (Hash.size_block a)) -> (hash:Hash.hash_w a) -> Tot (h:Hash.hash_w a)

val update_multi: (a:Hash.algorithm) -> (n:size_t{n * Hash.size_block a <= max_size_t}) -> (data:lbytes (n * Hash.size_block a)) -> (hash:Hash.hash_w a) -> Tot (h:Hash.hash_w a)

val update_last: (a:Hash.algorithm) -> (n:size_t) -> (len:size_t{len < Hash.size_block a /\ len + n * Hash.size_block a <= Hash.max_input a}) -> (last:lbytes len) -> (h:Hash.hash_w a) -> Tot (h:Hash.hash_w a)

val finish: (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> (hash:Hash.hash_w a) -> Tot (h:lbytes (Hash.size_hash a))

val hmac_core': (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> (len:size_t{Hash.size_block a + len < max_size_t /\ Hash.size_block a + len < Hash.max_input a}) -> (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))

val hmac_core: (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> (len:size_t{Hash.size_block a + len < max_size_t /\ Hash.size_block a + len < Hash.max_input a}) -> (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))

val hmac':
  (a:Hash.algorithm) ->
  (klen:size_t{klen < Hash.max_input a}) ->
  (key:lbytes klen) ->
  (len:size_t{Hash.size_block a + len < max_size_t /\ Hash.size_block a + len < Hash.max_input a}) ->
  (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))

val hmac:
  (a:Hash.algorithm) ->
  (klen:size_t{klen < Hash.max_input a}) ->
  (key:lbytes klen) ->
  (len:size_t{Hash.size_block a + len < max_size_t /\ Hash.size_block a + len < Hash.max_input a}) ->
  (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))
