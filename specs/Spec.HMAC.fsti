module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Hash = Spec.Hash

val wrap_key: (a:Hash.algorithm) -> (len:size_nat{len < Hash.max_input a}) -> (key:lbytes len) -> Tot (okey:lbytes (Hash.size_block a))

val init: (a:Hash.algorithm) -> (len:size_nat{len < Hash.max_input a}) -> (key:lbytes len) -> Tot (tuple2 (Hash.state a) (lbytes (Hash.size_block a)))

val init': (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> Tot (tuple2 (Hash.state a) (lbytes (Hash.size_block a)))

val update_block: (a:Hash.algorithm) -> (data:lbytes (Hash.size_block a)) -> (hash:Hash.state a) -> Tot (h:Hash.state a)

val update_multi: (a:Hash.algorithm) -> (n:size_nat{n * Hash.size_block a <= max_size_t}) -> (data:lbytes (n * Hash.size_block a)) -> (hash:Hash.state a) -> Tot (h:Hash.state a)

val update_last: (a:Hash.algorithm) -> (n:size_nat) -> (len:size_nat{len < Hash.size_block a /\ len + n * Hash.size_block a <= Hash.max_input a}) -> (last:lbytes len) -> (h:Hash.state a) -> Tot (h:Hash.state a)

val finish: (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> (hash:Hash.state a) -> Tot (h:lbytes (Hash.size_hash a))

val hmac_core': (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a}) -> (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))

val hmac_core: (a:Hash.algorithm) -> (key:lbytes (Hash.size_block a)) -> (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a}) -> (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))

val hmac':
  (a:Hash.algorithm) ->
  (klen:size_nat{klen < Hash.max_input a}) ->
  (key:lbytes klen) ->
  (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a}) ->
  (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))

val hmac:
  (a:Hash.algorithm) ->
  (klen:size_nat{klen < Hash.max_input a}) ->
  (key:lbytes klen) ->
  (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a}) ->
  (data:lbytes len) -> Tot (h:lbytes (Hash.size_hash a))
