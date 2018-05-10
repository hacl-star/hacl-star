# evercrypt

This cryptographic library caters to the needs of Project Everest. Building
blocks:
- `Hacl.fsti`, an F\* interface that states what `evercrypt` expects of HACL\*
  in terms of algorithm signatures and their specifications -- HACL\* will
  implement this interface in F\*, via `Hacl.fst`
- `Vale.fsti`, same thing for Vale, also to be implemented in F\* via a
  `Vale.fst` file
- `OpenSSL.fsti`, which captures the assumptions we make about OpenSSL's
  algorithms

On top of these three building blocks, we have:
- `EverCrypt.fsti`, a *multiplexing* provider that is configurable to call into
  any of the three providers above.

# status of the provider

- specs: the alloc function is marked as StackInline and therefore cannot cross
  interface boundaries; meaning that for now, we have to reveal to the client
  what the `state` type is for each SHA algorithm
- furthermore, this means that vale has to adopt the same state type as HACL*
- in the future, we may request that the client allocates a number of bytes
  (`UInt8.t`) and then do an unsafe cast via a C function into whichever state
  type each provider chooses to use, meaning that Hacl could expose an abstract
  state type
- KB suggests we put *only* the pure functional specs in EverCrypt.Specs and
  leave the memory safety specs to each algorithm, since they may adopt
  different strategies for init/update/finish incremental APIs

# status of primitives

 primitive | hacl | vale | openssl | c/bytes | ml/bytes 
-----------|------|------|---------|---------|---------
 sha256    | yes  | yes  | no      | no      | no
 sha384    | yes  | no   | no      | no      | no
 sha512    | yes  | no   | no      | no      | no
 curve     | yes  | no   | no      | yes     | yes
 aes256gcm | no   | no   | yes     | no      | no

How to add a primitive:
- EverCrypt.Specs.fsti, to be extended with suitable pre- and post-conditions
- EverCrypt.Native.fsti, to add a global variable to control the implementation
  choice
- evercrypt_native.c, to provide a suitable default implementation
- EverCrypt.fsti, to add the primitive
- EverCrypt.(OpenSSL|Vale|Hacl).fsti, to add the primitive in the specific
  provider
- EverCrypt.fst, to multiplex into the provider above
- if Hacl: edit EverCrypt.Hacl.fst, to implement the corresponding function by
  poking into code/<your-algorithm>/interfaces/<your-interface.fsti>
- if OpenSSL or Vale: edit evercrypt_(openssl|vale).c
- if new primitive: edit the Makefile and add the source to HACL_SOURCES or
  VALE_SOURCES or VALE_ASM
- if this primitive is to be called from miTLS
  - edit EverCrypt.Bytes.fst to expose a Pure function that returns bytes
  - edit evercrypt_bytes.c to implement this function in C
  - edit EverCrypt_bytes.ml to implement this function in ML using ctypes
- add a test for your primitive in sample-project/
