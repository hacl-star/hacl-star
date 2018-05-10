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

- the SHA2_256 and SHA2_384 files have some unbound variables in them and do not
  extract
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
