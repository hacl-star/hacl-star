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
