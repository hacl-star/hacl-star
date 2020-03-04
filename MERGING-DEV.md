The following experimental, deprecated, and alternative folders in `dev` are not tracked in `master`:

- code/code-with-previous-libraries
- code/curve25519/experimental
- code/experimental
- code/poly1305/experimental
- lib/experimental
- specs/alternative
- specs/deprecated
- specs/experimental
- specs/tests/experimental

The following changes are only in `dev` and will need to be ported explicitly (they won't appear in a merge):

- specs/Spec.Curve25519.fst adds `decodeScalar`
  used by spec/Spec.Agile.DH.fst
- specs/Spec.Agile.AEAD.fsti adds extra definitions
  used by Spec.Agile.HPKE.fst

(To check out a specific file or folder from a branch, use e.g.
 `git checkout origin/dev -- path/to/file`.)

Soon `dist` will be refreshed in `dev` and `master` as part of CI in the same way as hints. In the meantime, rather than merging it manually, it's easier to rebuild `dist` after merging the rest of the files. If in a hurry, use `git checkout --ours dist` to ignore all changes in `dist` and continue the merge.

The following files in `dev` are untracked in `master` and will need to be ported explicitly (they won't appear in a merge unless they change in between):

- CONVENTIONS.md
- code/Dockerfile
- code/Makefile.snapshot
- code/blake2/
- code/curve25519/Hacl_Vale_Curve25519.c
- code/curve25519/boringssl-test.c
- code/curve25519/curve51-test.c
- code/curve25519/curve64-rfc-test.c
- code/curve25519/curve64-test.c
- code/curve25519/rfc7748_25519.h
- code/curve25519/rfc7748_src/
- code/curve25519/vale-inline.h
- code/curve25519/vale/
- code/curve25519/vale_25519.h
- code/ed25519/ed25519-hacl/
- code/hpke/
- code/nacl-box/test-box.c
- code/snapshot/
- code/utils/
- lib/Lib.ByteSequence.Tuples.fsti
- lib/Lib.ByteSequence.Tuples.fst
- lib/Lib.FixedSequence.fst
- lib/Lib.IntVector.Random.fsti
- lib/Lib.NatMod.fst
- lib/Lib.NatMod.fsti
- lib/Lib.Network.fst
- lib/Lib.Network.fsti
- lib/Lib.NumericVector.fst
- lib/Lib.RandomBuffer.Hardware.fst
- lib/Lib.RandomBuffer.Hardware.fsti
- lib/Lib.Result.fst
- lib/Lib.StringSequence.fst
- lib/c/Lib_PrintBuffer.h
- lib/c/Lib_RandomBuffer_System.h
- lib/c/cpuid/
- lib/c/random/
- lib/ml/
- lib/tutorial/
- snapshots/
- specs/Makefile.OCaml
- specs/Makefile.test
- specs/Spec.AES128_CBC.fst
- specs/Spec.AES256.fst
- specs/Spec.AES256_CBC.fst
- specs/Spec.AES_GCM.fst
- specs/Spec.Agile.DH.fst
- specs/Spec.Agile.HPKE.fst
- specs/Spec.Agile.HPKE.fsti
- specs/Spec.Argon2i.fst
- specs/Spec.Blake2.fst
- specs/Spec.Curve448.fst
- specs/Spec.GF128.fst
- specs/Spec.Gimli.fst
- specs/Spec.Kyber.fst
- specs/Spec.RSAPSS.fst
- specs/Spec.SHA2.Fixed.fst
- specs/lemmas/Spec.Chacha20.Lemmas.fst
- specs/lemmas/Spec.Curve448.Lemmas.fst
- specs/lemmas/Spec.P256.Lemmas.fst
- specs/lemmas/Spec.Poly1305.Lemmas.fst
- specs/tests/Spec.AES256.Test.fst
- specs/tests/Spec.AES256_CBC.Test.fst
- specs/tests/Spec.AES_GCM.Test.fst
- specs/tests/Spec.Argon2i.Test.fst
- specs/tests/Spec.Blake2.Test.fst
- specs/tests/Spec.Curve448.Test.fst
- specs/tests/Spec.GF128.Test.fst
- specs/tests/Spec.RSAPSS.Test.fst
- specs/tests/Spec.SPARKLE.Test.fst
- tests/gf128-ni-test.c 
- tests/gf128-precomp-test.c
