### Example 3 - functional correctness

In F* buffers are encoded as a reference to a sequence of data, coupled with a *start index* that allows us to emulated some pointer arithmetic.

It also means that in this model, all the computations that happen on buffers have a specification in terms of what happens to the underlying sequence of values.

To access the underlying sequence of buffer `b` in the memory `h`, the F* library provides us with a *ghost* function which returns that sequence. `Ghost` is another F* effect, that is incompatible with computationally relevant effect. The F* type system enforces that *ghost* code cannot be mixed with *concrete* code, and the *ghost* code is always erased at extaction.

Thus, when computing on a buffer `b`, it is possible to give a *pure* specification in terms of what happens to the underlying value:
```F#
let spec (s:seq t) : Tot (seq t) = ...
val f: b:buffer t -> Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ (as_seq h1 b) == spec (as_seq h0 b)))
```

To prove the correctness of the `fsum` function we proceed the same way.

First we define what are the element of the Z/pZ field (as mathematical integers that are greater than or equal to 0 and less than the prime), as well as the additive law (a modular addition).

Then we define `seqelem`, the type of the sequence of 5 uint64 corresponding to the value of the bignums in a certain heap.
On this type, we define a mapping function, which associates a field element to a `seqelem`. Although the definition of the `seval_` function is recursive, for convenience for proofs, the unrolled value of 
`to_field s` is (s[0] + 2^51*s[1] + 2^51*s[2] + 2^51*s[3] + 2^51*s[4]) % (2^255-19), which is a natural mapping for the representation detailed in [example 2](https://github.com/mitls/hacl-star/tree/master/doc/tutorial/2).

Then we implement the equivalent of the `fsum_` function on sequence: `fsum_spec` and we show that indeed, `fsum_spec` is the pure specification of the `fsum` stateful computation between the memory state `h0` and `h1`.

Eventually we show that `fsum_spec` properly implements the field's addition via a extrinsic lemma:
```F#
val lemma_fsum_field: s:seqelem -> s':seqelem{fsum_spec_pre s s' len} ->
  Lemma (to_field (fsum_spec s s' len) = to_field s @+ to_field s')
```
which we can use in a `fsum`, a wrapper around `fsum_`.
Note that the `inline_for_extraction` keyword implies that when extracting the code, F* will inline the `fsum` body, so adding such a wrapper has no performance cost.
