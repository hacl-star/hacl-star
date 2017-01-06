## Example 1 - Memory safety

This example is almost identical to [example 0](https://github.com/mitls/hacl-star/tree/master/doc/tutorial/0).

The function's post condition however is different. The function of *example 0* was actually not really usable, while this one is. Here is why.

### The memory model

F* has customizable effects. `Stack` is one of those. It means that the computation implicitely carries the program memory, on which some changes can be performed.

The memory model lying under the `Stack` effect is called *HyperStack*. Without getting too deep into the details of the model, consider that *HyperStack* is a tree of *regions*.
These *regions* are organized into 3 different disjoint categories:
- a "stack": a branch of the tree on which a *stack* structure is enforced. This stack mimics the C framing discipline.
- a "memory managed heap": the programmer is responsible for allocating/freeing all objects in those regions, like in C.
- a "eternal heap": anything that has been allocated in those regions cannot be freed. This is convenient for proofs (any reference can always be dereferenced since the only was to get a reference from the memory is to allocate something, and such reference can never be freed). However this is responsible for memory leaks, and is not use in our code.

In this setting the `Stack` effect is quite constrained. It carries an invariant that specifies that the memory layout before and after the function call is identical. This means that:
- the set of regions is identical before and after
- the set of references of each regions is identical before and after.

Hence when in the `Stack` effect, nothing can be allocated on the heap, and thus the only way to allocate a fresh value is to first push a fresh frame on top of stack, allocate in it, and then free it.
Note that in our setting integers are implicitely allocated, only buffers are explicitely go through concrete allocation.

### The memory safety conditions

Buffer `a` and buffer `b` must have been allocated for them to be usable in the `fsum` function.
More precisely, they must be statically proven `live` to access their content. That is the meaning of the `requires (fun h -> live h a /\ live h b)` precondition.
Both `a` and `b` exist in memory, and they point to 5 consecutive values (as enforced by their type).

Those conditions are necessary to access their content. `<buffer>.(x)` is syntactic sugar for `FStar.Buffer.index buffer x` where that function's declaration is the following:
```F#
val index: #a:Type -> b:buffer a -> n:UInt32.t{v n < length b} -> Stack a
  (requires (fun h -> live h b))
  (ensures (fun h0 z h1 -> live h0 b /\ h1 == h0
    /\ z == Seq.index (as_seq h0 b) (v n)))
```

If trying to access an element at an index greater than or equal to the length of the buffer, that function would fail to typecheck.

### `let` definitions in stateful monads are opaque

In F* the `let` definition of the stateful computation is opaque: it is only visible to the SMT solver when it typechecks the function. When calling it it only knows about what its post-condition specifies.

Hence, in *example 0* where the post-condition is `true`, the SMT solver knows nothing about what the function did.
This is worse than sounds: although the `Stack` effect enforces a constraint on the memory layout, this is all the solver knows, which means that all the referenced values might have changed. For proofs, that is bad.
This is why we need to provide a `modifies` clause. Such clauses indicate exactly which references have been touched.

Here the buffer `b` has a refinement: `disjoint a b`. This indicates that the two buffers are not overlapping. In combination with the fact that only `a` has been modified (`modifies_1 a h0 h1`), the solver can deduce that the sequence of values `b` points to (`as_seq h b`) is left unchanged by the function.
