A note on rewriting stateful code into higher-order combinators
===============================================================

This document describes the intent, usage and inner workings of the "higher-order
tactic", whose goal is to rewrite agile, stateful code into a series of
higher-order functions. The higher-order functions can then be specialized and
instantiated by clients, in effect providing a loose equivalent of C++ templates
where code is written in a generic manner, then instantiated repeatedly to
obtain specialized implementations.

Exploiting agility for maximal code reuse
-----------------------------------------

In order to illustrate our problem statement, we take an easy, well-understood
algorithm: chacha20. There are several efficient ways to implement chacha20,
depending on the number of *lanes*, i.e. how wide memory instructions can be.

```fstar
type lane = x:nat { x = 1 \/ x = 4 \/ x = 8 }
```

If `lane = 1`, then we will implement chacha20 with 32-bit loads; with `lane =
4`, the implementation will use 128-bit loads and stores, etc.

Rather than write the code three times with only minor differences, we rely on
F\*'s support for *agility* to write code once. First, we define the type of the
state to be parametric (agile) over the *index* lane:

```fstar
let elem (l: lane) =
  match l with
  | 1 -> UInt32.t
  | 4 -> UInt128.t
  | 8 -> UInt256.t

let state (l: lane) =
  buffer (elem l)
```

We then write functions once rather than writing them three times, so as to
exploit the common structure between all variants of the same algorithm. The
entire algorithm can be written this way.

```fstar
// Chacha20_generic.fst (not extracted)
let ( +| ) (#l: lane) (x y: elem l) =
  match l with
  | 1 -> UInt32.add
  | 4 -> UInt128.add
  | 8 -> UInt256.add

let line (#l: lane) (s: state l): St unit = // modifies s
  s.(0ul) <- s.(1ul) +| s.(2ul)
  ... // etc.

let double_round (#l: lane) (s: state l): St unit =
  ...
  // various calls to line
  ...

let rounds (#l: lane) (s: state l): St unit =
  ...
  // various calls to double_round
  ...

// The function that clients will use.
let core (#l: lane) (s: state l): St unit =
  ...
  // various calls to rounds
  ...

```

Here, the key point is that all the functions are agile, i.e. index-parametric.
The operator `+|`, being at the leaves of the call-graph, dispatches to a
suitable operation based on the actual value of `#l`.

We now have a fully lane-generic implementation of chacha20, except that it
cannot compile to idiomatic C. What we wish to do, instead, is specialize this
entire call-graph (at least) three times, for each low-level choice of
representation, so that clients have access to several fully specialized
implementations of the whole chacha20 algorithm.

First attempt: inline all the things
------------------------------------

A first, workable solution, is to mark the entire call-graph with the
`inline_for_extraction` attribute, all the way to the `+|` operator.

The presence of this attribute on a function declaration means that, at
extraction-time, the function will be substituted with its body. Any (pure)
beta-redexes that appear will be evaluated and reduced before emitting code.

Concretely:

```fstar
inline_for_extraction let (+|) ... =
  // same definition

inline_for_extraction let line (#l: lane) (s: state l): St unit =
  s.(0ul) <- s.(1ul) +| s.(2ul)
```

at extraction-time, the definition of `line` becomes:

```fstar
inline_for_extraction let line (#l: lane) (s: state l): St unit =
  s.(0ul) <- (fun #l s -> match l with
    | 1 -> UInt32.add
    | 4 -> UInt128.add
    | 8 -> UInt256.add) #l s.(1ul) s.(2ul)
```

This is not a huge amount of progress, because the code still isn't valid Low\*,
until you realize that is suffices to apply `line` to a concrete argument for `l`
to trigger a complete specialization of this code:

```fstar
let line32 = line #1

// reduces to:

let line32 = fun (s: state 1) ->
  s.(0ul) <- ((fun #l s -> match l with
    | 1 -> UInt32.add
    | 4 -> UInt128.add
    | 8 -> UInt256.add) #1) s.(1ul) s.(2ul)
  //  ^^^^^^^^^^^^^^^^^^^^^
  //  this is a pure beta-redex

// F* can perform pure reduction steps within stateful computations, and reduces
// this to the following (notice that the type has been reduced, too):
let line32 (s: buffer UInt32.t) =
  s.(0ul) <- UInt32.add s.(1ul) s.(2ul)
```

We now have a way of completely specializing our algorithm: we can apply this
technique to the entire call-graph and expose three files:

```fstar
// Chacha20.fst
let core32 = core #1

// Chacha20_Avx.fst
let core128 = core #4

// Chacha20_Avx2.fst
let core256 = core #8
```

Since the `UInt128.add` and `UInt256.add` functions are implemented using AVX
and AVX-2 compiler intrinsics, respectively, we offer three specialized
instances of of chacha20 in separate files; each file will be compiled with
different compiler options (`-mavx` and `-mavx2`, respectively). It will then be
up to the upper EverCrypt layer to perform run-time CPU detection and dispatch
at run-time towards the version that is compatible with the instruction set of
the target CPU the code is running on.

The clean separation of this code into different files is actually crucial: if
the three instances (specializations) of chacha20 were to be placed in the same
file, then the compiler might optimize the 32-bit version with AVX2
instructions, which is precisely what we're trying to avoid.

This solution gives us i) full specialization of the code, and ii) in separate files
but fails to meet two more requirements:
- iii) preserving the shape of the call-graph: this technique destroys the
  structure of the original code, and might generate an arbitrary large function
  body for the `core` function. No one wants to see C code like that.
- iv) modularity: this approach is non-modular, in the sense that if, say, Intel
  adds dedicated Chacha20 support in its next Lakey Lake (tm) generation of
  processors, then we will want to have a `Chacha20_Lakey.fst` where the outer
  code is Avx2-compatible, but where `double_round` is replaced whole-sale with a
  call to a dedicated instruction.

Second attempt: preserving the structure of the call graph
----------------------------------------------------------

Let us now look at a solution that gives us i) and iii). This will be helpful in
working our way up to a solution that satisfies all four requirements above.

If we want to preserve some structure in the call-graph, then we now need to
remove the `inline_for_extraction` attribute from some function definitions.
Still taking inspiration from real-word chacha20, let's say we want to see in
the generated C code at least `double_round` and `core`.

Naïvely removing `inline_from_extraction` from `double_round` means that we will
be able to correctly specialize double_round.

```fstar
// Chacha20.fst
let double_round32 = double_round #1
```

However, attempting to specialize `core` will result in the following:

```fstar
// Chacha20.fst
let core32 = core #1

// ... reduces to ...
let core32 = fun state ->
  ... rounds #1 ...

// ... rounds is inline_for_extraction, so this reduces to ...
let core32 = fun state ->
  ... double_round #1 ...

// reduction is stuck because doule_round is not inline for extraction
```

Essentially, we would like `core32` to call `double_round32`. Or, in an
index-generic fashion: `core` (the generic instance) to call `double_round32`
(if the index is `1`), or `double_round128`, etc.

It turns out, we can rewrite our definition of `rounds` to do just
that.

```fstar
// Chacha20_generic2.fst
inline_for_extraction
let ( +| ) (#l: lane) (x y: elem l) =
  ...

inline_for_extraction
let line (#l: lane) (s: state l): St unit =
  ...

inline_for_extraction
let double_round (#l: lane) (s: state l): St unit =
  ...
  // various calls to line
  ...

// these three NOT inline_for_extraction!
let double_round32 = double_round #1
let double_round128 = double_round #4
let double_round256 = double_round #8

inline_for_extraction
let rounds (#l: lane) (s: state l): St unit =
  // previously: double_round #l s
  ... (match l with
    | 1 -> double_round32
    | 4 -> double_round128
    | 8 -> double_round256) s ...

inline_for_extraction
let core (#l: lane) (s: state l): St unit =
  ...
  // various calls to rounds
  ...

// these three NOT inline_for_extraction!
let core32 = core #1
let core128 = core #4
let core256 = core #8
```

This style allows `rounds` to dispatch, once it receive a concrete argument for
`l`, onto one of the three specialized instances of `double_round`. The three
versions of `double_round` remain as-is and appear as such in the generated
code: the structure of the call-graph is preserved, and `core32` reduces to a
function whose body contains calls to `double_round32`.

This style can be marginally improved upon, by replacing the definition of
rounds as follows:

```fstar
inline_for_extraction
let double_round #l =
  match l with
  | 1 -> double_round32
  | 4 -> double_round128
  | 8 -> double_round256

inline_for_extraction
let rounds (#l: lane) (s: state l): St unit =
  // looks just like before
  ... double_round #l s ...
```

Which is just a nice way to present the code.

The main drawback with this style is that we have lost the ability to split the
`_32` functions in their own file; furthermore, we also still cannot provide,
say, a microcoded version of `double_round256`.

The former issue could be remediated with some tricks in KreMLin; the latter,
however, is more serious.

Third and final attempt, using higher-order
-------------------------------------------

Instead of relying on local helpers that statically encode a *finite* set of
dispatch choices (like the version of `double_round` above), we use higher-order
to openly quantify on all valid implementations of `double_round`.

```fstar
// Chacha20_higher.fst

inline_for_extraction
let ( +| ) (#l: lane) (x y: elem l) =
  ...

inline_for_extraction
let line (#l: lane) (s: state l) =
  ...

inline_for_extraction
let double_round (#l: lane) (s: state l): St unit =
  ...
  // various calls to line
  ...

// Note that the type of the argument `double_round` does NOT have a #l parameter
inline_for_extraction
let rounds (#l: lane) (double_round: s: state l -> St unit) (s: state l): St unit =
  ... double_round s ...

inline_for_extraction
let core (#l: lane) (double_round: s: state l -> St unit) (s: state l): St unit =
  ... rounds #l double_round s
```

The second attempt offered i) specialization and iii) preserved the shape of
the call-graph. This third and final attempt preserves the shape of the
call-graph:

```fstar
// Chacha20.fst
let double_round32 = double_round #1
let core32 = core #1 double_round32
```

Thanks to the higher-order pattern, `core` takes an index, along with a version
of `double_round` *already specialized for that index*, and returns a version of
`core` that is, too, *specialized for that index*.

Therefore, once the client has specialized `double_round` to `double_round32`,
it gains the ability to generate a specialized version of `core` whose body
contains calls to the specialized `double_round32` that was just generated
above.

This also restores property ii): we have regained the ability to isolate each
set of specialized functions in a single file.

Finally, this fixes iv): if, say, we have a hardware implementation of
`double_round32`, it's easy to generate a fourth variant of the code for our
hypothetical architecture Lakey Lake.

```fstar
// Chacha20_Lakey.fst
let core256 = core #8 Vale.Chacha20.double_round
```

Automating the rewriting into the higher-order pattern
------------------------------------------------------

Now that we have understood the shape that our generated code ought to have, we
are ready to write a tactic that will automatically rewrite the first version
into the third version.

Functions that ought to remain in the resulting C call-graph (e.g.
`double_round`) are marked with the special `[@ Meta.Attribute.specialize ]`
attribute. Every function that transitively calls into a `specialize` node will
receive a specialized instance of it as a function parameter (e.g. `rounds` or
`core`).

Functions that are intended to disappear from the resulting C call-graph, but
that still ought to be traversed in order to find more specialized nodes (e.g.
`rounds`) are marked with the special `[@ Meta.Attribute.inline_ ]` attribute.

All other functions are left untouched; the absence of one of these two
attributes indicates to the tactic that it doesn't need to recursively traverse
any further (otherwise the traversal would be too large).

The tactic thus recursively walks the call-graph, recording how many functions
have been rewritten as it goes. There is no global state for tactics; we
therefore just thread a mapping, that to each "old" name associates: its new
(rewritten) name, along with the list of specialize nodes that are transitively
reachable through that (new) function.

Rewriting from the first style to the third style is done by invoking a `splice`
tactic, whose goal is to synthesize a `list signature_element` -- in other
words, a tactics that builds top-level declarations to be inserted at call-site.

```fstar
// Chacha20_higher.fst
%splice [
  double_round_higher;
  core_higher
] (Meta.specialize_call_graph [ `core ])
```

The list of names indicates, among all the declarations generated by
`specialize_call_graph`, which should be lexically bound in the scope that
follows the call to `%splice`. The argument to `specialize_call_graph` is the
list of definitions that should be visited.

Multiple definitions can be passed; if they end up calling into the same
functions marked with `Meta.Attribute.specialize`, only one specialized instance
will be generated, of course.
