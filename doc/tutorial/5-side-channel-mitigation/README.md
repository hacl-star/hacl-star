## Example 4 - side channel mitigation

In Hacl we use a wrapper mechanism around *secret* integers to prevent branching or array accesses based on their values, as well as the use of some of the arithmetic operators.

This wrapper mechanism (see [Hacl.UInt32.fst](https://github.com/mitls/hacl-star/blob/master/code/lib/Hacl.UInt32.fst) for instance) leaves all the implementation details visible to the SMT solver. *Hacl* integers and F* integers share the same logic for the operators they have in common.

They are, however, implemented as different types, since *Hacl* integers are implemented are wrapping F* machine integers in a Data Constructor. This means that, as oppposed to what would be the case if *Hacl* integers had been a simple refinement on F* integers, one cannot be use where the other was expected.
Also, in the *Hacl* integers implementation appears the `noeq` keyword in the type declaration. This means that we implement no concrete homogeneous equality (`=`) for these types. This being the only *equaity* concrete function usable in F* (the `==` equality is heterogeneous and reserve to specifications), this prevents the programmer from writing equality tests that may leak some information on sensitive data.

Similarly compared to the native F* machine integers, the *Hacl* integers have:
- No division or remainder operators defined, as those are often not constant-time.
- No comparison operators (such as greater than or equal)
- More gnerally, no concrete functions returning a native F* type. This means that when computing on a *Hacl* integer, the only type one can return is a *Hacl* integer (except in ghost code).
- Coerciions from F* to Hacl integers, but not the other way,
- Masking operators to replace the comparison operators :
```F#
val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})
```

Those can be used to implement constant time operations.
For instance, assuming that one has a bignum for which all the limbs are < 2^51 which she wants to reduce to a Z/(2^255-19)Z value, here is a way to do it:
```F#
val normalize: b:felem -> Stack unit
    (requires (fun h -> live h b /\ v (get h b 0) < pow2 51
        /\ v (get h b 0) < pow2 51 /\ v (get h b 0) < pow2 51
        /\ v (get h b 0) < pow2 51 /\ v (get h b 0) < pow2 51))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
        /\ eval h1 b = (eval h0 b) % (2^255-19)))
let normalize b =
  let mask_2_51 = 0x7ffffffffffffuL in //2^51 - 1
  let mask_2_51m19 = 0x7ffffffffffeduL in //2^51 - 19
  let mask = (eq_mask b.(4ul) mask_2_51) `logand`
	     (eq_mask b.(3ul) mask_2_51) `logand`
	     (eq_mask b.(2ul) mask_2_51) `logand`
	     (eq_mask b.(1ul) mask_2_51) `logand`
	     (gte_mask b.(0ul) mask2_51m19) in
  b.(0ul) <- b.(0ul) -^ mask2_51m19 `logand` mask;
  b.(1ul) <- b.(1ul) -^ b.(1ul) `logand` mask;
  b.(2ul) <- b.(2ul) -^ b.(2ul) `logand` mask;
  b.(3ul) <- b.(3ul) -^ b.(3ul) `logand` mask;
  b.(4ul) <- b.(4ul) -^ b.(4ul) `logand` mask
```

Of course some algorithms need to leak some information, for instance to verify a *MAC*.
In such cases we provide a declassification primitive, and the places were declassification happen must be carefully reviewed.
