The things left to be done (or assumed):

* Hacl.Impl.MM.Exponent - 
	* lemma_l_fermat - 
		pow a (prime_p256_order - 1) % prime_p256_order == 1
		little fermat theorem. 
		Lives in Hacl.Impl.MM.Exponent.

	*  k0 upload
		upload inverse (number) % pow2 64.
		Z3 can't prove it correctly, used the code in Sage to prove (by hand) that the parameter is correct.

* Hacl.Impl.P256 - 
	*	admits  montgomery_ladder_step function, because it kills F*. No idea why. Post conditions are asserts, and by assert proved to satisfy.
	* val lemma_modular_multiplication_p256_2: 
  		(a * pow2 256 % prime = b * pow2 256 % prime  <==> a == b)
		(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)
		(* if a ≡ b (mod n), then k a ≡ k b (mod n) for any integer k (compatibility with scaling) *)
		(*p = 2^256 - 2^224 + 2^192 + 2^96 - 1 

* SolinasReduction - 
	*	val lemma_xor_zero: low: uint64{uint_v (get_high_part low) ==  0} -> high: uint64{uint_v (get_low_part high) == 0} ->  Lemma (uint_v (logxor low high) = uint_v high * pow2 32 + uint_v low)
		No idea how to prove it. Used for uploading the variables in solinas reduction.

* Hacl.Spec.ECDSA - 
	* prove that inverse is indeed a * (prime - 2).
		Didnot work because of the wrong approach for scalar presentation as nat?


* bunch of staff in Lemmas. I will try to solve by myself, small annoying pieces of code.


NB: Point add in the Impl assumes that points are IN DOMAIN. And doesnot take them away after. Need to work together with (toDomain) + point add + (from Domain). I will changes asa I have time.

NB: the file test P256 is a set of tests. Some tests are commented because the previous version was taking an ARBITRARY key size, whereas the current one is waiting for 32 byte scalar. Other than that, the function to do scalar multiplication (together with toDomain, fromDomain) is     
	scalarMultiplication(pub,key,priv,tempBuffer).


