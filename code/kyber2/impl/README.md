Library details (files Lib.*) :
- Arithmetic.Group : declaration of the monoid and group typeclasses, and some type dependant functions acting on them + instances on pure int and nat
- Arithmetic.Group.Sequence : instances of the above typeclasses on lseq
- Arithmetic.Group.Uint_t : instances on unsigned machine integer
- Arithmetic.Ring : the ring typeclass + type dependant functions
- Arithmetic.Ring.Sequence : ring instance on lseq
- Arithmetic.Ring.Uint_t : ring instance on unsigned machine integer
- Arithmetic.Sums : expressing big sums (indexed by n) with lseq and typeclasses + fubini theorem + explicit bit reversal reordering
- Arithmetic.SumsBuffer : a naive implementation of Sums with buffers
- Lib.ModularArithmetic : a pure specification of Zq
- Lib.ModularArithmetic.Lemmas : useful lemmas on Zq arithmetic
- NumericTypes : recursive declaration of algebraic types : integers of Zq, polynomials, vectors, matrices.
- Lib.Poly : declaration of addition and multiplication in Zq[X]/(X^n+1) in the normal domain
- Lib.Poly.NTT : declaration of the NTT used in Kyber Round1 + some properties
- Lib.Poly.NTT2 : declaration of the NTT used in Kyber Round2 + some properties

Specification details (files Spec.* ) :
- CBD : the primitives to generate a centered binomial random distribution
- FunctionInstantiation : the implementation of Kyber's hash functions and key derivation function, as well as a function to generate a uniform distribution on Zq from a random distribution on uint16.
- Group : declaration of the group arithmetic on Zq with q = 3329 (Kyber spec) using machine integers + constant time operations
- GroupMontgomery : the group arithmetic on Zq expressed in the montgomery domain
- Indcpa : the Primitives for the Indcpa scheme + encoding of secrets as byte streams
- Kem : the CCA-KEM
- Lemmas : some small lemmas : we should aim to remove this file and integrate those lemmas in other modules
- NTT : Kyber's mathematical NTT + the induction property satisfied by the NTT
- NumericTypes : types for Kybers algebraic objects + accessors and modifiers
- Params : the set of parameters
- Poly : compression and decompression functions + proof of small error
- Reduce : montgomery, barrett reduction + division by q=3329 in constant time
- Ring : the ring Zq in Kyber
- Unsafe (fsti only) : do not use unless you want to "fill the blanks" with unchecked code. You will need to provide an external implementation during the compilation

Implementation details (files Impl.*) :
- Sums : implementation of Lib.Sums in the normal integer representation and the montgomery space
- CBD : implementation of CBD
- FunctionInstantiation : implementation of hash function, key derivation + random distribution on Zq (normal space + montgomery)
- Group : implementation of Group in the normal representation
- GroupMontgomery : in the montgomery space (+ links to and from the normal space)
- Indcpa : the implementation of the Indcpa scheme (TODO)
- Kem : the CCA-KEM (TODO)
- NTT : an attempt to implement NTT with Cooley-Tukey algorithm. if this is not a priority, just use Lib.SumBuffer to build a quadratic implementation (TO FINISH)
- NumericTypes : the flat implementation of Kyber types as buffers + accessors + modifiers + ghost interpretation as specification types + generators
- NumericTypes.Montgomery : same as before, but in the montgomery space with systematic modular reductions
- NumericTypes.MontgomeryInt16 : same as before, but only performs modular reduction when there may be an overflow
- Poly : implementation of compression and decompression (TODO, mainly map functions)
- Reduce : the reductions
- Ring : implementation of Zq ring