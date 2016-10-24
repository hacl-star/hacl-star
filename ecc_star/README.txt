ECC* library

*** RUNNING THE OCAML SNAPSHOT **

An OCaml snapshot is included in the ./ml directory.

To install and run OCaml we recommand to use the OPAM package manager available at
https://opam.ocaml.org/doc/Install.html.
Also note that the 'ocamlfind', 'batteries' and 'stdint' libraries are required to execute
the extracted code: 'opam install ocamlfind batteries stdint'.

To build the curves from the snapshot move to the directory and run 'make'.

NB: The test drivers are located in curve_proof/ml.


*** F* INSTALLATION INSTRUCTIONS ***

F* sources can be found at https://github.com/FStarLang/FStar.

Note that new changes have been incorporated recently.
The code was last verified under git commit 1b356bf76f52adad576b6b501b45546183514b4e.

Instructions on how to build F* and install the Z3 SMT solver are given at
https://github.com/FStarLang/FStar/blob/master/INSTALL.md

We recommand reading F* files using emacs and its F* mode: 
https://github.com/FStarLang/fstar-mode.el

*** CODE STRUCTURE ***

The code is organized in three directories.
- the 'math_interfaces' directory contains the mathematical interfaces
- the 'bignum_proof' directory contains the code for the Bignum library
- the 'curve_proof' directory contains the code for the curve library
- the 'sage_scripts' directory contains SAGE SCRIPTS taken from www.hyperelliptic.org
- the 'itp_2014_coq_dev' directory contains the Coq development our proofs were inspired from

*** PROOF STRUCTURE ***

The proof structure is the following:

In the math_interfaces folder:
- the definitions.fst file defines abelian groups and commutative fields
- the field.fst file specifies a finite field
- the curve.fst file specifies an elliptic curve according to a previous Coq development

In the bignum_proof folder:
- the Axiomatic, IntLib and Lemmas modules provide some useful mathematical functions and lemmas
- the UInt module defines platform integers and assumes the provided operations which will be
  implemented practically be the OCaml module UInt64.ml from the bignum_proof/ml/ directory
- the Bigint and Eval module define the concrete bignum type and the mapping from this
  data type
- The rest of the modules detail the implementations of operators, to implement the top-level
  Bignum module in the bignum.fsti file

In the curve_proof folder:
- the ConcretePoint module defines the data structure to represent points on the curve
- the DoubleAndAdd module defines the doubling and adding function, informally proven by SAGE scripts are correct formulas
- the MontgomeryLadder module specifies a Montgomery ladder algorithm

The itp_2014_coq_dev folder contains the Coq developments on elliptic curves, from the paper
"A formal library for Elliptic Curves in the Coq proof Assistant" from Bartzia and al.
In particular 'ec.v' contains the definitions which 'math_interfaces/curve.fst' matches against.

The 'sage_scripts' folder contains the SAGE software scripts:
- add-2007-bl.sage.txt: the script for the Weierstrass curve addition (without doubling) in Jacobian coordinates
- dbl-2001-b.sage.txt: the script for the Weierstrass curve doubling in Jacobian coordinates
- ladd-1987-m2.sage.txt: the script for the Montgomery curves in Projective coordinates

*** PROOF ***
The location of F* root directory has to be ported to the Makefiles.

In the 'bignum_proof' directory, targets are provided to verify modules.
Running 'make' in that folder will run proofs for all modules.
Individual targets are also provided for each module individually, such as 'make fsum'.

In the 'curve_proof' directory, targets are provided to verify the point module and the montgomery ladder. The proofs of 'double_and_add.fst' (for Montgomery curves) and 'double_and_add2.fst' (for Weierstrass curves) relies on SAGE scripts.
Running 'make' in that folder willl run proofs for all modules.
Individual targets are also provided for each module individually, such as 'make ladder'.

*** CURVES ***
The location of F* root directory has to be ported to the Makefiles.

The library files extract to OCaml code and run using the OCaml compiler.
A running OCaml installation is thus needed to execute the code.

To install and run OCaml we recommand to use the OPAM package manager available at
https://opam.ocaml.org/doc/Install.html.
Also note that the 'ocamlfind', 'batteries' and 'stdint' libraries are required to execute
the extracted code.

A slight modification of F* library files is required: the file FStar_ST.ml located in
fstar_lib/ has to be copied to root_of_FStar/lib/ml, which can be done manually of running
'make fixlib'.

Then 'make curve25519' will build and run curve25519, just as 'make curve448' and 'make p256'.
