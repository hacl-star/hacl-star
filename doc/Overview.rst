Underlying research
===================

What is verified software?
--------------------------

Formal verification involves using software tools to analyze **all
possible behaviors** of a program and prove mathematically that they comply with
the code's specification (i.e., a machine-readable description of the
developer's intentions). Unlike software testing, formal verification provides
strong guarantees that a program behaves as expected and is free from entire
classes of errors.

Our specifications cover a range of properties, including:

* Memory safety: our code never violates memory abstractions,
  and, as a consequence, is free from common bugs and vulnerabilities like
  buffer overflows, null-pointer dereferences, use-after-frees, double-frees,
  etc.

* Type safety: our code respects the interfaces amongs its components
  including any abstraction boundaries; e.g., one component never passes
  the wrong kind of parameters to another, or accesses its private state.

* Functional correctness: our code's input/output behavior is fully
  characterized by simple mathematical functions derived directly
  from the official cryptographic standards (e.g., from NIST or the IETF).

* Secret Independence: Observations about our code's low-level behavior
  (specifically, the time it takes to execute or the memory addresses that it
  accesses) are independent of the secrets manipulated by the library. Hence, an
  adversary monitoring these "side-channels" learns nothing about the secrets.

All of these guarantees *do not* prevent our code from achieving good
performance!  HACL* meets or beats the performance of most existing
cryptographic implementations in C, and on certain platforms, Vale
code meets or beats the performance of hand-tuned assembly code in
state-of-the-art libraries.  By bringing them together, the EverCrypt
provider provides best-in-class performance on most platforms.


History and publications
------------------------

Our cryptographic code is the culmination of several years of research carried
through `Project Everest <https://project-everest.github.io/>`_.

Early attempts at verifying cryptographic code in F* were presented at CSF 2016:
`A Verified Extensible Library of Elliptic Curves
<https://hal.inria.fr/hal-01425957>`_ (Jean Karim Zinzindohoué, Evmorfia-Iro
Bartzia, Karthikeyan Bhargavan). This work established an initial body of
verified libraries, but extracted to OCaml and had substandard performance.
More on this early work be found in J-K Zinzindohoué's `Ph.D. thesis
<https://www.theses.fr/s175861>`_.

To deliver better performance, we established a C-like subset of F* that would
compile to C, called Low*. Its foundations were presented at ICFP 2017:
`Verified Low-Level Programming Embedded in F\*
<https://arxiv.org/abs/1703.00053>`_ (Jonathan Protzenko, Jean-Karim
Zinzindohoué, Aseem Rastogi, Tahina Ramananandro, Peng Wang, Santiago
Zanella-Béguelin, Antoine Delignat-Lavaud, Cătălin Hriţcu, Karthikeyan
Bhargavan, Cédric Fournet, and Nikhil Swamy).

Using Low*, and inspired by discussions at the
`HACS series of workshops <https://github.com/HACS-workshop>`_, we presented the
first version of the HACL* library at CCS 2017:
`HACL*: A Verified Modern Cryptographic Library
<http://eprint.iacr.org/2017/536>`_ (Jean-Karim Zinzindohoué, Karthikeyan
Bhargavan, Jonathan Protzenko, Benjamin Beurdouche).

In parallel to work on HACL*, the Vale team set out to design a DSL for assembly programming,
for those algorithms which could not achieve maximal performance unless written in hand-tuned
assembly. The first version of Vale, which used Dafny as its verified backend,
was presented at Usenix 2017 (distinguished paper award): `Vale: Verifying
High-Performance Cryptographic Assembly Code
<https://project-everest.github.io/assets/vale2017.pdf>`_ (Barry Bond, Chris
Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno,
Ashay Rane, Srinath Setty, Laure Thompson).

In order to unify C-like and ASM-like programming, Vale was overhauled to use F*
as its verification infrastructure; this second version of Vale was presented at
POPL 2019: `A Verified, Efficient Embedding of a Verifiable Assembly Language
<https://www.microsoft.com/en-us/research/publication/a-verified-efficient-embedding-of-a-verifiable-assembly-language/>`_
(Aymeric Fromherz, Nick Giannarakis, Chris Hawblitzel, Bryan Parno, Aseem
Rastogi, Nikhil Swamy).

Having both C-like and ASM-like implementations all expressed in F* allowed us
to connect the two semantics and establish deep integrations between parts of
the codebase written in C and those written in assembly. Connecting C and ASM also
enabled implementation multiplexing and algorithmic agility, while establishing
strong abstraction boundaries to serve as a foundation for other verified
clients. We call the result EverCrypt: `EverCrypt: A Fast, Verified,
Cross-Platform Cryptographic Provider <https://eprint.iacr.org/2019/757>`_
(Jonathan Protzenko, Bryan Parno, Aymeric Fromherz, Chris Hawblitzel, Marina
Polubelova, Karthikeyan Bhargavan, Benjamin Beurdouche, Joonwon Choi, Antoine
Delignat-Lavaud, Cedric Fournet, Tahina Ramananandro, Aseem Rastogi, Nikhil
Swamy, Christoph Wintersteiger and Santiago Zanella-Beguelin).

Our Verification Tools
----------------------

HACL* and EverCrypt are written and verified
using the `F* <https://github.com/FStarLang/kremlin/>`_ language, then compiled
to a mixture of C (using a dedicated compiler, KreMLin_).

The Vale cryptographic libraries (used in EverCrypt) rely on the
Vale_ tool, which compiles the Vale DSL to F*, and is
responsible for compiling the Vale code to assembly.

.. _Vale: https://github.com/project-everest/vale/
.. _KreMLin: https://github.com/FStarLang/kremlin/
