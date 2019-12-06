Overview
========

What is verified software
-------------------------

HACL*, Vale and EverCrypt are written and verified using the
`F* <https://github.com/FStarLang/kremlin/>`_
language, then compiled to a mixture of C (using a dedicated compiler,
KreMLin_) and assembly.

Our libraries' formal verification involves using software tools to analyze **all
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

* Side-channel resistance: Observations about our code's low-level behavior
  (specifically, the time it takes to execute or the memory addresses that it
  accesses) are independent of the secrets manipulated by the library. Hence, an
  adversary monitoring these "side-channels" learns nothing about the secrets.

All of these guarantees *do not* prevent our code from achieving good performance!
EverCrypt meets or beats the performance of most existing cryptographic implementations in C,
and for certain targeted platforms meets or beats the performance of state-of-the-art
libraries that rely on hand-tuned assembly code.

.. _KreMLin: https://github.com/FStarLang/kremlin/
