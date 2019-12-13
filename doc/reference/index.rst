.. The KreMLin user manual documentation master file, created by
   sphinx-quickstart on Mon Apr 23 15:16:54 2018.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

The HACL and EverCrypt reference manual
=======================================

This manual describes the HACL*, Vale and EverCrypt formally verified
cryptographic libraries.

.. Need to figure out how to make this image only use 80% of the width.
.. image:: /diagram.png
   :width: 80%
   :align: center

All of our code is verified, all together, using the F* programming language.

HACL* provides a set of highly efficient, pure C implementations of complete
cryptographic primitives. Vale provides optimized assembly (ASM) core routines
for performance-critical code.

EverCrypt brings HACL* and Vale together under an abstract, high-level API that
automatically picks the best Vale or HACL* implementation depending on the
machine the code is running on; furthermore, EverCrypt offers a single API for
all algorithms from the same family (e.g. AEAD, Hashes), allowing clients to
reconfigure their choice of algorithm dynamically without recompiling.

EverCrypt serves as a foundation for verified and unverified applications alike.

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   Overview
   Obtaining
   HaclDoc
   EverCryptDoc
   WasmDoc
   OCamlDoc


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
