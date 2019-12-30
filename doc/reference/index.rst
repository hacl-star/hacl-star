.. The KreMLin user manual documentation master file, created by
   sphinx-quickstart on Mon Apr 23 15:16:54 2018.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

The HACL and EverCrypt reference manual
=======================================

This manual describes the HACL*, Vale and EverCrypt formally verified
cryptographic libraries.

Parts of these libraries appear in `Firefox
<https://bugzilla.mozilla.org/show_bug.cgi?id=1387183>`_, the Windows kernel,
the Linux kernel,
the `Tezos blockchain
<https://www.reddit.com/r/tezos/comments/8hrsz2/tezos_switches_cryptographic_libraries_from/>`_,
the Microsoft MSQuic implementation of the QUIC protocol,
and the `Wireguard VPN <https://lwn.net/Articles/770750/>`_.

.. image:: /diagram.png
   :width: 80%
   :align: center

- HACL* provides a set of highly efficient, pure C implementations of complete
  cryptographic primitives. Each algorithm comes with its own API callable from
  C clients.
- Vale provides optimized assembly (ASM) core routines for performance-critical
  code. Vale code is not intended to be called from C by end users.
- EverCrypt brings HACL* and Vale under an abstract, high-level API
  that automatically picks the best Vale or HACL* implementation depending on
  the machine the code is running on (multiplexing). EverCrypt also offers a
  single API for all algorithms from the same family (e.g. AEAD, hashes),
  allowing clients to reconfigure their choice of algorithm dynamically without
  recompiling (agility).

All of our code is verified using the F* programming language; once verified,
our code is extracted to a mixture of C and ASM.

Our code is callable from C clients, and from OCaml, via ctypes bindings. A
subset of our code (the HACL API) compiles to WebAssembly via a dedicated,
formalized codepath of the KreMLin_ compiler and can be used for any Web context
(e.g. Electron, website) where modern, trustworthy cryptography is in order.

In addition to unverified clients, verified clients can be built atop the
EverCrypt API. These include a library of Merkle Trees, distributed in the
present repository, but also an implementation of the Signal protocol in F*.


.. _KreMLin: https://github.com/FStarLang/kremlin/

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   Supported
   Overview
   Obtaining
   General
   HaclDoc
   EverCryptDoc
   Merkle
   WasmDoc
   OCamlDoc


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
