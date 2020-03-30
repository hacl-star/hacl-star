.. The KreMLin user manual documentation master file, created by
   sphinx-quickstart on Mon Apr 23 15:16:54 2018.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

A High Assurance Cryptographic Library
======================================

HACL* is a formally verified cryptographic library written in `F*
<https://github.com/FStarLang/FStar>`_ and compiled to C, developed as a collaboration
between the `Prosecco <http://prosecco.inria.fr>`_ team at INRIA
Paris, `Microsoft Research <http://research.microsoft.com>`_, and
`Carnegie Mellon University <https://www.csd.cs.cmu.edu/>`_. The
library, its applications, and the verification tools it relies on are
being actively developed and maintained as part of `Project Everest
<https://github.com/project-everest>`_.

EverCrypt is a cryptographic *provider* that into a single library combines
HACL*, described above, and ValeCrypt, a collection of verified assembly
code for cryptographic primitives. This manual describes the HACL* and EverCrypt APIs. Read
:ref:`hacl-vale-evercrypt` for a detailed description of how they relate to each
other.

HACL* is an open source project hosted at `hacl-star
<https://github.com/project-everest/hacl-star/>`_, along with ValeCrypt_
and `EverCrypt <https://github.com/project-everest/hacl-star/tree/master/evercrypt>`_.
HACL*, Vale and EverCrypt are distributed together as a collection of C and
assembly files. These can be used either as individual components, or as a
full-fledged library through the EverCrypt provider.

Code from HACL* has been incorporated into `Firefox
<https://bugzilla.mozilla.org/show_bug.cgi?id=1387183>`_, the Windows
kernel, the Linux kernel, the `Tezos blockchain
<https://www.reddit.com/r/tezos/comments/8hrsz2/tezos_switches_cryptographic_libraries_from/>`_,
the Microsoft MSQuic implementation of the QUIC protocol, and the
`Wireguard VPN <https://lwn.net/Articles/770750/>`_. Still,
HACL*, Vale, and EverCrypt remain ongoing research projects and should
be treated as such. If you want to integrate this code into a production environment,
or if you have any questions, comments, or feature requests for HACL*, Vale,
or EverCrypt, initiate a conversation with the `HACL* maintainers <mailto:hacl-star-maintainers@lists.gforge.inria.fr>`_

.. _KreMLin: https://github.com/FStarLang/kremlin/
.. _ValeCrypt: https://github.com/project-everest/hacl-star/tree/master/vale

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   HaclValeEverCrypt
   Supported
   Overview
   Obtaining
   General
   HaclDoc
   EverCryptDoc
   API
   Applications
   Javascript


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
