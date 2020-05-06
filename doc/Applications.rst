Verified Applications
=====================

Several verification projects are based on HACL* and EverCrypt.

Everest/miTLS
-------------

The `miTLS <https://mitls.org>`_ verified TLS implementation being developed as part of Project Everest relies on EverCrypt for all its cryptography.
The current development of miTLS can be found `here <https://github.com/project-everest/mitls-fstar>`_.

LibSignal*
-------------

The `Signal* <https://signalstar.gforge.inria.fr/>`_ verified implementation of the Signal protocol is written in F* and compiles
to both C and WebAssembly. Both versions rely on HACL* for their crypto.

MerkleTree
-------------

The HACL* repository includes a verified Merkle Tree library in `/secure_api/merkle_tree` which uses the EverCrypt Hash API to
build and modify Merkle Trees.




