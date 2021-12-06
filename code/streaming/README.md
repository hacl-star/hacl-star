This is a generic facility for building streaming APIs on top of block-based
APIs. While block-based APIs require the client to chunk the data and only feed
it block-by-block, streaming-based APIs use an internal buffer in order to
relieve the client of any modulo computations and/or error-prone buffering.

Examples of how to use the streaming API in Low*:
- [HACL API](https://github.com/project-everest/hacl-star/blob/59d6494b8eeeed847ebd6ef8b5a220554db6dbfb/code/ed25519/Hacl.Impl.SHA512.ModQ.fst#L31)
- [EverCrypt API](https://github.com/project-everest/hacl-star/blob/2e0595154ae5cdce2af30ef4be1e24258577002d/providers/test/Test.Hash.fst#L36)
