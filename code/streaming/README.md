This is a generic facility for building streaming APIs on top of block-based
APIs. While block-based APIs require the client to chunk the data and only feed
it block-by-block, streaming-based APIs use an internal buffer in order to
relieve the client of any modulo computations and/or error-prone buffering.
