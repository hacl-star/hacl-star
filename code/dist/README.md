This directory contains the HACL\* library compiled as a set of C files.

- The `generic` flavor has no particular optimizations and generates a lot of
  files.
- The `compact` flavor uses a fine-tuned invocation of the KreMLin compiler to
  generate a minimal set of files, with a minimal set of includes. It also
  includes some often-requested features, e.g. extra parentheses and curly
  braces, to facilitate integration into existing software projects.
