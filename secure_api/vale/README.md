Some wrappers around ASM implementations written using Vale.

We combine into asm/vale.a the .S files and thin C wrappers that expose the
correct API and calling conventions. It may be the case the ASM only implements
selected chunks of the algorithm, meaning that extra C files are needed, as in
the case of SHA256.

To avoid taking an actual dependency on Vale, we import and check into the
repository the required files that are produced by Vale.
