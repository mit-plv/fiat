Fiat − Deductive Synthesis of Abstract Data Types in a Proof Assistant
======================================================================

This repository holds the source code of Fiat, a Coq ADT synthesis
library.

This library is now mostly unmaintained; only targets `fiat-core parsers
parsers-examples` are maintained for Coq's CI.

## Dependencies:
  * To build the library:          Coq 8.4pl6 (use branch [v8.4](https://github.com/mit-plv/fiat/tree/v8.4)), Coq >= 8.16 (only `fiat-core parsers parsers-examples`)
  * To step through the examples:  GNU Emacs 24.3+, Proof General 4.4+
  * To extract and run OCaml code: OCaml 4.02.0+

## Compiling and running the code
  * To build the core library: `make fiat-core`
  * To build the SQL-like libary: `make querystructures` (no longer builds)
  * To build the parsers libary: `make parsers`
