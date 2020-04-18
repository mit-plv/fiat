Extensible Extraction of Efficient Imperative Programs with Foreign Functions, Manually Managed Memory, and Proofs
==================================================================================================================

Getting started
~~~~~~~~~~~~~~~

This archive contains source code for Fiat
and Bedrock, compilable with Coq version 8.4pl6.  Our extensions live in
Bedrock's ``bedrock/Bedrock/Platform/Facade`` folder, and in Fiat's
``fiat/src/CertifiedExtraction/`` folder.

Browsing the code
~~~~~~~~~~~~~~~~~

Quick peek
----------

We have annotated all of the examples discussed by the paper with comments and
copied of Coq's output, making it easy to browse the code and results without
compiling. All examples live in ``fiat/src/CertifiedExtraction/Benchmarks``

- The file ``MicrobenchmarksAnnotated.v`` contains a brief introduction and a
  collection of simple compilation examples.

- The file ``ProcessScheduler.v`` presents the paper's main case study.

- The file ``MicroEncoders.v`` contains a third category of examples, extracting
  serializers for simple packet formats into efficient Facade code.


Exploring the source
--------------------

Here is an outline of the fiat/src/CertifiedExtraction folder::

  ./src/CertifiedExtraction

  ├── Benchmarks                       Various compilation examples
  │   ├── MicrobenchmarksAnnotated.v     Examples of small Fiat programs being compiled to Facade
  │   ├── ProcessScheduler.v             The paper's core example, compiling database queries
  │   ├── MicroEncoders.v                Another application domain, producing efficient packet serializers
  │
  ├── Extraction                       Implementation of the extraction logic
  │   │
  │   ├── External                       Calls to generically defined data structures
  │   │
  │   ├── QueryStructures                Query structures
  │   │   ├── CallRules                    Calls to Bedrock data structures
  │   │   ├── Wrappers.v                   Injections of Fiat datatypes into Bedrock
  │   │
  │   ├── BinaryEncoders                 Compilers for packet serialization code
  │   │   ├── CallRules                    Calls to Bedrock data structures
  │   │   ├── Wrappers.v                   Injections of Fiat datatypes into Bedrock
  │
  ├── ADT2CompileUnit.v                Translation of Fiat specs to Bedrock specs
  ├── Core.v                           Main definitions (telescopes, Hoare triples, wrappers)
  └── ...                              Properties of telescopes and triples

Diving in
---------

To build out code, extract this archive to a folder on your hard drive, say
``/build/ijcar2020``, then adjust the ``COQPATH`` environment variable to point to
that folder::

  export COQPATH=/build/ijcar2020/bedrock:

You can then compile our code::

  cd /build/ijcar2020
  make -C bedrock -j4 facade qsfacade
  make -C fiat -j4 \
    src/CertifiedExtraction/Benchmarks/MicrobenchmarksAnnotated.vo \
    src/CertifiedExtraction/Benchmarks/ProcessScheduler.vo \
    src/CertifiedExtraction/Benchmarks/MicroEncoders.vo
