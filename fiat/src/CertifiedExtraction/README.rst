Extensible Extraction of Efficient Imperative Programs with Foreign Functions, Manually Managed Memory, and Proofs
==================================================================================================================

Getting started
~~~~~~~~~~~~~~~

Dependencies
------------

Coq v8.4pl6

Setting up
----------

1. Bedrock::

     git clone --recursive git@github.mit.edu:plv/bedrock.git --branch facade-generic-specs
     make -C bedrock -j4 facade qsfacade

2. Fiat::

     export COQPATH=PATH_TO_BEDROCK_CLONE
     git clone --recursive git@github.mit.edu:plv/fiat.git --branch binencoders-compiler
     make -C fiat -j4 extraction

Browsing the code
~~~~~~~~~~~~~~~~~

Outline
-------

Here is an outline of the CertifiedExtraction folder::

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

The file ./Benchmarks/MicrobenchmarksAnnotated.v contains a short introduction
and a collection of simple compilation examples.

The file ./Benchmarks/ProcessScheduler has the paper's main example.

The file ./Benchmarks/MicroEncoders.v contains examples compilers for simple
packets layouts, extracted into efficient Facade code.
