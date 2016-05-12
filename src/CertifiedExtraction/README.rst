Certified extraction using correct-by-construction program synthesis
====================================================================

Getting started
~~~~~~~~~~~~~~~

Dependencies
------------

Coq ∈ v8.4pl[2-6] (Bedrock doesn't support 8.5)

Setting up
----------

1. Bedrock::

     git clone --recursive git@github.mit.edu:plv/bedrock.git --branch facade-generic-specs
     make -C bedrock -j4 qsfacade

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
  │   ├── ProcessScheduler.v             A more ambitious example, using trees
  │
  ├── Extraction                       Implementation of the extraction logic
  │   │
  │   ├── External                       Calls to generically defined data structures
  │   │
  │   ├── QueryStructures                Compiler for ICFP 2016 submission
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

Two preliminary examples of Binary encoders are in ./Benchmarks/MicroEncoders.v.
