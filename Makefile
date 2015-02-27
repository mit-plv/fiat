CORE_MODULES    := \
	Common \
	Common/Equality \
	Common/Monad \
	Common/ReservedNotations \
	Common/ilist \
	Common/i2list \
	Common/ilist2 \
	Common/i2list2 \
	Common/StringBound \
	Common/DecideableEnsembles \
	Common/IterateBoundedIndex \
	Common/BoolFacts \
	Common/ListFacts \
	Common/FlattenList \
	Common/LogicFacts \
	Common/NatFacts \
	Common/ListMorphisms \
	Common/LogicMorphisms \
	Common/Ensembles \
	Common/Ensembles/EnsembleListEquivalence \
	Common/Ensembles/Cardinal \
	Common/Ensembles/IndexedEnsembles \
	Common/Ensembles/Equivalence \
	Common/Ensembles/Morphisms \
	Common/Ensembles/Tactics \
	Common/Ensembles/CombinatorLaws \
	Common/Ensembles/Notations \
	Common/PermutationFacts \
	Common/String_as_OT \
	Common/FMapExtensions \
	Common/SetEq \
	Common/SetEqProperties \
	ComputationalEnsembles \
	ComputationalEnsembles/Core \
	ComputationalEnsembles/Laws \
	ComputationalEnsembles/Morphisms \
	Computation/Notations \
	Computation/Core \
	Computation/Monad \
	Computation/LogicLemmas \
	Computation/SetoidMorphisms \
	Computation/ReflectiveMonad \
	Computation/ApplyMonad \
	Computation/Refinements/General \
	Computation/Refinements/Tactics \
	Computation \
	ADT/ADTSig \
	ADT/Core \
	ADT/ADTHide \
	ADT/ComputationalADT \
	ADT \
	Common/ilist \
	Common/Wf \
	Common/Le \
	Common/UIP \
	ADTNotation/BuildADTSig \
	ADTNotation/BuildADT \
	ADTNotation/BuildComputationalADT \
	ADTNotation/BuildADTReplaceMethods \
	ADTNotation \
	ADTRefinement/Core \
	ADTRefinement/SetoidMorphisms \
	ADTRefinement/BuildADTSetoidMorphisms \
	ADTRefinement/GeneralRefinements \
	ADTRefinement/GeneralBuildADTRefinements \
	ADTRefinement \
	ADTRefinement/Refinements/DelegateMethods \
	ADTRefinement/Refinements/HoneRepresentation \
	ADTRefinement/Refinements/SimplifyRep \
	ADTRefinement/Refinements/ADTRepInv \
	ADTRefinement/Refinements/ADTCache \
	ADTRefinement/Refinements/RefineHideADT \
	ADTRefinement/Refinements \
	ADTRefinement/BuildADTRefinements/HoneRepresentation \
	ADTRefinement/BuildADTRefinements/SimplifyRep \
	ADTRefinement/BuildADTRefinements/AddCache \
	ADTRefinement/BuildADTRefinements

QUERYSTRUCTURE_MODULES := \
	QueryStructure/Specification/Representation/Notations \
	QueryStructure/Specification/Representation/Heading \
	QueryStructure/Specification/Representation/Tuple \
	QueryStructure/Specification/Representation/Schema \
	QueryStructure/Specification/Representation/Relation \
	QueryStructure/Specification/Representation/QueryStructureSchema \
	QueryStructure/Specification/Representation/QueryStructure \
	QueryStructure/Specification/Representation/QueryStructureNotations \
	QueryStructure/Specification/Constraints/tupleAgree \
	QueryStructure/Specification/Operations/FlattenCompList \
	QueryStructure/Specification/Operations/Empty \
	QueryStructure/Specification/Operations/Query \
	QueryStructure/Specification/Operations/Insert \
	QueryStructure/Specification/Operations/Delete \
	QueryStructure/Specification/Operations/Mutate \
	QueryStructure/Specification/Operations/Update \
	QueryStructure/Implementation/Constraints/ConstraintChecksRefinements \
	QueryStructure/Implementation/Constraints/ConstraintChecksUnfoldings \
	QueryStructure/Implementation/Operations/General/EmptyRefinements \
	QueryStructure/Implementation/Operations/General/QueryRefinements \
	QueryStructure/Implementation/Operations/General/InsertRefinements \
	QueryStructure/Implementation/Operations/General/MutateRefinements \
	QueryStructure/Implementation/Operations/General/DeleteRefinements \
	QueryStructure/Implementation/Operations/General/QueryStructureRefinements \
	QueryStructure/Implementation/Operations \
	QueryStructure/Implementation/Operations/List/ListQueryRefinements \
	QueryStructure/Implementation/Operations/List/ListInsertRefinements \
	QueryStructure/Implementation/ListImplementation \
	QueryStructure/Implementation/DataStructures/Bags/BagsInterface \
	QueryStructure/Implementation/DataStructures/Bags/BagsProperties \
	QueryStructure/Implementation/DataStructures/Bags/BagsTactics \
	QueryStructure/Implementation/DataStructures/Bags/ListBags \
	QueryStructure/Implementation/DataStructures/Bags/CountingListBags \
	QueryStructure/Implementation/DataStructures/Bags/TreeBags \
	QueryStructure/Implementation/DataStructures/Bags/CachingBags \
	QueryStructure/Implementation/DataStructures/Bags/CacheableFunctions \
	QueryStructure/Implementation/DataStructures/Bags/BagsOfTuples \
	QueryStructure/Implementation/DataStructures/BagADT/BagADT \
	QueryStructure/Implementation/DataStructures/BagADT/BagImplementation \
	QueryStructure/Implementation/DataStructures/BagADT/QueryStructureImplementation \
	QueryStructure/Implementation/DataStructures/BagADT/IndexSearchTerms \
	QueryStructure/Implementation/Operations/BagADT/Refinements \
	QueryStructure/Implementation/BagImplementation \
	QueryStructure/Automation/AutoDB

FINITESET_MODULES := \
	FiniteSetADTs \
	FiniteSetADTs/FiniteSetADT \
	FiniteSetADTs/FiniteSetADTMethodLaws \
	FiniteSetADTs/FiniteSetADTImplementation \
	FiniteSetADTs/FiniteSetRefinement \
	FiniteSetADTs/WordInterface \
	FiniteSetADTs/NatWord \
	FiniteSetADTs/BedrockWord \

SRC_GRAMMAR_MODULES := \
	Parsers/ContextFreeGrammar\
	Parsers/ContextFreeGrammarProperties\
	Parsers/ContextFreeGrammarNotations

SRC_PARSERS_BASE_MODULES := \
	Parsers/StringLike\
	Parsers/StringLike/Core\
	Parsers/StringLike/Properties\
	Parsers/StringLike/Examples\
	Parsers/DependentlyTyped\
	Parsers/DependentlyTypedOption\
	Parsers/DependentlyTypedSum\
	Parsers/DependentlyTypedMinimal\
	Parsers/DependentlyTypedMinimalOfParse\
	Parsers/DependentlyTypedMinimalOfParseFactored\
	Parsers/DependentlyTypedMinimalOfParseFactoredFull\
	Parsers/BooleanRecognizer\
	Parsers/WellFoundedParse\
	Parsers/MinimalParse\
	Parsers/MinimalParseOfParse\
	Parsers/BooleanRecognizerCorrect

SRC_PARSERS_MODULES := \
	Parsers/Specification\
	$(SRC_PARSERS_BASE_MODULES)\
	$(SRC_GRAMMAR_MODULES)

#	QueryStructure/Refinements/BagADT/DelegateImplementation\

COMPILER_MODULES := \
	FiatToFacade/StringMapNotations \
	FiatToFacade/FacadeNotations \
	FiatToFacade/Utilities \
	FiatToFacade/BedrockUtilities \
	FiatToFacade/StringMapUtilities \
	FiatToFacade/FacadeNotations \
	FiatToFacade/FacadeUtilities \
	FiatToFacade/Superset \
	FiatToFacade/SupersetMorphisms \
	FiatToFacade/SupersetUtilities \
	FiatToFacade/Prog \
	FiatToFacade/ProgEquiv \
	FiatToFacade/ProgUtilities \
	FiatToFacade/ProgMorphisms \
	FiatToFacade/Loop \
	FiatToFacade/LoopUtilities \
	FiatToFacade/GLabelMapFacts \
	FiatToFacade/Compiler/Utilities \
	FiatToFacade/Compiler/Prerequisites \
	FiatToFacade/Compiler/Basics \
	FiatToFacade/Compiler/Pairs \
	FiatToFacade/Compiler/Cleanup \
	FiatToFacade/Compiler/NoOp \
	FiatToFacade/Compiler/Copy \
	FiatToFacade/Compiler/Constants \
	FiatToFacade/Compiler/Binops \
	FiatToFacade/Compiler/Conditionals \
	FiatToFacade/Compiler/ADTs/FiniteSets \
	FiatToFacade/Compiler/ADTs/ListsInversion \
	FiatToFacade/Compiler/ADTs/Lists \
	FiatToFacade/Compiler/ADTs/Folds \
	FiatToFacade/Compiler/Automation/Vacuum \
	FiatToFacade/Compiler/Automation/FacadeHelpers \
	FiatToFacade/Compiler/Automation/SpecializedFolds \
	FiatToFacade/Compiler

EXAMPLE_MODULES := \
	QueryStructure/BookstorewDelegationSemiAutomatic \
	QueryStructure/WeatherwDelegation \
	QueryStructure/StockswDelegation
#FiniteSetsADTs/FiniteSetsExamples \
	ExtractingFiniteSetsExamples \
	QueryStructure/Bookstore \
	QueryStructure/BookstoreSemiAutomatic \
	QueryStructure/Weather \
	QueryStructure/Stocks \
	ProcessScheduler \
	CacheADT/KVEnsembles \
	CacheADT/CacheSpec \
	CacheADT/CacheRefinements \
	CacheADT/FMapCacheImplementation \
	CacheADT/LRUCache \
	BookstoreCache \


COQDEP=coqdep
COQDOC=coqdoc
CITO_ARGS=

UNPREFIXED_CORE_VS := $(CORE_MODULES:%=%.v)
UNPREFIXED_CORE_VOS:= $(CORE_MODULES:%=%.vo)
UNPREFIXED_CORE_VD := $(CORE_MODULES:%=%.v.d)

CORE_VS := $(CORE_MODULES:%=src/%.v)
CORE_VOS:= $(CORE_MODULES:%=src/%.vo)
CORE_VDS:= $(CORE_MODULES:%=src/%.v.d)

COMPILER_VS  := $(COMPILER_MODULES:%=src/%.v)
COMPILER_VDS := $(COMPILER_MODULES:%=src/%.v.d)
COMPILER_VOS := $(COMPILER_MODULES:%=src/%.vo)

QUERYSTRUCTURE_VS  := $(QUERYSTRUCTURE_MODULES:%=src/%.v)
QUERYSTRUCTURE_VDS := $(QUERYSTRUCTURE_MODULES:%=src/%.v.d)
QUERYSTRUCTURE_VOS := $(QUERYSTRUCTURE_MODULES:%=src/%.vo)

SRC_PARSERS_VS  := $(SRC_PARSERS_MODULES:%=src/%.v)
SRC_PARSERS_VDS := $(SRC_PARSERS_MODULES:%=src/%.v.d)
SRC_PARSERS_VOS := $(SRC_PARSERS_MODULES:%=src/%.vo)
PREFIXED_SRC_PARSERS_VOS:= $(SRC_PARSERS_MODULES:%=src/%.vo)

SRC_PARSERS_BASE_VS  := $(SRC_PARSERS_BASE_MODULES:%=src/%.v)
SRC_PARSERS_BASE_VDS := $(SRC_PARSERS_BASE_MODULES:%=src/%.v.d)
SRC_PARSERS_BASE_VOS := $(SRC_PARSERS_BASE_MODULES:%=src/%.vo)
PREFIXED_SRC_PARSERS_BASE_VOS:= $(SRC_PARSERS_BASE_MODULES:%=src/%.vo)

FINITESET_VS  := $(FINITESET_MODULES:%=src/%.v)
FINITESET_VDS := $(FINITESET_MODULES:%=src/%.v.d)
FINITESET_VOS := $(FINITESET_MODULES:%=src/%.vo)

EXAMPLE_VS := $(EXAMPLE_MODULES:%=examples/%.v)
EXAMPLE_VOS:= $(EXAMPLE_MODULES:%=examples/%.vo)

V = 0

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

SILENCE_OCAMLC_0 = @echo "OCAMLC $<"; #
SILENCE_OCAMLC_1 =
SILENCE_OCAMLC = $(SILENCE_OCAMLC_$(V))

SILENCE_OCAMLDEP_0 = @echo "OCAMLDEP $<"; #
SILENCE_OCAMLDEP_1 =
SILENCE_OCAMLDEP = $(SILENCE_OCAMLDEP_$(V))

SILENCE_OCAMLOPT_0 = @echo "OCAMLOPT $<"; #
SILENCE_OCAMLOPT_1 =
SILENCE_OCAMLOPT = $(SILENCE_OCAMLOPT_$(V))

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

COQDOCFLAGS=-interpolate -utf8

FAST_TARGETS := clean archclean printenv clean-old

.PHONY: all fiat querystructures parsers finitesets examples html clean pretty-timed pretty-timed-files pdf doc clean-doc cheat parsers-base

all : fiat querystructures parsers examples

fiat : $(CORE_VOS)

querystructures : $(QUERYSTRUCTURE_VOS)

finitesets : $(FINITESET_VOS)

examples : $(EXAMPLE_VOS)

compiler : $(COMPILER_VOS)

parsers : $(PREFIXED_SRC_PARSERS_VOS)

parsers-base : $(PREFIXED_SRC_PARSERS_BASE_VOS)

pdf: Overview/ProjectOverview.pdf Overview/library.pdf

doc: pdf html

Overview/library.tex: all.pdf
	cp "$<" "$@"

Overview/coqdoc.sty: all.pdf
	cp coqdoc.sty "$@"

Overview/library.pdf: Overview/library.tex Overview/coqdoc.sty
	cd Overview; pdflatex library.tex

Overview/ProjectOverview.pdf: $(shell find Overview -name "*.tex" -o -name "*.sty" -o -name "*.cls" -o -name "*.bib") Overview/library.pdf
	cd Overview; pdflatex -interaction=batchmode -synctex=1 ProjectOverview.tex || true
	cd Overview; bibtex ProjectOverview
	cd Overview; pdflatex -interaction=batchmode -synctex=1 ProjectOverview.tex || true
	cd Overview; pdflatex -synctex=1 ProjectOverview.tex

Makefile.coq: Makefile
	$(VECHO) "COQ_MAKEFILE > $@"
	$(Q)"$(COQBIN)coq_makefile" $(CORE_VS) $(EXAMPLE_VS) $(QUERYSTRUCTURE_VS) $(SRC_PARSERS_VS) $(FINITESET_VS) $(COMPILER_VS) COQC = "\$$(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" -arg -dont-load-proofs -R src ADTSynthesis -R examples ADTExamples | sed s'/^\(-include.*\)$$/ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)\n\1\nelse\nifeq ($$(MAKECMDGOALS),)\n\1\nendif\nendif/g' | sed s'/^clean:$$/clean-old::/g' | sed s'/^Makefile: /Makefile-old: /g' > $@

-include Makefile.coq

# overwrite OCAMLC, OCAMLOPT, OCAMLDEP to make `make` quieter
OCAMLC_OLD := $(OCAMLC)
OCAMLC = $(SILENCE_OCAMLC)$(OCAMLC_OLD)

OCAMLDEP_OLD := $(OCAMLDEP)
OCAMLDEP = $(SILENCE_OCAMLDEP)$(OCAMLDEP_OLD)

OCAMLOPT_OLD := $(OCAMLOPT)
OCAMLOPT = $(SILENCE_OCAMLOPT)$(OCAMLOPT_OLD)

clean::
	$(VECHO) "RM *.CMO *.CMI *.CMA"
	$(Q)rm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)
	$(VECHO) "RM *.CMX *.CMXS *.CMXA *.O *.A"
	$(Q)rm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)
	$(VECHO) "RM *.ML.D *.MLI.D *.ML4.D *.MLLIB.D"
	$(Q)rm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))
	$(VECHO) "RM *.VO *.VI *.G *.V.D *.V.BEAUTIFIED *.V.OLD"
	$(Q)rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	$(VECHO) "RM *.PS *.PDF *.GLOB *.TEX *.G.TEX"
	$(Q)rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml
	rm -f Makefile.coq .depend

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

examples/BookstoreExtraction.vo : examples/BookstoreExtraction.v examples/Bookstore.vo
	coqc -R src ADTSynthesis -R examples ADTExamples examples/BookstoreExtraction.v

examples/BookstoreNaiveExtraction.vo : examples/BookstoreNaiveExtraction.v examples/BookstoreNaive.vo
	coqc -R src ADTSynthesis -R examples ADTExamples examples/BookstoreNaiveExtraction.v

examples/bookstore.cmxa: examples/BookstoreExtraction.vo
	cd examples && ocamlopt -w -a -o bookstore.cmxa -a bookstore.mli bookstore.ml

examples/bookstorenaive.cmxa: examples/BookstoreNaiveExtraction.vo
	cd examples && ocamlopt -w -a -o bookstorenaive.cmxa -a bookstorenaive.mli bookstorenaive.ml

repl: examples/repl.ml examples/bookstore.cmxa
	cd examples && ocamlopt -w -a -o repl unix.cmxa str.cmxa bookstore.cmxa repl.ml

naiverepl: examples/repl.ml examples/bookstorenaive.cmxa
	cd examples && ocamlopt -w -a -o repl unix.cmxa str.cmxa bookstorenaive.cmxa repl.ml

examples/ExtractingFiniteSetsExamples.vo: examples/ExtractingFiniteSetsExamples.v
	$(COQC) -I ../bedrock/platform -dont-load-proofs -R src ADTSynthesis -R examples ADTExamples \
		-R ../bedrock/src Bedrock -R ../bedrock/platform/cito Cito -R ../bedrock/platform/facade Facade \
		examples/ExtractingFiniteSetsExamples

examples/SumUnique.ml examples/SumUniqueAMD64.vo: examples/SumUniqueAMD64.v
	cat examples/ignoreFail.ml >$@
	$(COQC) -I ../bedrock/platform -dont-load-proofs -R src ADTSynthesis -R examples ADTExamples \
		-R ../bedrock/src Bedrock -R ../bedrock/platform/cito Cito -R ../bedrock/platform/facade Facade \
		$< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat examples/printCode.ml >>$@

examples/SumUnique.s: examples/SumUnique.ml
	echo ".global bedrock_heap,export_dffun,sys_abort" >$@
	echo >>$@
	ocaml -w -x $< >>$@

examples/SumUnique.exe: examples/SumUnique.o examples/bedrock_main.o examples/bedrock_driver.o
	cc $^ -o $@

cheat:
	cp examples/SumUnique.pregenerated.ml examples/SumUnique.ml
	cp examples/SumUnique.pregenerated.s examples/SumUnique.s
