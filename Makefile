SRC_MODULES    := \
	Common \
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
	ADTNotation/ilist \
	ADTNotation/StringBound \
	ADTNotation/BuildADTSig \
	ADTNotation/BuildADT \
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
	ADTRefinement/BuildADTRefinements \
	QueryStructure/Notations \
	QueryStructure/Heading \
	QueryStructure/Tuple \
	QueryStructure/Schema \
	QueryStructure/Relation \
	QueryStructure/QueryStructureSchema \
	QueryStructure/QueryStructure \
	QueryStructure/QuerySpecs/EmptyQSSpecs \
	QueryStructure/QuerySpecs/QueryQSSpecs \
	QueryStructure/QuerySpecs/InsertQSSpecs \
	QueryStructure/QuerySpecs/EnsembleListEquivalence \
	QueryStructure/QueryStructureNotations \
	QueryStructure/Refinements/GeneralQueryRefinements \
	QueryStructure/Refinements/GeneralInsertRefinements \
	QueryStructure/Refinements/GeneralQueryStructureRefinements \
	QueryStructure/SetEq \
	QueryStructure/SetEqProperties \
	QueryStructure/AdditionalLemmas \
	QueryStructure/tupleAgree \
	QueryStructure/Refinements/AdditionalRefinementLemmas \
	QueryStructure/Refinements/AdditionalPermutationLemmas \
	QueryStructure/Refinements/EnsembleListEquivalenceProperties \
	QueryStructure/Refinements/AdditionalMorphisms \
	QueryStructure/Refinements/flattenCompListProperties \
	QueryStructure/Refinements/ConstraintChecksRefinements \
	QueryStructure/Refinements/ListImplementation/ListQueryRefinements \
	QueryStructure/Refinements/ListImplementation/ListInsertRefinements \
	QueryStructure/Refinements/ListImplementation/ListQueryStructureRefinements \
	QueryStructure/Refinements/ListImplementation \
	QueryStructure/Refinements/FMapImplementation/FMapExtensions \
	QueryStructure/Refinements/Bags/BagsInterface\
	QueryStructure/Refinements/Bags/BagsProperties\
	QueryStructure/Refinements/Bags/BagsTactics\
	QueryStructure/Refinements/Bags/ListBags\
	QueryStructure/Refinements/Bags/CountingListBags\
	QueryStructure/Refinements/Bags/TreeBags\
	QueryStructure/Refinements/Bags/CachingBags\
	QueryStructure/Refinements/Bags/CacheableFunctions\
	QueryStructure/Refinements/Bags/BagsOfTuples\
	QueryStructure/Refinements/Bags/String_as_OT \
	QueryStructure/Refinements/Bags/Bags

EXAMPLE_MODULES := \
	AutoDB \
	ComputationExamples \
	Trivial \
	TrivialCache \
	ProcessScheduler/DBSchema \
	ProcessScheduler/TreeBasedRefinement \
	Bookstore \
	BookstoreSemiAutomatic \
	BookstoreNaive \
	Weather \
	Stocks
#	CacheADT \

# ADTExamples/CombineBinaryOperationsSpec
# ADTExamples/BinaryOperationSpec
# ADTExamples/BinaryOperationImpl
# ADTExamples/BinaryOperationRefinements
# ADTExamples/MinCollection
# ADTExamples/MinPlusMax

COQDEP=coqdep
COQDOC=coqdoc

SRC_VS         	:= $(SRC_MODULES:%=%.v)
PREFIXED_SRC_VS	:= $(SRC_MODULES:%=src/%.v)
SRC_VDS	   	:= $(SRC_MODULES:%=src/%.v.d)
PREFIXED_SRC_VOS:= $(SRC_MODULES:%=src/%.vo)


EXAMPLE_VS          := $(EXAMPLE_MODULES:%=%.v)
PREFIXED_EXAMPLE_VS := $(EXAMPLE_MODULES:%=examples/%.v)
EXAMPLE_VDS	    := $(EXAMPLE_MODULES:%=examples/%.v.d)
PREFIXED_EXAMPLE_VOS:= $(EXAMPLE_MODULES:%=examples/%.vo)

V = 0

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

COQDOCFLAGS=-interpolate -utf8

TIMED=
TIMECMD=
# we should use %U for compatibility with Coq trunk, but that's broken on Windows cygwin with a non-cygwin-compilied program, it seems.  %M is also broken, but whatever
STDTIME=/usr/bin/time -f \"\$$* (user: %e mem: %M ko)\"
TIMER=\$$(if \$$(TIMED), $(STDTIME), $(TIMECMD))


.PHONY: all sources examples html clean pretty-timed pretty-timed-files pdf doc clean-doc

sources : $(PREFIXED_SRC_VOS)

examples : $(PREFIXED_EXAMPLE_VOS)

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
	"$(COQBIN)coq_makefile" $(PREFIXED_SRC_VS) $(PREFIXED_EXAMPLE_VS) COQC = " \$$(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = " \$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" -arg -dont-load-proofs -R src ADTSynthesis -R examples ADTExamples -o Makefile.coq

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

-include Makefile.coq

examples/BookstoreExtraction.vo : examples/BookstoreExtraction.v examples/Bookstore.vo
	coqc -R src ADTSynthesis -R examples ADTExamples examples/BookstoreExtraction.v

examples/BookstoreNaiveExtraction.vo : examples/BookstoreNaiveExtraction.v examples/BookstoreNaive.vo
	coqc -R src ADTSynthesis -R examples ADTExamples examples/BookstoreNaiveExtraction.v

examples/bookstore.cmxa: examples/BookstoreExtraction.vo
	cd examples && ocamlopt -o bookstore.cmxa -a bookstore.mli bookstore.ml

examples/bookstorenaive.cmxa: examples/BookstoreNaiveExtraction.vo
	cd examples && ocamlopt -o bookstorenaive.cmxa -a bookstorenaive.mli bookstorenaive.ml

repl: examples/repl.ml examples/bookstore.cmxa
	cd examples && ocamlopt -o repl unix.cmxa str.cmxa bookstore.cmxa repl.ml

naiverepl: examples/repl.ml examples/bookstorenaive.cmxa
	cd examples && ocamlopt -o repl unix.cmxa str.cmxa bookstorenaive.cmxa repl.ml

# uncomment this to get a clean target that cleans the documentation, at the cost of emitting
# Makefile:156: warning: overriding recipe for target 'clean'
# Makefile.coq:247: warning: ignoring old recipe for target 'clean'
#clean: clean-doc Makefile.coq
#	$(MAKE) -f Makefile.coq clean
#	rm -f Makefile.coq
