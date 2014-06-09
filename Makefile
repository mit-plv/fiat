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
	QueryStructure/QueryStructureNotations \
	QueryStructure/Refinements/GeneralQueryRefinements \
	QueryStructure/Refinements/GeneralInsertRefinements \
	QueryStructure/Refinements/GeneralQueryStructureRefinements \
	QueryStructure/SetEq \
	QueryStructure/SetEqProperties \
	QueryStructure/AdditionalLemmas \
	QueryStructure/Refinements/ListImplementation/ListQueryRefinements \
	QueryStructure/Refinements/ListImplementation/ListInsertRefinements \
	QueryStructure/Refinements/ListImplementation/ListQueryStructureRefinements \
	QueryStructure/Refinements/ListImplementation \
	QueryStructure/Refinements/FMapImplementation/FMapExtensions \
	QueryStructure/Refinements/Bags/BagsInterface\
	QueryStructure/Refinements/Bags/String_as_OT \
	QueryStructure/Refinements/Bags/Bags

EXAMPLE_MODULES := \
	ComputationExamples \
	Trivial \
	Bookstore \
	ProcessScheduler/State \
	ProcessScheduler/DBSchema \
	ProcessScheduler/ListBasedRefinement \
	ProcessScheduler/TreeBasedRefinement

# ADTExamples/QueryStructure/ProcessScheduler/TreeBasedRefinement \
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


EXAMPLE_VS          := $(EXAMPLE_MODULES:%=%.v)
PREFIXED_EXAMPLE_VS := $(EXAMPLE_MODULES:%=examples/%.v)
EXAMPLE_VDS	    := $(EXAMPLE_MODULES:%=examples/%.v.d)

V = 0

SILENCE_COQC_0 := @echo \"COQC $$<\"; #
SILENCE_COQC_1 :=
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 := @echo \"COQDEP $$<\"; #
SILENCE_COQDEP_1 :=
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

COQDOCFLAGS=-interpolate -utf8

TIMED=
TIMECMD=
# we should use %U for compatibility with Coq trunk, but that's broken on Windows cygwin with a non-cygwin-compilied program, it seems.  %M is also broken, but whatever
STDTIME=/usr/bin/time -f \"\$$* (user: %e mem: %M ko)\"
TIMER=\$$(if \$$(TIMED), $(STDTIME), $(TIMECMD))


.PHONY: all sources examples html clean pretty-timed pretty-timed-files pdf doc clean-doc

all: sources examples

sources : src/Makefile.coq
	$(MAKE) -C src/ -f Makefile.coq COQC="$(SILENCE_COQC)$(TIMER) \"$(COQBIN)coqc\"" COQDEP=" $(SILENCE_COQDEP)\"$(COQBIN)coqdep\" -c"

examples : examples/Makefile.coq
	$(MAKE) -C examples/ -f Makefile.coq COQC="$(SILENCE_COQC)$(TIMER) \"$(COQBIN)coqc\"" COQDEP=" $(SILENCE_COQDEP)\"$(COQBIN)coqdep\" -c"

html_sources : Source_Makefile.coq
	$(MAKE) -f Source_Makefile.coq html

html_examples : examples/Makefile.coq
	$(MAKE) -f examples/Makefile.coq html

pdf: Overview/ProjectOverview.pdf Overview/library.pdf

doc: pdf html

all.pdf: Source_Makefile.coq
	$(MAKE) -f Source_Makefile.coq COQDEP="$(COQDEP)" COQDOC="COQDOC='$(COQDOC)' ./coqdoc-latex.sh" all.pdf

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

src/Makefile.coq: Makefile $(PREFIXED_SRC_VS)
	"$(COQBIN)coq_makefile" $(SRC_VS) COQC = " $(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = " $(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" -arg -dont-load-proofs -R . ADTSynthesis.src -o Makefile.coq
	mv Makefile.coq src/Makefile.coq

examples/Makefile.coq: Makefile $(PREFIXED_EXAMPLE_VS)
	"$(COQBIN)coq_makefile" $(EXAMPLE_VS) COQC = " $(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = " $(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" -arg -dont-load-proofs -I src -R ../ ADTSynthesis -o Makefile.coq
	mv Makefile.coq examples/Makefile.coq

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

clean:: src/Makefile.coq examples/Makefile.coq clean-doc
	$(MAKE) -C src/ -f Makefile.coq clean
	$(MAKE) -C examples/ -f Makefile.coq clean
	rm -f Source_Makefile.coq .depend
	rm -f examples/Makefile.coq .depend
