MODULES    := \
	Notations \
	Common \
	LogicLemmas \
	Computation/Core \
	Computation/Monad \
	Computation/ReflectiveMonad \
	Computation/ApplyMonad \
	Computation/Refinements/Tactics \
	Computation/SetoidMorphisms \
	Computation/Refinements/General \
	Computation/Refinements/Inline \
	Computation \
	ADT/ADTSig \
	ADT/Core \
	ADT/ADTHide \
	ADT \
	ADTNotation/StringBound \
	ADTNotation/BuildADTSig \
	ADTNotation/ilist \
	ADTNotation/BuildADT \
	ADTNotation/BuildADTReplaceMethods \
	ADTNotation \
	ADTRefinement/Core \
	ADTRefinement/SetoidMorphisms \
	ADTRefinement/BuildADTSetoidMorphisms \
	ADTRefinement/GeneralRefinements \
	ADTRefinement/GeneralBuildADTRefinements \
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
	ADTRefinement \
	ComputationExamples \
	ADTExamples/QueryStructure/Notations \
	ADTExamples/QueryStructure/Heading \
	ADTExamples/QueryStructure/Tuple \
	ADTExamples/QueryStructure/Schema \
	ADTExamples/QueryStructure/Relation \
	ADTExamples/QueryStructure/QueryStructureSchema \
	ADTExamples/QueryStructure/QueryStructure \
	ADTExamples/QueryStructure/EmptyQSSpecs \
	ADTExamples/QueryStructure/QueryQSSpecs \
	ADTExamples/QueryStructure/InsertQSSpecs \
	ADTExamples/QueryStructure/GeneralQueryRefinements \
	ADTExamples/QueryStructure/GeneralInsertRefinements \
	ADTExamples/QueryStructure/GeneralQueryStructureRefinements \
	ADTExamples/QueryStructure/ProcessScheduler/State \
	ADTExamples/QueryStructure/ProcessScheduler/SetEq \
	ADTExamples/QueryStructure/ProcessScheduler/AdditionalLemmas \
	ADTExamples/QueryStructure/ListQueryRefinements \
	ADTExamples/QueryStructure/ListInsertRefinements \
	ADTExamples/QueryStructure/ListQueryStructureRefinements \
	ADTExamples/QueryStructure/QueryStructureNotations \
	ADTExamples/QueryStructure/Bookstore \
	ADTExamples/QueryStructure/ProcessScheduler/FMapExtensions \
	ADTExamples/QueryStructure/ProcessScheduler/DBSchema \
	ADTExamples/QueryStructure/ProcessScheduler/ListBasedRefinement

# ADTExamples/QueryStructure/ProcessScheduler/TreeBasedRefinement \
# ADTExamples/CombineBinaryOperationsSpec
# ADTExamples/BinaryOperationSpec
# ADTExamples/BinaryOperationImpl
# ADTExamples/BinaryOperationRefinements
# ADTExamples/MinCollection
# ADTExamples/MinPlusMax

COQDEP=coqdep
COQDOC=coqdoc

VS         := $(MODULES:%=%.v)
VDS	   := $(MODULES:%=%.v.d)

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


.PHONY: all html clean pretty-timed pretty-timed-files pdf doc clean-doc

all: Makefile.coq
	$(MAKE) -f Makefile.coq COQC="$(SILENCE_COQC)$(TIMER) \"$(COQBIN)coqc\"" COQDEP=" $(SILENCE_COQDEP)\"$(COQBIN)coqdep\" -c"

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

pdf: Overview/ProjectOverview.pdf Overview/library.pdf

doc: pdf html

all.pdf: Makefile.coq
	$(MAKE) -f Makefile.coq COQDEP="$(COQDEP)" COQDOC="COQDOC='$(COQDOC)' ./coqdoc-latex.sh" all.pdf

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

Makefile.coq: Makefile $(VS)
	"$(COQBIN)coq_makefile" $(VS) COQC = " $(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = " $(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" -arg -dont-load-proofs -R . ADTSynthesis -o Makefile.coq

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

clean:: Makefile.coq clean-doc
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
