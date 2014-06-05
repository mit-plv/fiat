MODULES    := \
	src/Notations \
	src/Common \
	src/Computation/Core \
	src/Computation/Monad \
	src/Computation/ReflectiveMonad \
	src/Computation/ApplyMonad \
	src/Computation/Refinements/Tactics \
	src/Computation/SetoidMorphisms \
	src/Computation/Refinements/General \
	src/Computation/Refinements/Inline \
	src/Computation \
	src/ADT/ADTSig \
	src/ADT/Core \
	src/ADT/ADTHide \
	src/ADT \
	src/ADTNotation/StringBound \
	src/ADTNotation/BuildADTSig \
	src/ADTNotation/ilist \
	src/ADTNotation/BuildADT \
	src/ADTNotation/BuildADTReplaceMethods \
	src/ADTRefinement/Core \
	src/ADTRefinement/SetoidMorphisms \
	src/ADTRefinement/BuildADTSetoidMorphisms \
	src/ADTRefinement/GeneralRefinements \
	src/ADTRefinement/GeneralBuildADTRefinements \
	src/ADTRefinement/Refinements/DelegateMethods \
	src/ADTRefinement/Refinements/HoneRepresentation \
	src/ADTRefinement/Refinements/SimplifyRep \
	src/ADTRefinement/Refinements/ADTRepInv \
	src/ADTRefinement/Refinements/ADTCache \
	src/ADTRefinement/Refinements/RefineHideADT \
	src/ADTRefinement/Refinements \
	src/ADTRefinement/BuildADTRefinements/HoneRepresentation \
	src/ADTRefinement/BuildADTRefinements/SimplifyRep \
	src/ADTRefinement/BuildADTRefinements \
	src/QueryStructure/Notations \
	src/QueryStructure/Heading \
	src/QueryStructure/Tuple \
	src/QueryStructure/Schema \
	src/QueryStructure/Relation \
	src/QueryStructure/QueryStructureSchema \
	src/QueryStructure/QueryStructure \
	src/QueryStructure/EmptyQSSpecs \
	src/QueryStructure/QueryQSSpecs \
	src/QueryStructure/InsertQSSpecs \
	src/QueryStructure/GeneralQueryRefinements \
	src/QueryStructure/GeneralInsertRefinements \
	src/QueryStructure/GeneralQueryStructureRefinements \
	src/QueryStructure/ListQueryRefinements \
	src/QueryStructure/ListInsertRefinements \
	src/QueryStructure/ListQueryStructureRefinements \
	src/QueryStructure/QueryStructureNotations \
	src/QueryStructure/ProcessScheduler/FMapExtensions \
	examples/ComputationExamples \
	examples/Trivial \
	examples/Bookstore \
	examples/ProcessScheduler/State \
	examples/ProcessScheduler/SetEq \
	examples/ProcessScheduler/AdditionalLemmas \
	examples/ProcessScheduler/DBSchema \
	examples/ProcessScheduler/ListBasedRefinement

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
