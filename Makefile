MODULES    := \
	Notations \
	Common \
	LogicLemmas \
	Computation/Core \
	Computation/Monad \
	Computation/Refinements/Tactics \
	Computation/SetoidMorphisms \
	Computation/Refinements/General \
	Computation/Refinements/Inline \
	Computation \
	ADT/ADTSig \
	ADT/Core \
	ADT/ADTHide \
	ADT/Specs \
	ADT/Pick \
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
	ADTRefinement/Refinements/HonePickRepresentation \
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
	ADTExamples/CombineBinaryOperationsSpec \
	ADTExamples/BinaryOperationSpec \
	ADTExamples/BinaryOperationImpl \
	ADTExamples/BinaryOperationRefinements \
	ADTExamples/MinCollection \
	ADTExamples/MinPlusMax \
	ADTExamples/QueryStructure/Notations \
	ADTExamples/QueryStructure/Heading \
	ADTExamples/QueryStructure/Tuple \
	ADTExamples/QueryStructure/Schema \
	ADTExamples/QueryStructure/Relation \
	ADTExamples/QueryStructure/QueryStructureSchema \
	ADTExamples/QueryStructure/QuerySpecs \
	ADTExamples/QueryStructure/Bookstore

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

#NEW_TIME_FILE=time-of-build-after.log
#OLD_TIME_FILE=time-of-build-before.log
#BOTH_TIME_FILE=time-of-build-both.log
#NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
#SINGLE_TIME_FILE=time-of-build.log
#SINGLE_PRETTY_TIME_FILE=time-of-build-pretty.log
#TIME_SHELF_NAME=time-of-build-shelf
COQDOCFLAGS=-interpolate -utf8


.PHONY: all html clean pretty-timed pretty-timed-files pdf doc clean-doc

all: Makefile.coq
	$(MAKE) -f Makefile.coq

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

#pretty-timed-diff:
#	bash ./etc/make-each-time-file.sh "$(MAKE)" "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)"
#	$(MAKE) combine-pretty-timed
#
#combine-pretty-timed:
#	python ./etc/make-both-time-files.py "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)" "$(BOTH_TIME_FILE)"
#	cat "$(BOTH_TIME_FILE)"
#	@echo
#
#pretty-timed:
#	bash ./etc/make-each-time-file.sh "$(MAKE) SEMICOLON=;" "$(SINGLE_TIME_FILE)"
#	python ./etc/make-one-time-file.py "$(SINGLE_TIME_FILE)" "$(SINGLE_PRETTY_TIME_FILE)"
#	cat "$(SINGLE_PRETTY_TIME_FILE)"
#	@echo

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) COQC = " $(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = " $(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" COQDOCFLAGS = "$(COQDOCFLAGS)" -arg -dont-load-proofs -R . ADTSynthesis -o Makefile.coq

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc"

clean:: Makefile.coq clean-doc
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
