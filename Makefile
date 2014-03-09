MODULES    := \
	Notations \
	Common \
	Computation/Core \
	Computation/Monad \
	Computation/SetoidMorphisms \
	Computation/Refinements/General \
	Computation/Refinements/Inline \
	Computation \
	ADT \
	ADTRefinement/Specs \
	ADTRefinement/Pick \
	ADTRefinement/Core \
	ADTRefinement/SetoidMorphisms \
	ADTRefinement/GeneralRefinements \
	ADTRefinement \
	ADTRepInv \
	ADTCache \
	ComputationExamples \
	ADTExamples/BinaryOperationSpec \
	ADTExamples/CombineBinaryOperationsSpec \
	ADTExamples

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


.PHONY: all html clean pretty-timed pretty-timed-files

all: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

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

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
