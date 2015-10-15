COMPATIBILITY_FILE=src/Common/Coq__8_4__8_5__Compat.v
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"

.PHONY: fiat fiat-core querystructures parsers parsers-all finitesets dns compiler facade-test ics fiat4monitors examples \
	fiat-quick fiat-core-quick querystructures-quick parsers-quick parsers-all-quick finitesets-quick dns-quick compiler-quick facade-test-quick ics-quick fiat4monitors-quick examples-quick \
	install install-fiat install-fiat-core install-querystructures install-parsers install-finitesets install-dns install-compiler install-ics install-fiat4monitors install-examples \
	pdf doc clean-doc

submodule-update: .gitmodules
	git submodule sync && \
	git submodule update --init && \
	touch "$@"

ifneq (,$(wildcard .git)) # if we're in a git repo
etc/coq-scripts/Makefile.coq.common etc/coq-scripts/compatibility/Makefile.coq.compat_84_85 etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early: submodule-update
	@ touch "$@"
endif

FAST_TARGETS += clean-doc etc/coq-scripts etc/coq-scripts/Makefile.coq.common etc/coq-scripts/compatibility/Makefile.coq.compat_84_85 etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early submodule-update
SUPER_FAST_TARGETS += submodule-update

Makefile.coq: etc/coq-scripts/Makefile.coq.common etc/coq-scripts/compatibility/Makefile.coq.compat_84_85 etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early

include etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early

include etc/coq-scripts/Makefile.coq.common

include etc/coq-scripts/compatibility/Makefile.coq.compat_84_85

.DEFAULT_GOAL := fiat

clean::
	rm -f src/Examples/Ics/WaterTank.ml
	rm -f submodule-update

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

CORE_UNMADE_VO := \
	src/Common/ilist2.vo \
	src/Common/i2list.vo \
	src/Common/ilist2_pair.vo

QUERYSTRUCTURES_UNMADE_VO := \
	src/QueryStructure/Implementation/DataStructures/Bags/InvertedIndexBags.vo

PARSERS_UNMADE_VO :=

FIAT4MONITORS_UNMADE_VO := \
	src/Fiat4Monitors/HelloWorld/%.vo \
	src/Fiat4Monitors/HealthMonitor/%.vo \
	src/Fiat4Monitors/TurretMonitorSpec.vo \
	src/Fiat4Monitors/MonitorRepInv.vo

EXAMPLES_UNMADE_VO := \
	src/Examples/Smtp/Smtp.vo \
	src/Examples/CacheADT/TrivialADTCache.vo \
	src/Examples/CacheADT/LRUCache.vo \
	src/Examples/CacheADT/KVEnsembles.vo \
	src/Examples/CacheADT/FMapCacheImplementation.vo \
	src/Examples/CacheADT/CacheSpec.vo \
	src/Examples/CacheADT/CacheSig.vo \
	src/Examples/CacheADT/CacheRefinements.vo \
	src/Examples/CacheADT/CacheADT.vo \
	src/Examples/QueryStructure/FriendFinder.vo \
	src/Examples/QueryStructure/Github.vo \
	src/Examples/QueryStructure/Photoalbum.vo \
	src/Examples/QueryStructure/PhotoalbumExtraction.vo \
	src/Examples/QueryStructure/PhotoalbumUnOpt.vo \
	src/Examples/QueryStructure/PhotoalbumUnOptimizedExtraction.vo \
	src/Examples/QueryStructure/CodeLookup.vo \
	src/Examples/QueryStructure/SearchTest.vo \
	src/Examples/SearchTest.vo \
	src/Examples/Ics/WaterTankExtract.vo



WATER_TANK_EXTRACT_VO := src/Examples/Ics/WaterTankExtract.vo
WATER_TANK_EXTRACT_ML := src/Examples/Ics/WaterTank.ml

FIAT_CORE_VO := $(filter-out $(CORE_UNMADE_VO),$(filter src/Computation.vo src/ADT.vo src/ADTNotation.vo src/ADTRefinement.vo src/Common.vo src/Computation/%.vo src/ADT/%.vo src/ADTNotation/%.vo src/ADTRefinement/%.vo src/Common/%.vo,$(VOFILES)))
QUERYSTRUCTURES_VO := $(filter-out $(QUERYSTRUCTURES_UNMADE_VO),$(filter src/QueryStructure/%.vo,$(VOFILES)))
PARSERS_VO := $(filter-out $(PARSERS_UNMADE_VO),$(filter src/Parsers/%.vo,$(VOFILES)))
PARSERS_ALL_VO := $(filter src/Parsers/%.vo,$(VOFILES))
FINITESET_VO := $(filter src/FiniteSetADTs.vo src/FiniteSetADTs/%.vo,$(VOFILES))
DNS_VO := $(filter src/Examples/DnsServer/%.vo,$(VOFILES))
COMPILER_VO := $(filter src/FiatToFacade/%.vo,$(VOFILES))
FACADE_TEST_VO := src/Examples/FacadeTest.vo
ICS_VO := $(filter-out $(WATER_TANK_EXTRACT_VO),$(filter src/Examples/Ics/%.vo,$(VOFILES)))
FIAT4MONITORS_VO := $(filter-out $(FIAT4MONITORS_UNMADE_VO), $(filter src/Fiat4Monitors/%.vo,$(VOFILES)))
EXAMPLES_VO := $(filter-out $(EXAMPLES_UNMADE_VO) $(ICS_VO) $(DNS_VO) $(FACADE_TEST_VO),$(filter src/Examples/%.vo,$(VOFILES)))

FIAT_VO := $(FIAT_CORE_VO) $(QUERYSTRUCTURES_VO) $(PARSERS_VO)

fiat: $(FIAT_VO)
fiat-core: $(FIAT_CORE_VO)
querystructures: $(QUERYSTRUCTURES_VO)
parsers: $(PARSERS_VO)
parsers-all: $(PARSERS_ALL_VO)
finitesets: $(FINITESETS_VO)
dns: $(DNS_VO)
compiler: $(COMPILER_VO)
facade-test: $(FACADE_TEST_VO)
ics: $(ICS_VO)
fiat4monitors: $(FIAT4MONITORS_VO)
examples:  $(EXAMPLES_VO)

fiat-quick: $(addsuffix .vio,$(basename $(FIAT_VO)))
fiat-core-quick: $(addsuffix .vio,$(basename $(FIAT_CORE_VO)))
querystructures-quick: $(addsuffix .vio,$(basename $(QUERYSTRUCTURES_VO)))
parsers-quick: $(addsuffix .vio,$(basename $(PARSERS_VO)))
parsers-all-quick: $(addsuffix .vio,$(basename $(PARSERS_ALL_VO)))
finitesets-quick: $(addsuffix .vio,$(basename $(FINITESETS_VO)))
dns-quick: $(addsuffix .vio,$(basename $(DNS_VO)))
compiler-quick: $(addsuffix .vio,$(basename $(COMPILER_VO)))
facade-test-quick: $(addsuffix .vio,$(basename $(FACADE_TEST_VO)))
ics-quick: $(addsuffix .vio,$(basename $(ICS_VO)))
fiat4monitors-quick: $(addsuffix .vio,$(basename $(FIAT4MONITORS_VO)))
examples-quick: $(addsuffix .vio,$(basename $(EXAMPLES_VO)))

install-fiat: T = $(FIAT_VO)
install-fiat-core: T = $(FIAT_CORE_VO)
install-querystructures: T = $(QUERYSTRUCTURES_VO)
install-parsers: T = $(PARSERS_VO)
install-finitesets: T = $(FINITESETS_VO)
install-dns: T = $(DNS_VO)
install-compiler: T = $(COMPILER_VO)
install-ics: T = $(ICS_VO)
install-fiat4monitors: T = $(FIAT4MONITORS_VO)
install-examples: T = $(EXAMPLES_VO)

install-fiat install-fiat-core install-querystructures install-parsers install-finitesets install-dns install-compiler install-fiat4monitors install-examples:
	$(VECHO) "MAKE -f Makefile.coq INSTALL"
	$(Q)$(MAKE) -f Makefile.coq VFILES="$(call vo_to_installv,$(T))" install

$(UPDATE_COQPROJECT_TARGET):
	(echo '-R src Fiat'; echo '-arg -dont-load-proofs'; find src -name "*.v" -a ! -wholename '$(COMPATIBILITY_FILE)' | $(SORT_COQPROJECT); echo '$(COMPATIBILITY_FILE)') > _CoqProject.in

$(WATER_TANK_EXTRACT_ML): $(filter-out $(WATER_TANK_EXTRACT_VO),$(call vo_closure,$(WATER_TANK_EXTRACT_VO))) $(WATER_TANK_EXTRACT_VO:%.vo=%.v)
	$(VECHO) "COQC $(WATER_TANK_EXTRACT_VO:%.vo=%.v) > $@"
	$(Q)$(COQC) $(COQDEBUG) $(COQFLAGS) $(WATER_TANK_EXTRACT_VO:%.vo=%.v) > $@

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


src/Examples/QueryStructure/classifier.cmxa: src/Examples/QueryStructure/ClassifierExtraction.vo
	cd src/Examples/QueryStructure && ocamlopt -w -a -o classifier.cmxa -a classifier.mli classifier.ml

classifier_repl: src/Examples/QueryStructure/classifier_repl.ml src/Examples/QueryStructure/classifier.cmxa
	cd src/Examples/QueryStructure && ocamlopt -w -a -o classifier_repl unix.cmxa str.cmxa classifier.cmxa classifier_repl.ml

src/Examples/QueryStructure/classifier_unopt.cmxa: src/Examples/QueryStructure/ClassifierUnOptExtraction.vo
	cd src/Examples/QueryStructure && ocamlopt -w -a -o classifier_unopt.cmxa -a classifier_unopt.mli classifier_unopt.ml

classifierUnOpt_repl: src/Examples/QueryStructure/classifierUnOpt_repl.ml src/Examples/QueryStructure/classifier_unopt.cmxa
	cd src/Examples/QueryStructure && ocamlopt -w -a -o classifierUnOpt_repl unix.cmxa str.cmxa classifier_unopt.cmxa classifierUnOpt_repl.ml
