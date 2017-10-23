COMPATIBILITY_FILE=src/Common/Coq__8_4__8_5__Compat.v
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"

.PHONY: fiat fiat-core querystructures parsers parsers-examples parsers-examples-verbose parsers-all finitesets dns compiler facade-test ics fiat4monitors examples binencoders \
	fiat-quick fiat-core-quick querystructures-quick parsers-quick parsers-examples-quick parsers-examples-verbose-quick parsers-all-quick finitesets-quick dns-quick compiler-quick facade-test-quick ics-quick fiat4monitors-quick examples-quick binencoders-quick \
	install install-fiat install-fiat-core install-querystructures install-parsers install-parsers-examples install-parsers-examples-verbose install-parsers-all install-finitesets install-dns install-compiler install-ics install-fiat4monitors install-examples install-binencoders \
	pdf doc clean-doc \
	test-parsers test-parsers-profile test-parsers-profile-graph

ifneq (,$(wildcard .git)) # if we're in a git repo

# if the submodule changed, update it
SUBMODULE_DIFF=$(shell git diff etc/coq-scripts 2>&1 | grep 'Subproject commit')
SUBMODULE_DIRTY=$(shell git diff etc/coq-scripts 2>&1 | grep dirty)
ifneq (,$(SUBMODULE_DIRTY))
submodule-update::
	@ echo "\033[0;31mThe submodule is dirty; some scripts may fail.\033[0m"
	@ echo "\033[0;31mRun (cd etc/coq-scripts && git clean -xfd && git reset --hard)\033[0m"
else
ifneq (,$(SUBMODULE_DIFF))
submodule-update::
	git submodule sync && \
	git submodule update --init && \
	touch "$@"
endif
endif

ifeq (,$(wildcard submodule-update))
submodule-update::
	git submodule sync && \
	git submodule update --init && \
	touch "$@"
else
submodule-update::
endif

etc/coq-scripts/Makefile.coq.common etc/coq-scripts/compatibility/Makefile.coq.compat_84_85 etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early: submodule-update
	@ touch "$@"
endif

FAST_TARGETS += clean-doc etc/coq-scripts etc/coq-scripts/Makefile.coq.common etc/coq-scripts/compatibility/Makefile.coq.compat_84_85 etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early submodule-update
SUPER_FAST_TARGETS += submodule-update

Makefile.coq: etc/coq-scripts/Makefile.coq.common etc/coq-scripts/compatibility/Makefile.coq.compat_84_85 etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early

STRICT_COQDEP ?= 1

ML_COMPATIBILITY_FILES = src/Common/Tactics/hint_db_extra_tactics.ml src/Common/Tactics/hint_db_extra_plugin.ml4 src/Common/Tactics/transparent_abstract_plugin.ml4 src/Common/Tactics/transparent_abstract_tactics.ml

-include etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early

-include etc/coq-scripts/Makefile.coq.common

-include etc/coq-scripts/compatibility/Makefile.coq.compat_84_85

ifeq ($(filter printdeps printreversedeps,$(MAKECMDGOALS)),)
-include etc/coq-scripts/Makefile.vo_closure
else
include etc/coq-scripts/Makefile.vo_closure
endif

.DEFAULT_GOAL := fiat

clean::
	rm -f src/Examples/Ics/WaterTank.ml
	rm -f submodule-update

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

HASNATDYNLINK = true

test-parsers: src/Parsers/Refinement/ExtractSharpenedABStar.vo
	$(MAKE) -C src/Parsers/Refinement/Testing

test-parsers-profile: src/Parsers/Refinement/ExtractSharpenedABStar.vo
	$(MAKE) -C src/Parsers/Refinement/Testing test-ab-star-profile

test-parsers-profile-graph: src/Parsers/Refinement/ExtractSharpenedABStar.vo
	$(MAKE) -C src/Parsers/Refinement/Testing test-ab-star-profile-graph

CORE_UNMADE_VO := \
	src/Common/ilist2.vo \
	src/Common/i2list.vo \
	src/Common/ilist2_pair.vo \
	src/Common/FMapExtensions/LiftRelationInstances.vo \
	src/Common/FMapExtensions/Wf.vo

QUERYSTRUCTURES_UNMADE_VO := \
	src/QueryStructure/Implementation/DataStructures/Bags/IndexedBags.vo \
	src/QueryStructure/Implementation/DataStructures/Bags/ProductBags.vo \
	src/QueryStructure/Implementation/DataStructures/Bags/InvertedIndexBags.vo

PARSERS_EXAMPLES_VERBOSE_UNMADE_VO := \
	src/Parsers/Refinement/SharpenedJavaScriptAssignmentExpression.vo

PARSERS_EXAMPLES_UNMADE_VO := \
	src/Parsers/Refinement/ExtractSharpenedJSComment.vo \
	src/Parsers/Refinement/ExtractSharpenedJSON.vo \
	$(PARSERS_EXAMPLES_VERBOSE_UNMADE_VO)

PARSERS_UNMADE_VO := \
	src/Parsers/Grammars/SimpleRecognizerOptimized.vo \
	src/Parsers/Refinement/SharpenedJSON.vo \
	$(PARSERS_EXAMPLES_UNMADE_VO)

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
	src/Examples/QueryStructure/IncompleteROSMaster.vo \
	src/Examples/QueryStructure/Photoalbum.vo \
	src/Examples/QueryStructure/PhotoalbumExtraction.vo \
	src/Examples/QueryStructure/PhotoalbumUnOpt.vo \
	src/Examples/QueryStructure/PhotoalbumUnOptimizedExtraction.vo \
	src/Examples/QueryStructure/ProcessScheduler.vo \
	src/Examples/QueryStructure/DelegatedProcessScheduler.vo \
	src/Examples/QueryStructure/CodeLookup.vo \
	src/Examples/QueryStructure/SearchTest.vo \
	src/Examples/SearchTest.vo \
	src/Examples/Ics/WaterTankExtract.vo \
	src/Examples/HACMSDemo/WheelSensor.vo \
	src/Examples/HACMSDemo/WheelSensorEncoder.vo \
	src/Examples/HACMSDemo/WheelSensorDecoder.vo \
	src/Examples/HACMSDemo/WheelSensorExtraction.vo

EXTRACTION_UNMADE_VO := \
	src/CertifiedExtraction/Benchmarks/DNS.vo \

BINENCODERS_UNMADE_VO := \
	src/BinEncoders/Env/Examples/EthernetFrame.vo \
	src/BinEncoders/Env/Examples/Dns.vo \
	src/BinEncoders/Env/Examples/DnsMap.vo \
	src/BinEncoders/Env/Examples/Toy.vo \
	src/BinEncoders/Env/Examples/Toy2.vo

WATER_TANK_EXTRACT_VO := src/Examples/Ics/WaterTankExtract.vo
WATER_TANK_EXTRACT_ML := src/Examples/Ics/WaterTank.ml

FIAT_CORE_VO := $(filter-out $(CORE_UNMADE_VO),$(filter src/Computation.vo src/ADT.vo src/ADTInduction.vo src/ADTNotation.vo src/ADTRefinement.vo src/Common.vo src/Computation/%.vo src/ADT/%.vo src/ADTNotation/%.vo src/ADTRefinement/%.vo src/Common/%.vo,$(VOFILES)))
QUERYSTRUCTURES_VO := $(filter-out $(QUERYSTRUCTURES_UNMADE_VO),$(filter src/QueryStructure/%.vo,$(VOFILES)))
PARSERS_VO := $(filter-out $(PARSERS_UNMADE_VO),$(filter src/Parsers/%.vo,$(VOFILES)))
PARSERS_EXAMPLES_VO := $(filter-out $(PARSERS_EXAMPLES_UNMADE_VO),$(filter src/Parsers/Refinement/Sharpened%.vo,$(VOFILES)))
PARSERS_EXAMPLES_VERBOSE_VO := $(filter-out $(PARSERS_EXAMPLES_VERBOSE_UNMADE_VO),$(filter src/Parsers/Refinement/ExtractSharpened%.vo,$(VOFILES)))
PARSERS_ALL_VO := $(filter src/Parsers/%.vo,$(VOFILES))
FINITESET_VO := $(filter src/FiniteSetADTs.vo src/FiniteSetADTs/%.vo,$(VOFILES))
DNS_VO := $(filter src/Examples/DnsServer/%.vo,$(VOFILES))
EXTRACTION_VO := $(filter-out $(EXTRACTION_UNMADE_VO),$(filter src/CertifiedExtraction/%.vo,$(VOFILES))) src/Examples/QueryStructure/ProcessScheduler.vo
FACADE_TEST_VO := src/Examples/FacadeTest.vo
ICS_VO := $(filter-out $(WATER_TANK_EXTRACT_VO),$(filter src/Examples/Ics/%.vo,$(VOFILES)))
TUTORIAL_VO := src/Examples/Tutorial/Tutorial.vo src/Examples/Tutorial/NotInList.vo src/Examples/Tutorial/Queue.vo src/Examples/Tutorial/BookstoreMoreManual.vo
HACMSDEMO_VO := src/Examples/HACMSDemo/DuplicateFree.vo src/Examples/HACMSDemo/HACMSDemo.vo src/Examples/HACMSDemo/WheelSensor.vo src/Examples/HACMSDemo/WheelSensorEncoder.vo src/Examples/HACMSDemo/WheelSensorDecoder.vo src/Examples/HACMSDemo/WheelSensorExtraction.vo
FIAT4MONITORS_VO := $(filter-out $(FIAT4MONITORS_UNMADE_VO), $(filter src/Fiat4Monitors/%.vo,$(VOFILES)))
EXAMPLES_VO := $(filter-out $(EXAMPLES_UNMADE_VO) $(ICS_VO) $(TUTORIAL_VO) $(DNS_VO) $(FACADE_TEST_VO),$(filter src/Examples/%.vo,$(VOFILES)))
BINENCODERS_VO := $(filter-out $(BINENCODERS_UNMADE_VO), $(filter src/BinEncoders/%.vo,$(VOFILES)))
FIAT_VO := $(FIAT_CORE_VO) $(QUERYSTRUCTURES_VO) $(PARSERS_VO)
TACTICS_TARGETS := $(filter src/Common/Tactics/%,$(CMOFILES) $(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES)))

fiat: $(FIAT_VO) $(TACTICS_TARGETS)
fiat-core: $(FIAT_CORE_VO) $(TACTICS_TARGETS)
querystructures: $(QUERYSTRUCTURES_VO)
parsers: $(PARSERS_VO)
parsers-examples: $(PARSERS_EXAMPLES_VO)
parsers-examples-verbose: $(PARSERS_EXAMPLES_VERBOSE_VO)
parsers-all: $(PARSERS_ALL_VO)
finitesets: $(FINITESETS_VO)
dns: $(DNS_VO)
extraction: $(EXTRACTION_VO)
facade-test: $(FACADE_TEST_VO)
ics: $(ICS_VO)
tutorial: $(TUTORIAL_VO)
hacms-demo: $(HACMSDEMO_VO)
fiat4monitors: $(FIAT4MONITORS_VO)
examples: $(EXAMPLES_VO)
binencoders: $(BINENCODERS_VO)

fiat-quick: $(addsuffix .vio,$(basename $(FIAT_VO))) $(TACTICS_TARGETS)
fiat-core-quick: $(addsuffix .vio,$(basename $(FIAT_CORE_VO))) $(TACTICS_TARGETS)
querystructures-quick: $(addsuffix .vio,$(basename $(QUERYSTRUCTURES_VO)))
parsers-quick: $(addsuffix .vio,$(basename $(PARSERS_VO)))
parsers-examples-quick: $(addsuffix .vio,$(basename $(PARSERS_EXAMPLES_VO)))
parsers-examples-verbose-quick: $(addsuffix .vio,$(basename $(PARSERS_EXAMPLES_VERBOSE_VO)))
parsers-all-quick: $(addsuffix .vio,$(basename $(PARSERS_ALL_VO)))
finitesets-quick: $(addsuffix .vio,$(basename $(FINITESETS_VO)))
dns-quick: $(addsuffix .vio,$(basename $(DNS_VO)))
facade-test-quick: $(addsuffix .vio,$(basename $(FACADE_TEST_VO)))
ics-quick: $(addsuffix .vio,$(basename $(ICS_VO)))
fiat4monitors-quick: $(addsuffix .vio,$(basename $(FIAT4MONITORS_VO)))
examples-quick: $(addsuffix .vio,$(basename $(EXAMPLES_VO)))
binencoders-quick: $(addsuffix .vio,$(basename $(BINENCODERS_VO)))

install-fiat: T = $(FIAT_VO)
install-fiat-core: T = $(FIAT_CORE_VO)
install-querystructures: T = $(QUERYSTRUCTURES_VO)
install-parsers: T = $(PARSERS_VO)
install-parsers-examples: T = $(PARSERS_EXAMPLES_VO)
install-parsers-examples-verbose: T = $(PARSERS_EXAMPLES_VERBOSE_VO)
install-parsers-all: T = $(PARSERS_ALL_VO)
install-finitesets: T = $(FINITESETS_VO)
install-dns: T = $(DNS_VO)
install-ics: T = $(ICS_VO)
install-fiat4monitors: T = $(FIAT4MONITORS_VO)
install-examples: T = $(EXAMPLES_VO)
install-binencoders: T = $(BINENCODERS_VO)

install-fiat install-fiat-core install-querystructures install-parsers install-parsers-examples install-parsers-examples-verbose install-parsers-all install-finitesets install-dns install-compiler install-fiat4monitors install-examples install-binencoders:
	$(SHOW)'MAKE -f Makefile.coq INSTALL'
	$(HIDE)$(MAKE) -f Makefile.coq VFILES="$(call vo_to_installv,$(T))" install

$(UPDATE_COQPROJECT_TARGET):
	(echo '-R src Fiat'; echo '-I src/Common/Tactics'; git ls-files "*.v" | grep -v '^$(COMPATIBILITY_FILE)$$' | $(SORT_COQPROJECT); (echo '$(COMPATIBILITY_FILE)'; git ls-files "*.ml4" | $(SORT_COQPROJECT); (echo '$(ML_COMPATIBILITY_FILES)' | tr ' ' '\n'; echo 'src/Common/Tactics/transparent_abstract_plugin.mllib'; echo 'src/Common/Tactics/hint_db_extra_plugin.mllib') | $(SORT_COQPROJECT))) > _CoqProject.in

ifeq ($(IS_FAST),0)
# >= 8.5 if it exists
NOT_EXISTS_LOC_DUMMY_LOC := $(call test_exists_ml_function,Loc.dummy_loc)

ifneq (,$(filter 8.4%,$(COQ_VERSION))) # 8.4 - this is a kludge to get around the fact that reinstalling 8.4 doesn't remove the 8.5 files, like universes.cmo
EXPECTED_EXT:=.v84
ML_DESCRIPTION := "Coq v8.4"
else
ifneq (,$(filter 8.5%,$(COQ_VERSION)))
EXPECTED_EXT:=.v85
ML_DESCRIPTION := "Coq v8.5"
else
ifneq (,$(filter 8.6%,$(COQ_VERSION)))
EXPECTED_EXT:=.v86
ML_DESCRIPTION := "Coq v8.6"
OTHERFLAGS += -w "-deprecated-appcontext -notation-overridden"
else
ifneq (,$(filter 8.7%,$(COQ_VERSION)))
EXPECTED_EXT:=.v87
ML_DESCRIPTION := "Coq v8.7"
OTHERFLAGS += -w "-deprecated-appcontext -notation-overridden"
else
ifneq (,$(filter trunk,$(COQ_VERSION)))
EXPECTED_EXT:=.trunk
ML_DESCRIPTION := "Coq trunk"
OTHERFLAGS += -w "-deprecated-appcontext -notation-overridden"
else
ifneq (,$(filter master,$(COQ_VERSION)))
EXPECTED_EXT:=.master
ML_DESCRIPTION := "Coq master"
OTHERFLAGS += -w "-deprecated-appcontext -notation-overridden"
else
ifeq ($(NOT_EXISTS_LOC_DUMMY_LOC),1) # <= 8.4
EXPECTED_EXT:=.v84
ML_DESCRIPTION := "Coq v8.4"
else
EXPECTED_EXT:=.trunk
ML_DESCRIPTION := "Coq trunk"
OTHERFLAGS += -w "-deprecated-appcontext -notation-overridden"
endif
endif
endif
endif
endif
endif
endif

# see http://stackoverflow.com/a/9691619/377022 for why we need $(eval $(call ...))
$(eval $(call SET_ML_COMPATIBILITY,src/Common/Tactics/hint_db_extra_tactics.ml,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Common/Tactics/hint_db_extra_plugin.ml4,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Common/Tactics/transparent_abstract_plugin.ml4,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Common/Tactics/transparent_abstract_tactics.ml,$(EXPECTED_EXT)))

endif


$(WATER_TANK_EXTRACT_ML): $(filter-out $(WATER_TANK_EXTRACT_VO),$(call vo_closure,$(WATER_TANK_EXTRACT_VO))) $(WATER_TANK_EXTRACT_VO:%.vo=%.v)
	$(SHOW)'COQC $(WATER_TANK_EXTRACT_VO:%.vo=%.v) > $@'
	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $(WATER_TANK_EXTRACT_VO:%.vo=%.v) > $@

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

src/Examples/HACMSDemo/wheelSensorEncoder.cmxa: src/examples/hacmsdemo/WheelSensorExtraction.vo
	cd src/Examples/HACMSDemo && ocamlopt -w -a -o wheelSensorEncoder.cmxa -a wheelSensorEncoder.mli wheelSensorEncoder.ml

encoder_repl: src/Examples/HACMSDemo/encoder_repl.ml src/Examples/HACMSDemo/wheelSensorEncoder.cmxa
	cd src/Examples/HACMSDemo && ocamlopt -w -a -o encoder_repl unix.cmxa str.cmxa wheelSensorEncoder.cmxa encoder_repl.ml

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )
