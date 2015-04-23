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

containing = $(foreach v,$2,$(if $(findstring $1,$v),$v))
not-containing = $(foreach v,$2,$(if $(findstring $1,$v),,$v))

.PHONY: fiat fiat-core querystructures parsers examples \
	install install-fiat install-fiat-core install-querystructures install-parsers install-finitesets install-dns install-compiler install-ics install-fiat4monitors install-examples \
	pdf doc clean-doc \
	clean update-_CoqProject FORCE

FAST_TARGETS := clean clean-doc archclean printenv clean-old update-_CoqProject Makefile.coq

# pipe the output of coq_makefile through sed so that we don't have to run coqdep just to clean
# use tr to handle the fact that BSD sed doesn't substitute \n
Makefile.coq: Makefile _CoqProject
	$(VECHO) "COQ_MAKEFILE -f _CoqProject > $@"
	$(Q)$(COQBIN)coq_makefile COQC = "\$$(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject | sed s'/^\(-include.*\)$$/ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)~\1~else~ifeq ($$(MAKECMDGOALS),)~\1~endif~endif/g' | tr '~' '\n' | sed s'/^clean:$$/clean-old::/g' | sed s'/^clean::$$/clean-old::/g' | sed s'/^Makefile: /Makefile-old: /g' > $@

-include Makefile.coq

.DEFAULT_GOAL := fiat

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
	rm -f src/Examples/Ics/WaterTank.ml
	rm -f Makefile.coq .depend

clean-doc::
	rm -rf html
	rm -f all.pdf Overview/library.pdf Overview/ProjectOverview.pdf Overview/coqdoc.sty coqdoc.sty
	rm -f $(shell find Overview -name "*.log" -o -name "*.aux" -o -name "*.bbl" -o -name "*.blg" -o -name "*.synctex.gz" -o -name "*.out" -o -name "*.toc")

# Recursively find the transitively closed dependencies of the set $1
# of *.vo files, using an accumulating parameter $2 of dependencies
# previously found.  We extract the dependencies from the
# corresponding *.v.d files using sed(1), filter out previously found
# dependencies, sort to remove duplicates, then make a recursive call
# with the deduplicated newly found dependencies.  When $1 becomes
# empty, the result is $2.
read_deps = $(if $(wildcard $1),$(filter %.vo,$(shell sed -n 's/^[^:]*: // p' $(wildcard $1))))
vo_closure = $(if $1,$(call vo_closure,$(sort $(filter-out $1 $2,$(call read_deps,$(1:.vo=.v.d)))),$1 $2),$2)

QUERYSTRUCTURES_UNMADE_VO := \
	src/QueryStructure/Implementation/DataStructures/Bags/InvertedIndexBags.vo

PARSERS_UNMADE_VO := \
	src/Parsers/Refinement/SharpenedExpressionPlus.vo \
	src/Parsers/Refinement/DisjointLemmas.vo

EXAMPLES_UNMADE_VO :=

WATER_TANK_EXTRACT_VO := src/Examples/Ics/WaterTankExtract.vo
WATER_TANK_EXTRACT_ML := src/Examples/Ics/WaterTank.ml

FIAT_CORE_VO := $(filter-out src/Fiat4Monitors/% src/QueryStructure/% src/Parsers/% src/FiniteSetADTs/% src/FiatToFacade/% src/Examples/% src/FiniteSetADTs.vo,$(filter src/%.vo,$(VOFILES)))
QUERYSTRUCTURES_VO := $(filter src/QueryStructure/%.vo,$(filter-out $(QUERYSTRUCTURES_UNMADE_VO),$(VOFILES)))
PARSERS_VO := $(filter-out $(PARSERS_UNMADE_VO),$(filter src/Parsers/%.vo,$(VOFILES)))
EXAMPLES_VO := $(filter-out $(EXAMPLES_UNMADE_VO),$(filter src/Examples/%.vo,$(VOFILES)))

FIAT_VO := $(FIAT_CORE_VO) $(QUERYSTRUCTURES_VO) $(PARSERS_VO)

fiat: $(FIAT_VO)
fiat-core: $(FIAT_CORE_VO)
querystructures: $(QUERYSTRUCTURES_VO)
parsers: $(PARSERS_VO)
examples: $(EXAMPLES_VO)

install-fiat: T = $(FIAT_VO)
install-fiat-core: T = $(FIAT_CORE_VO)
install-querystructures: T = $(QUERYSTRUCTURES_VO)
install-parsers: T = $(PARSERS_VO)
install-examples: T = $(EXAMPLES_VO)

install-fiat install-fiat-core install-querystructures install-parsers install-examples:
	$(VECHO) "MAKE -f Makefile.coq INSTALL"
	$(Q)$(MAKE) -f Makefile.coq VFILES="$(addsuffix .v,$(basename $(call vo_closure,$(filter %.vo,$(T)))))" install

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

update-_CoqProject:
	(echo '-R src Fiat'; echo '-arg -dont-load-proofs'; find src -name "*.v" | $(SORT_COQPROJECT)) > _CoqProject

$(filter-out $(VOFILES),$(call vo_closure,$(VOFILES))): FORCE
	@ echo
	@ echo 'error: $@ is missing from _CoqProject.'
	@ echo 'error: Please run `make update-_CoqProject`.'
	@ echo
	@ false

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
