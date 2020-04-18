CFLAGS ?= -std=c99 -O3 -Wall -Wpedantic

.PHONY: all test

all: test_ab_star test_ab_star_reference

test_ab_star test_ab_star_reference: % : %.ml
	ocamlopt -o $@ $<

ab10:
	echo -n "abababababababababab" > $@

ab10.0 ab10.0.0 ab10.0.0.0 ab10.0.0.0.0 ab10.0.0.0.0.0 ab10.0.0.0.0.0.0 ab10.0.0.0.0.0.0.0 ab10.0.0.0.0.0.0.0.0 : %.0 : %
	@cp -f $< $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@
	@cat $< >> $@

make_fmt = $$(echo "$1 (real: %e, user: %U, sys: %S, mem: %M ko)" | sed s'/\.//g')

test: ab10.0.0.0.0.0 test_ab_star test_ab_star_reference
	for F in ab10 ab10.0 ab10.0.0 ab10.0.0.0 ab10.0.0.0.0 ab10.0.0.0.0.0; do \
	FMT="$(call make_fmt, $$F)"; \
	$(shell which time) -f "cat       $$FMT" cat $$F>/dev/null; \
	echo $$?; \
	$(shell which time) -f "reference $$FMT" ./test_ab_star_reference $$F; \
	echo $$?; \
	$(shell which time) -f "coq       $$FMT" ./test_ab_star $$F; \
	echo $$?; \
	done
