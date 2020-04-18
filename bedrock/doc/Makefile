WWW = /afs/csail.mit.edu/group/plv/www/data/bedrock

.PHONY: all install

BEDROCK = -R ../src Bedrock
ARGS = $(BEDROCK) -I ../examples
GLOB = --glob-from Tutorial.glob

all: tutorial.pdf Tutorial.html

tutorial.pdf: tutorial.tex Tutorial.v.tex Makefile
	pdflatex tutorial
	pdflatex tutorial

Tutorial.v.tex: Tutorial.vo Makefile
	coqdoc -s --body-only --latex $(BEDROCK) $(GLOB) Tutorial.v -o Tutorial.v.tex

Tutorial.html: Tutorial.vo Makefile
	coqdoc -s --html $(BEDROCK) $(GLOB) Tutorial.v

Tutorial.vo: Tutorial.v Makefile
	coqc $(ARGS) -dump-glob Tutorial.glob Tutorial

install: tutorial.pdf Tutorial.html
	cp Tutorial.v $(WWW)/
	cp tutorial.pdf $(WWW)/
	cp Tutorial.html $(WWW)/
	cp coqdoc.css $(WWW)/
