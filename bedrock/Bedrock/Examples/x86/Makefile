all: Factorial.exe

.PHONY: all

COQC = $(COQBIN)coqc -R ../.. Bedrock -I ../../reification

%.gen.ml: %AMD64.v ../%.vo ignoreFail.ml printCode.ml Makefile
	cat ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat printCode.ml >>$@

%.gen.s: %.gen.ml
	echo "	.data" >$@
	echo "	.global bedrock_heap, factDriver_main" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*10+50),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

%.exe: %.gen.o driver.o
	$(CC) $^ -o $@
