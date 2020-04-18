COQC := $(COQBIN)coqc -R .. Bedrock -I ../reification

.PHONY: default master rtos32 rtos64
.PRECIOUS: tests/%.gen.ml tests/%.gen.s

default:

tests/%.gen.ml: tests/%AMD64.v tests/%Driver.vo tests/ignoreFail.ml tests/printCode.ml Makefile
	cat tests/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat tests/printCode.ml >>$@

tests/%.gen.s: tests/%.gen.ml tests/%.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/$*.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

tests/%32.gen.ml: tests/%I386.v tests/%Driver.vo tests/ignoreFail.ml tests/printCode.ml Makefile
	cat tests/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat tests/printCode.ml >>$@

tests/%32.gen.s: tests/%32.gen.ml tests/%.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/$*.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

tests/%.exe: tests/%.gen.o tests/sys.o tests/driver.o
	cc $^ -o $@

tests/pages.gen.s:
	ocaml str.cma tests/makepages.ml $(PAGES) >$@

tests/WebServer.exe: tests/WebServer.gen.o tests/pages.gen.o tests/sys.o tests/driver.o
	cc $^ -o $@

tests/Rtos.exe: tests/Rtos.gen.o tests/sys.o tests/driver.o tests/rtos.o tests/rtos_app.o
	cc $^ -o $@

tests/Rtos.gen.s: tests/Rtos.gen.ml tests/Rtos.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/Rtos.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main,scheduler_init,scheduler_spawn,scheduler_exit,scheduler_yield,scheduler_listen,scheduler_close,scheduler_read,scheduler_write,scheduler_accept,scheduler_connect,scheduler_connected" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

tests/Rtos32.gen.s: tests/Rtos32.gen.ml tests/Rtos.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/Rtos.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main,scheduler_init,scheduler_spawn,scheduler_exit,scheduler_yield,scheduler_listen,scheduler_close,scheduler_read,scheduler_write,scheduler_accept,scheduler_connect,scheduler_connected" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

master: tests/sys.c tests/driver32.s tests/RosMaster32.gen.s
	mkdir -p /tmp/master
	-rm /tmp/master/*
	cp tests/sys.c /tmp/master
	cp tests/driver32.s /tmp/master/driver.s
	cp tests/RosMaster32.gen.s /tmp/master/RosMaster.s
	cp Makefile.ros /tmp/master/Makefile
	cd /tmp ; tar zcf master.tgz master

LIB := tests
CITO_EXAMPLES_DIR := Cito/examples

$(CITO_EXAMPLES_DIR)/%.gen.ml: $(CITO_EXAMPLES_DIR)/%AMD64.v $(CITO_EXAMPLES_DIR)/%Driver.vo $(LIB)/ignoreFail.ml $(LIB)/printCode.ml Makefile
	cat $(LIB)/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		| sed 's/let rec nuke/type set = unit\n\nlet rec nuke/' \
		>>$@
	cat $(LIB)/printCode.ml >>$@

$(CITO_EXAMPLES_DIR)/%.gen.s: $(CITO_EXAMPLES_DIR)/%.gen.ml
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024+50),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

$(CITO_EXAMPLES_DIR)/%.exe: %.gen.o $(LIB)/sys.o $(LIB)/driver.o
	cc $^ -o $@

rtos64: tests/sys.c tests/driver.s tests/Rtos.gen.s tests/rtos.s tests/bedrock.h tests/rtos_app.c
	mkdir -p /tmp/brtos64
	-rm /tmp/brtos64/*
	cp README.rtos /tmp/brtos64/README
	cp tests/sys.c /tmp/brtos64/
	cp tests/driver.s /tmp/brtos64/
	cp tests/Rtos.gen.s /tmp/brtos64/bedrock.s
	cp Makefile.rtos64 /tmp/brtos64/Makefile
	cp tests/bedrock.h /tmp/brtos64/
	cp tests/rtos_app.c /tmp/brtos64/
	cp tests/rtos.s /tmp/brtos64/
	cd /tmp ; tar zcf brtos64.tgz brtos64

rtos32: tests/sys.c tests/driver32.s tests/Rtos32.gen.s tests/rtos32.s tests/bedrock.h tests/rtos_app.c
	mkdir -p /tmp/brtos32
	-rm /tmp/brtos32/*
	cp README.rtos /tmp/brtos32/README
	cp tests/sys.c /tmp/brtos32/
	cp tests/driver32.s /tmp/brtos32/driver.s
	cp tests/Rtos32.gen.s /tmp/brtos32/bedrock.s
	cp Makefile.rtos32 /tmp/brtos32/Makefile
	cp tests/bedrock.h /tmp/brtos32/
	cp tests/rtos_app.c /tmp/brtos32/
	cp tests/rtos32.s /tmp/brtos32/rtos.s
	cd /tmp ; tar zcf brtos32.tgz brtos32
