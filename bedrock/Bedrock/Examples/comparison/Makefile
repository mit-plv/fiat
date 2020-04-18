compare: gen.exe
	./gen.exe $(DATA) $(CMD)
	$(MAKE) c.exe ocaml.exe ocaml_nice.exe bedrock.exe
	time ./c.exe >/dev/null
	time ./ocaml.exe >/dev/null
	time ./ocaml_nice.exe >/dev/null
	time ./bedrock.exe >/dev/null

verify: gen.exe
	./gen.exe $(DATA) $(CMD)
	$(MAKE) c.exe ocaml.exe ocaml_nice.exe bedrock.exe
	./c.exe >/tmp/c.txt
	./ocaml.exe >/tmp/ocaml.txt
	./ocaml_nice.exe >/tmp/ocaml_nice.txt
	./bedrock.exe >/tmp/bedrock.txt
	diff /tmp/c.txt /tmp/ocaml.txt
	diff /tmp/c.txt /tmp/ocaml_nice.txt
	diff /tmp/c.txt /tmp/bedrock.txt

.PHONY: compare verify

gen.exe: gen.ml
	ocamlopt gen.ml -o gen.exe

c.exe: server.o data.o driver.o
	gcc server.o data.o driver.o -o c.exe

ocaml.exe: ocaml_server.ml ocaml_data.ml ocaml_driver.ml
	ocamlopt ocaml_server.ml ocaml_data.ml ocaml_driver.ml -o ocaml.exe

ocaml_nice.exe: ocaml_nice_server.ml ocaml_data.ml ocaml_nice_driver.ml
	ocamlopt ocaml_nice_server.ml ocaml_data.ml ocaml_nice_driver.ml -o ocaml_nice.exe

COQC = $(COQBIN)coqc -q -R ../.. Bedrock -I ../../reification

Server.vo: Server.v ../AutoSep.vo ../SinglyLinkedList.vo ../Malloc.vo
	$(COQC) Server

bedrock_server.ml Combined.vo: Combined.v Server.vo
	cat ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat printCode.ml >>$@

bedrock_server.s: bedrock_server.ml
	echo ".global bedrock_heap" >$@
	echo ".comm bedrock_heap,4*(100*1024*1024+3+1024)" >>$@
	echo ".global m_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

bedrock.exe: bedrock_server.o bedrock_data.o bedrock_driver.o
	cc bedrock_server.o bedrock_data.o bedrock_driver.o -o bedrock.exe
