OCAMLC = ocamlopt
CMO = cmx
CMA = cmxa

LIBS = str.$(CMA) unix.$(CMA)

uruz2:	code.$(CMO) flags.$(CMO) uruz2_utils.$(CMO) uruz2_ast.$(CMO) uruz2_parser.$(CMO) uruz2_lexer.$(CMO) uruz2_main.$(CMO) main.$(CMO)
	$(OCAMLC) -o uruz2 $(LIBS) uruz2_utils.$(CMO) uruz2_ast.$(CMO) uruz2_parser.$(CMO) uruz2_lexer.$(CMO) uruz2_main.$(CMO) flags.$(CMO) code.$(CMO) main.$(CMO)

main.$(CMO):	main.ml uruz2_main.$(CMO) uruz2_parser.$(CMO) uruz2_lexer.$(CMO) uruz2_ast.$(CMO) uruz2_utils.$(CMO) flags.$(CMO) code.$(CMO)
	$(OCAMLC) -c main.ml

flags.$(CMO):	flags.ml uruz2_utils.$(CMO)
	$(OCAMLC) -c flags.ml

code.$(CMO):	code.ml flags.$(CMO) uruz2_utils.$(CMO) uruz2_ast.$(CMO)
	$(OCAMLC) -c code.ml

uruz2_Makefile:	uruz2.gra
	uruz uruz2.gra

clean:	uruz2_clean
	rm -rf *.o *.cm* *.mli uruz2_main.ml uruz2_utils.ml uruz2_ast.ml uruz2_parser.ml uruz2_parser.mly uruz2_lexer.ml uruz2_lexer.mll uruz2_Makefile

test:	
		MAX=`ls -1 tests/*.gra | wc -l`; COUNTER=0; echo ----------------; for i in tests/*.gra; do echo "Testing: $$i"; \
		FOOBAR=`./uruz2 -flatten $$i | tr "\\n" " " | sed "s/ //g"`; \
		BAZBAR=`cat $$i.ans | tr "\\n" " " | sed "s/ //g"`; \
		if [ "$$FOOBAR" != "$$BAZBAR" ]; then echo FAIL; else echo ok; COUNTER=$$(($$COUNTER + 1)); fi \
		; done; echo ----------------; echo $$COUNTER out of $$MAX

include uruz2_Makefile
