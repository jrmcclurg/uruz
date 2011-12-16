pgg:	ast.cmo pp.cmo utils.cmo parser.cmo lexer.cmo main.cmo
	ocamlc -o pgg.exe ast.cmo pp.cmo utils.cmo parser.cmo lexer.cmo main.cmo

pp.cmo:		pp.ml ast.cmo
		ocamlc -c pp.ml

main.cmo:	main.ml parser.cmo lexer.cmo 
		ocamlc -c main.ml

parser.cmo:	parser.ml parser.cmi utils.cmo
		ocamlc -c parser.ml

lexer.cmo:	lexer.ml parser.cmi utils.cmo
		ocamlc -c lexer.ml

utils.cmo:	utils.ml ast.cmo
		ocamlc -c utils.ml

parser.cmi:	parser.mli ast.cmo
		ocamlc -c parser.mli

ast.cmo:	ast.ml
		ocamlc -c ast.ml

parser.ml:	parser.mly
		ocamlyacc parser.mly

parser.mli:	parser.mly
		ocamlyacc parser.mly

lexer.ml:	lexer.mll
		ocamllex lexer.mll

clean:		
		rm *.cm* *.mli parser.ml lexer.ml

wc:		
		wc -l lexer.mll parser.mly ast.ml utils.ml pp.ml main.ml 
