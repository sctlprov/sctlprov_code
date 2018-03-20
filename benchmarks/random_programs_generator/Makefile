all: generator_p1.ml generator_p2.ml
	ocamlc -c generator_p1.ml
	ocamlc -o generator_p1 generator_p1.cmo
	ocamlc -c generator_p2.ml
	ocamlc -o generator_p2 generator_p2.cmo

clean: 
	rm -f *.cmo *.cmi
	rm -f generator_p1 generator_p2
	rm -f *.model
	rm -f *.smv 
	rm -f *.vvm
	
