all:
	ocamlopt -c options.ml
	ocamlopt -c pairs.ml
	ocamlopt -c refpairs.ml
	ocamlopt -c lists.ml
	ocamlopt -a -o utils.cmxa options.cmx pairs.cmx refpairs.cmx lists.cmx

opt:
	ocamlopt -c options.ml
	ocamlopt -c pairs.ml
	ocamlopt -c refpairs.ml
	ocamlopt -c lists.ml
	ocamlopt -a -o utils.cmxa options.cmx pairs.cmx refpairs.cmx lists.cmx


clean:
	rm -f *.cm[ioxa]
	rm -f *.a
	rm -f *.o
	rm -f utils.cma
	rm -f utils.cmxa