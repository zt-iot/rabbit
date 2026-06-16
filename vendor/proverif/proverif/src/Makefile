OCB_FLAGS = -use-ocamlfind -tag bin_annot
OCB = ocamlbuild $(OCB_FLAGS)

all: native

native:
	$(OCB) reduction.inferred.mli main.native
	cp _build/main.native proverif

clean:
	$(OCB) -clean
