old:
	 ocamlopt -I +compiler-libs ocamlcommon.cmxa str.cmxa symtbl.ml zipper.ml -o symold

new:
	 ocamlopt -I +compiler-libs ocamlcommon.cmxa str.cmxa symtbl_zip.ml zipper.ml -o symzip

test:
	./symzip rec_fn.cmt
