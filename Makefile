#old:
	 #ocamlopt -I +compiler-libs ocamlcommon.cmxa str.cmxa symtbl.ml zipper.ml -o symold

new:
	 ocamlopt -I +compiler-libs ocamlcommon.cmxa str.cmxa zipper.ml symtbl_zip.ml -o symzip

test:
	./symzip rec_fn.cmt
