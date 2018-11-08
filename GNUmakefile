.PHONY: all
all:
	@dune build

.PHONY: clean
clean:
	@dune clean

.PHONY: distclean
distclean: clean
	@find . -name "*~" -exec rm {} \;
	@rm -rf boottmp

OCAMLVERSION = $(shell ocamlc -version | sed s/+.*//)

.PHONY: boot
boot:
	@# Reinitialize the [boottmp] directory.
	@rm -rf boottmp
	@mkdir boottmp
	@# Preprocess the [pa_*] files.
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ast.ml \
		> boottmp/pa_ast.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_default.ml \
		> boottmp/pa_default.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_lexing.ml \
		> boottmp/pa_lexing.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_main.ml \
		> boottmp/pa_main.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ocaml.ml \
		> boottmp/pa_ocaml.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ocaml_prelude.ml \
		> boottmp/pa_ocaml_prelude.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_parser.ml \
		> boottmp/pa_parser.ml
	@# Erase [open Earley_ocaml] from [boottmp/pa_default.ml]
	@sed -i 's/open Earley_ocaml//g' boottmp/pa_default.ml
	@# Copy the [ast_helper] files.
	@cp ast_helper/helper.mli boottmp/helper.mli
	@cp ast_helper/$(OCAMLVERSION)/* boottmp/
	@# Generate [compare.ml].
	@dune exec -- pa_ocaml --ascii ast_tools/generic_eq.ml \
		> boottmp/compare.ml
	@echo "(* asttypes.mli *)" \
		>> boottmp/compare.ml
	@dune exec -- pa_eq ast_tools/$(OCAMLVERSION)/asttypes.mli \
		>> boottmp/compare.ml
	@echo "(* parsetree.mli *)" \
		>> boottmp/compare.ml
	@dune exec -- pa_eq ast_tools/$(OCAMLVERSION)/parsetree.mli \
		>> boottmp/compare.ml
	@# Generate [iter.ml].
	@dune exec -- pa_ocaml --ascii ast_tools/generic_iter.ml \
		> boottmp/iter.ml
	@echo "(* asttypes.mli *)" \
		>> boottmp/iter.ml
	@dune exec -- pa_iter ast_tools/$(OCAMLVERSION)/asttypes.mli \
		>> boottmp/iter.ml
	@echo "(* parsetree.mli *)" \
		>> boottmp/iter.ml
	@dune exec -- pa_iter ast_tools/$(OCAMLVERSION)/parsetree.mli \
		>> boottmp/iter.ml
	@# Generate [quote.ml].
	@dune exec -- pa_ocaml --ascii ast_tools/generic_quote.ml \
		> boottmp/quote.ml
	@echo "(* asttypes.mli *)" \
		>> boottmp/quote.ml
	@dune exec -- pa_quote ast_tools/$(OCAMLVERSION)/asttypes.mli \
		>> boottmp/quote.ml
	@echo "(* parsetree.mli *)" \
		>> boottmp/quote.ml
	@dune exec -- pa_quote ast_tools/$(OCAMLVERSION)/parsetree.mli \
		>> boottmp/quote.ml
	@# Replace boot directory.
	@rm -rf boot/$(OCAMLVERSION)
	@mv boottmp boot/$(OCAMLVERSION)
