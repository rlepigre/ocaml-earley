.PHONY: all
all:
	@dune build

.PHONY: clean
clean:
	@dune clean

.PHONY: distclean
distclean: clean
	@find . -name "*~" -exec rm {} \;

OCAMLVERSION = $(shell ocamlc -version | sed s/+.*//)

.PHONY: boot
boot:
	@# Reinitialize the [tmp] directory.
	@rm -rf tmp
	@mkdir tmp
	@# Preprocess the [pa_*] files.
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ast.ml \
		> tmp/pa_ast.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_default.ml \
		> tmp/pa_default.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_lexing.ml \
		> tmp/pa_lexing.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_main.ml \
		> tmp/pa_main.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ocaml.ml \
		> tmp/pa_ocaml.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ocaml_prelude.ml \
		> tmp/pa_ocaml_prelude.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_parser.ml \
		> tmp/pa_parser.ml
	@# Erase [open Earley_ocaml] from [tmp/pa_default.ml]
	@sed -i 's/open Earley_ocaml//g' tmp/pa_default.ml
	@# Copy the [ast_helper] files.
	@cp ast_helper/helper.mli tmp/helper.mli
	@cp ast_helper/$(OCAMLVERSION)/* tmp/
	@# Generate [compare.ml].
	@dune exec -- pa_ocaml --ascii ast_tools/generic_eq.ml \
		> tmp/compare.ml
	@echo "(* asttypes.mli *)" \
		>> tmp/compare.ml
	@dune exec -- pa_eq ast_tools/$(OCAMLVERSION)/asttypes.mli \
		>> tmp/compare.ml
	@echo "(* parsetree.mli *)" \
		>> tmp/compare.ml
	@dune exec -- pa_eq ast_tools/$(OCAMLVERSION)/parsetree.mli \
		>> tmp/compare.ml
	@# Generate [iter.ml].
	@dune exec -- pa_ocaml --ascii ast_tools/generic_iter.ml \
		> tmp/iter.ml
	@echo "(* asttypes.mli *)" \
		>> tmp/iter.ml
	@dune exec -- pa_iter ast_tools/$(OCAMLVERSION)/asttypes.mli \
		>> tmp/iter.ml
	@echo "(* parsetree.mli *)" \
		>> tmp/iter.ml
	@dune exec -- pa_iter ast_tools/$(OCAMLVERSION)/parsetree.mli \
		>> tmp/iter.ml
	@# Generate [quote.ml].
	@dune exec -- pa_ocaml --ascii ast_tools/generic_quote.ml \
		> tmp/quote.ml
	@echo "(* asttypes.mli *)" \
		>> tmp/quote.ml
	@dune exec -- pa_quote ast_tools/$(OCAMLVERSION)/asttypes.mli \
		>> tmp/quote.ml
	@echo "(* parsetree.mli *)" \
		>> tmp/quote.ml
	@dune exec -- pa_quote ast_tools/$(OCAMLVERSION)/parsetree.mli \
		>> tmp/quote.ml
	@# Replace boot directory.
	@rm -rf boot/$(OCAMLVERSION)
	@mv tmp boot/$(OCAMLVERSION)
