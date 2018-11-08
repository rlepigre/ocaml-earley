.PHONY: all
all:
	@dune build

.PHONY: clean
clean:
	@dune clean

.PHONY: distclean
distclean: clean
	@find . -name "*~" -exec rm {} \;
	@rm -rf tmp_boot

OCAMLVERSION = $(shell ocamlc -version | sed s/+.*//)

.PHONY: boot
boot:
	@# Reinitialize the [tmp_boot] directory.
	@rm -rf tmp_boot
	@mkdir tmp_boot
	@# Preprocess the [pa_*] files.
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ast.ml \
		> tmp_boot/pa_ast.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_default.ml \
		> tmp_boot/pa_default.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_lexing.ml \
		> tmp_boot/pa_lexing.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_main.ml \
		> tmp_boot/pa_main.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ocaml.ml \
		> tmp_boot/pa_ocaml.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_ocaml_prelude.ml \
		> tmp_boot/pa_ocaml_prelude.ml
	@dune exec -- pa_ocaml --ascii pa_ocaml/pa_parser.ml \
		> tmp_boot/pa_parser.ml
	@# Erase [open Earley_ocaml] from [tmp_boot/pa_default.ml]
	@sed -i 's/open Earley_ocaml//g' tmp_boot/pa_default.ml
	@# Copy the [static/helpers] files.
	@cp static/helpers/helper.mli tmp_boot/helper.mli
	@cp static/helpers/$(OCAMLVERSION)/* tmp_boot/
	@# Generate [compare.ml].
	@dune exec -- pa_ocaml --ascii static/tools/generic_eq.ml \
		> tmp_boot/compare.ml
	@echo "(* asttypes.mli *)" \
		>> tmp_boot/compare.ml
	@dune exec -- pa_eq static/tools/$(OCAMLVERSION)/asttypes.mli \
		>> tmp_boot/compare.ml
	@echo "(* parsetree.mli *)" \
		>> tmp_boot/compare.ml
	@dune exec -- pa_eq static/tools/$(OCAMLVERSION)/parsetree.mli \
		>> tmp_boot/compare.ml
	@# Generate [iter.ml].
	@dune exec -- pa_ocaml --ascii static/tools/generic_iter.ml \
		> tmp_boot/iter.ml
	@echo "(* asttypes.mli *)" \
		>> tmp_boot/iter.ml
	@dune exec -- pa_iter static/tools/$(OCAMLVERSION)/asttypes.mli \
		>> tmp_boot/iter.ml
	@echo "(* parsetree.mli *)" \
		>> tmp_boot/iter.ml
	@dune exec -- pa_iter static/tools/$(OCAMLVERSION)/parsetree.mli \
		>> tmp_boot/iter.ml
	@# Generate [quote.ml].
	@dune exec -- pa_ocaml --ascii static/tools/generic_quote.ml \
		> tmp_boot/quote.ml
	@echo "(* asttypes.mli *)" \
		>> tmp_boot/quote.ml
	@dune exec -- pa_quote static/tools/$(OCAMLVERSION)/asttypes.mli \
		>> tmp_boot/quote.ml
	@echo "(* parsetree.mli *)" \
		>> tmp_boot/quote.ml
	@dune exec -- pa_quote static/tools/$(OCAMLVERSION)/parsetree.mli \
		>> tmp_boot/quote.ml
	@# Replace boot directory.
	@rm -rf boot/$(OCAMLVERSION)
	@mv tmp_boot boot/$(OCAMLVERSION)
