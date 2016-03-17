DECAP_DIR = ../..
PA_OCAML = $(DECAP_DIR)/pa_ocaml

all: calc_decap calc_gdecap calc_sdecap

calc_decap.cmx: calc_decap.ml $(PA_OCAML) $(DECAP_DIR)/decap.cmxa
	ocamlopt -pp $(PA_OCAML) -c -I $(DECAP_DIR) $<

calc_decap: calc_decap.ml $(PA_OCAML) $(DECAP_DIR)/decap.cmxa calc_decap.cmx main.ml
	ocamlopt -pp $(PA_OCAML) -I $(DECAP_DIR) -o $@ unix.cmxa str.cmxa $(DECAP_DIR)/decap.cmxa calc_decap.cmx main.ml

calc_gdecap.cmx: calc_gdecap.ml $(PA_OCAML) $(DECAP_DIR)/decap.cmxa
	ocamlopt -pp $(PA_OCAML) -c -I $(DECAP_DIR) $<

calc_gdecap: calc_gdecap.ml $(PA_OCAML) $(DECAP_DIR)/decap.cmxa calc_gdecap.cmx gmain.ml
	ocamlopt -pp $(PA_OCAML) -I $(DECAP_DIR) -o $@ unix.cmxa str.cmxa $(DECAP_DIR)/decap.cmxa calc_gdecap.cmx gmain.ml

calc_sdecap.cmx: calc_sdecap.ml $(PA_OCAML) $(DECAP_DIR)/decap.cmxa
	ocamlopt -pp $(PA_OCAML) -c -I $(DECAP_DIR) $<

calc_sdecap: calc_sdecap.ml $(PA_OCAML) $(DECAP_DIR)/decap.cmxa calc_sdecap.cmx
	ocamlopt -pp $(PA_OCAML) -o $@ unix.cmxa str.cmxa $(DECAP_DIR)/decap.cmxa calc_sdecap.cmx

clean:
	rm -f *.cmi *.cmo

distclean: clean
	rm -f calc_decap calc_gdecap calc_sdecap
