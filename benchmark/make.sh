

cd calcyacc
source make.sh
cd ..

cd calccamlp4
source make.sh
cd ..

cd calcdecap
make
cd ..

cd calc_testfiles
ocamlopt -o generate generate.ml
./generate
cd ..

ocamlopt -I .. -I ./calccamlp4 -I ./calcyacc -I ./calcdecap -I +camlp4 -o calc unix.cmxa str.cmxa decap.cmxa dynlink.cmxa camlp4lib.cmxa calc_decap.cmx calc_gdecap.cmx calc_sdecap.cmx calc_camlp4.cmx parser.cmx lexer.cmx calc.ml

./calc
