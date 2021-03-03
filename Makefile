include CoqMakefile

CoqMakefile:
	coq_makefile -f _CoqProject -o CoqMakefile

documentation:
	coq2html -short-names -no-css -d docs *.glob *.v
