lambda_calcul: lambda.ml
	ocamlbuild -use-ocamlfind lambda.native


clean:
	ocamlbuild -clean
