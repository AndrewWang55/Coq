check:
	bash checkenv.sh && bash checktypes.sh && bash checkauto.sh

admitted:
	coqc a10.v
	coqchk -silent -o -norec a10
	
extract:
	coqc a10.v extract.v

clean:
	rm -f *.vo *.glob .*.aux tlqueue.ml*
