
all: Makefile.coq
	make -f Makefile.coq clean
	export ZDEBUG='-g -bin-annot'
	$(MAKE) -f Makefile.coq
	make install
	rm -f theories/test.vo
	make -f Makefile.coq theories/test.vo > test.log



Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install :
	make -f Makefile.coq install

clean:
	make -f Makefile.coq clean
	rm Makefile.coq
	rm src/reduceawayvar.cmt
