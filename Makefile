all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install :
	make -f Makefile.coq install

clean:
	make -f Makefile.coq clean
	rm Makefile.coq
	rm _CoqProject
