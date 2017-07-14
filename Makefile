
all: Makefile.coq
	make -f Makefile.coq clean
	$(MAKE) -f Makefile.coq
	make install
	rm theories/myplug.vo
	make -f Makefile.coq theories/myplug.vo > test.log



Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install :
	make -f Makefile.coq install

clean:
	make -f Makefile.coq clean
	rm Makefile.coq
