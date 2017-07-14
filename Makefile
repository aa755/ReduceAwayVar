
all: Makefile.coq
	$(MAKE) -f Makefile.coq
	make install
	rm theories/myplug.vo
	make -f Makefile.coq theories/myplug.vo > test.vlog



Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install :
	make -f Makefile.coq install

clean:
	make -f Makefile.coq clean
	rm Makefile.coq
