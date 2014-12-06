PREFIX=/usr
DESTDIR=
OFLAGS=-O1
CFLAGS=-O2
CC=gcc

# you get a .parrot if err builds and tests pass
everything: .parrot

.parrot: bin/err test/*.err* theory/*.the test/*.the*
	test/run ./bin/err
	touch .parrot

fasl: bin/faslerr

# fast build because C compiler is not needed, requires global owl-vm install though
# mainly useful for working on raspberry or very slow netbook
bin/faslerr: err.fasl
	mkdir -p bin
	echo '#!/usr/bin/owl-vm' > bin/faslerr
	cat err.fasl >> bin/faslerr
	chmod +x bin/faslerr
	./bin/faslerr --help || echo "no global owl install?"
	test/run ./bin/faslerr

bin/err: err.c
	mkdir -p bin
	$(CC) $(CFLAGS) -o bin/err err.c

err.c: err/*.scm owl-lisp/bin/ol
	owl-lisp/bin/ol $(OFLAGS) -o err.c err/main.scm
	
err.fasl: err/*.scm owl-lisp/bin/ol
	owl-lisp/bin/ol -o err.fasl err/main.scm

install: bin/err .parrot
	mkdir -p $(DESTDIR)$(PREFIX)/bin
	install -m 755 bin/err $(DESTDIR)$(PREFIX)/bin/err
 
uninstall:
	-rm $(DESTDIR)$(PREFIX)/bin/err

owl-lisp/bin/ol:
	-git clone https://github.com/aoh/owl-lisp.git
	-cd owl-lisp && git pull
	cd owl-lisp && make

clean:
	-rm bin/err err.c err.fasl
	-rm theory/*.err
	-cd owl-lisp && make clean
