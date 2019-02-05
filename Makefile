# rudimentary
all:	libsoufflenum.so tests

libsoufflenum.so: 	num256.cpp
	g++ -O3 -shared -o libsoufflenum.so -fPIC num256.cpp
	ln -sf libsoufflenum.so libfunctors.so 

tests:	num256.cpp num256_test.cpp
	g++ -o tests num256_test.cpp
	./tests
