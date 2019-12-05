# rudimentary
all:	libsoufflenum.so tests

libsoufflenum.so: 	num256.cpp
	g++ -std=c++17 -O3 -shared -o libsoufflenum.so -fPIC num256.cpp
	ln -sf libsoufflenum.so libfunctors.so 

tests:	num256.cpp num256_test.cpp
	g++ -std=c++17 -o tests num256_test.cpp
	./tests
