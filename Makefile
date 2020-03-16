# rudimentary
all:	libsoufflenum.so num_tests mappings_tests

libsoufflenum.so: 	num256.cpp mappings.cpp
	g++ -march=native -std=c++17 -O3 -shared -o libsoufflenum.so -fPIC num256.cpp mappings.cpp -lcrypto -lssl
	ln -sf libsoufflenum.so libfunctors.so 

num_tests:	num256.cpp num256_test.cpp 
	g++ -march=native -std=c++17 -o num_tests num256_test.cpp -lcrypto -lssl
	./num_tests

mappings_tests:	mappings.cpp mappings_test.cpp
	g++ -march=native -std=c++17 -o mappings_tests mappings_test.cpp -lcrypto -lssl
	./mappings_tests
