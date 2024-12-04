KECCAK_DIR := keccak
KECCAK_SRC := $(wildcard $(KECCAK_DIR)/*.c)
KECCAK_OBJ := $(patsubst $(KECCAK_DIR)/%.c,$(KECCAK_DIR)/%.o, $(KECCAK_SRC))

.PHONY: clean softclean

# rudimentary
all: libsoufflenum.so num_tests mappings_tests keccak256_tests

libsoufflenum.so: $(KECCAK_OBJ) num256.o mappings.o keccak256.o lists.o smt-api.o
	g++ -std=c++17 -shared -o libsoufflenum.so $(KECCAK_OBJ) smt-api.o num256.o mappings.o keccak256.o lists.o -march=native -lz3
	ln -sf libsoufflenum.so libfunctors.so

# all: libsoufflenum.so

# libsoufflenum.so: smt-api.o symeval.o
# 	g++ -std=c++17 -shared -o libsoufflenum.so smt-api.o symeval.o -march=native -lz3
# 	ln -sf libsoufflenum.so libfunctors.so

smt-api.o: smt-api.cpp
	g++ -std=c++17 -O2 smt-api.cpp -lz3 -c -fPIC -o smt-api.o

num256.o: num256.cpp
	g++ -std=c++17 -O2 num256.cpp -c -fPIC -o num256.o -lz3

num_tests:	num256.cpp num256_test.cpp
	g++ -std=c++17 -o num_tests num256_test.cpp
	./num_tests

mappings.o: mappings.cpp
	g++ -std=c++17 -O2 mappings.cpp -c -fPIC -o mappings.o -lz3

mappings_tests:	mappings.cpp mappings_test.cpp
	g++ -std=c++17 -o mappings_tests mappings_test.cpp
	./mappings_tests

lists.o: lists.cpp
	g++ -std=c++17 -O2 lists.cpp -c -fPIC -o lists.o -lz3

lists_tests:	lists.cpp lists_test.cpp
	g++ -std=c++17 -o lists_tests lists_test.cpp
	./lists_tests

keccak256.o: keccak256.cpp
	g++ -std=c++17 -O2 keccak256.cpp -c -fPIC -o keccak256.o

keccak256_test.o: keccak256_test.cpp keccak256.cpp
	g++ -std=c++17 -O2 -c -o keccak256_test.o keccak256_test.cpp

keccak256_tests: keccak256_test.o $(KECCAK_OBJ)
	g++ -std=c++17 keccak256_test.o $(KECCAK_OBJ) -o keccak256_tests
	./keccak256_tests

# Format all C++ files following standardized formatting
#  requires installing clang-format
# Currently applying only on smt-api{.cpp,.h} files to
# reduce conflicts when these changes are merged upstream.
.PHONY: format
format:
	clang-format -style="{BasedOnStyle: Google, ColumnLimit: 160}" -i smt-api.cpp smt-api.h

softclean:
	rm -f $(KECCAK_OBJ)
	rm -f *.o

clean: softclean
	rm -f libsoufflenum.so libfunctors.so
	rm -f keccak256_tests num_tests mappings_tests
