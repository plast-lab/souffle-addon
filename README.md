A simple add-on dynamic library for more complex arithmetic operations in Souffle-Datalog
(https://souffle-lang.github.io).

Current coverage:
 - 256-bit arithmetic (for crypto)

Dependencies:
 - Souffle: https://github.com/souffle-lang/souffle
 - Boost libraries
 - Z3: https://github.com/Z3Prover/z3

Functor compilation is rellying on the underlying word size of the installed `souffle` binary.
Due to that, our Makefile is parametrized via its `WORD_SIZE` parameter.
The `make WORD_SIZE=$(souffle --version | sed -n 3p | cut -c12,13)` command will build the functor with the correct word size (for latest `souffle` versions). 
Usage:

    $ make WORD_SIZE=32|64          # builds all, sets libfunctors.so as a link to libsoufflenum.so
    $ export LD_LIBRARY_PATH=`pwd`  # or wherever you want to put the resulting libfunctors.so

and use a Souffle program with the num256functors.dl definitions. For compiled execution, libfunctors.so (i.e., at least a
link to the real .so) should be in the compilation directory.

A sample Souffle client program can be found under directory dlexample.  
