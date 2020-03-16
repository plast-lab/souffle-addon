// Just a skeleton for meaningful test cases to be added later

#define BOOST_TEST_MODULE Mappings Tests
#include <boost/test/included/unit_test.hpp> 
#include <boost/multiprecision/cpp_int.hpp>
#include "mappings.cpp"  // shouldn't include .cpps, so ... sue me

using namespace boost::multiprecision;

BOOST_AUTO_TEST_CASE(test_simplenodup) {
	BOOST_TEST(
               singleton_mapping("x", "3", "three")
			   ==
               singleton_mapping("x", "3", "three"));
}

BOOST_AUTO_TEST_CASE(test_emptynodup) {
	BOOST_TEST(
               empty_mapping()
			   ==
               empty_mapping()
               );
}

BOOST_AUTO_TEST_CASE(test_complexnodup1) {
	BOOST_TEST(
               combine_strict(
                              singleton_mapping("x", "3", "three"),
                              singleton_mapping("z", "8", "eight"))
			   ==
               combine_strict(
                              singleton_mapping("z", "8", "eight"),
                              singleton_mapping("x", "3", "three"))
               );
}

BOOST_AUTO_TEST_CASE(test_complexnodup2) {
	BOOST_TEST(
               combine_strict(singleton_mapping("y", "87", "eighty-seven"),
                              combine_strict(
                                             singleton_mapping("x", "3", "three"),
                                             singleton_mapping("z", "8", "eight")))
			   ==
               combine_strict(combine_strict(
                                             singleton_mapping("z", "8", "eight"),
                                             singleton_mapping("x", "3", "three")
                                             ),
                              singleton_mapping("y", "87", "eighty-seven"))
               );
}

BOOST_AUTO_TEST_CASE(test_simplenoconflict) {
	BOOST_TEST(
               combine_strict(singleton_mapping("x", "3", "three"),
                              singleton_mapping("y", "4", "four"))
			   !=
               0);
}

BOOST_AUTO_TEST_CASE(test_simplenoconflict2) {
	BOOST_TEST(
               combine_strict(singleton_mapping("x", "3", "three"),
                              singleton_mapping("x", "3", "three"))
			   !=
               0);
}

BOOST_AUTO_TEST_CASE(test_simpleconflict) {
	BOOST_TEST(
               combine_strict(singleton_mapping("x", "3", "three"),
                              singleton_mapping("x", "4", "four"))
			   ==
               0);
}

BOOST_AUTO_TEST_CASE(test_zeros_tolerated) {
	BOOST_TEST(
               combine_strict(combine_strict(singleton_mapping("x", "3", "three"),
                                             singleton_mapping("x", "4", "four")),
                              singleton_mapping("y", "8", "eight"))
			   ==
               0);
}

BOOST_AUTO_TEST_CASE(test_count_bits) {
	BOOST_TEST(
                   uint256::from_uint_64(0x10001000).count_bits()
			   ==
               2);
}

BOOST_AUTO_TEST_CASE(test_hash_simple) {
	BOOST_TEST(
                   uint256::from_uint_64(0x10001000).hash()
			   ==
               0x10001000);
}


BOOST_AUTO_TEST_CASE(test_hash_complex) {
	BOOST_TEST(
                   (uint256::from_onehot(1)   |
                    uint256::from_onehot(64)  |
                    uint256::from_onehot(128) |
                    uint256::from_onehot(130)).hash()
			   ==
               0b110);
}


BOOST_AUTO_TEST_CASE(test_empty_works_simple) {
	BOOST_TEST(
               combine_strict(combine_strict(singleton_mapping("x", "3", "three"),
                                             empty_mapping()),
                              empty_mapping())
			   ==
               singleton_mapping("x", "3", "three"));
}

BOOST_AUTO_TEST_CASE(test_complexnoconflict1) {
	BOOST_TEST(
               combine_strict(
                              combine_strict(singleton_mapping("b", "87", "eighty-seven"),
                                             combine_strict(
                                                            singleton_mapping("x", "3", "three"),
                                                            singleton_mapping("y", "8", "eight"))),
                              combine_strict(combine_strict(
                                                            singleton_mapping("a", "8", "eight"),
                                                            singleton_mapping("f", "asd", "asd")
                                                            ),
                                             singleton_mapping("c", "2", "two")))
               !=
               0
               );
}

BOOST_AUTO_TEST_CASE(test_complexnoconflict2) {
	BOOST_TEST(
               combine_strict(
                              combine_strict(singleton_mapping("b", "87", "eighty-seven"),
                                             combine_strict(
                                                            singleton_mapping("x", "3", "three"),
                                                            singleton_mapping("y", "8", "eight"))),
                              combine_strict(combine_strict(
                                                            singleton_mapping("a", "8", "eight"),
                                                            singleton_mapping("f", "asd", "asd")
                                                            ),
                                             singleton_mapping("x", "3", "three")))
               !=
               0
               );
}

BOOST_AUTO_TEST_CASE(test_complexconflict1) {
	BOOST_TEST(
               combine_strict(
                              combine_strict(singleton_mapping("b", "87", "eighty-seven"),
                                             combine_strict(
                                                            singleton_mapping("x", "3", "three"),
                                                            singleton_mapping("y", "8", "eight"))),
                              combine_strict(combine_strict(
                                                            singleton_mapping("a", "8", "eight"),
                                                            singleton_mapping("b", "asd", "asd")
                                                            ),
                                             singleton_mapping("c", "2", "two")))
               ==
               0
               );
}

BOOST_AUTO_TEST_CASE(test_complexconflict2) {
	BOOST_TEST(
               combine_strict(
                              combine_strict(singleton_mapping("b", "87", "eighty-seven"),
                                             combine_strict(
                                                            singleton_mapping("x", "3", "three"),
                                                            singleton_mapping("y", "8", "eight"))),
                              combine_strict(combine_strict(
                                                            singleton_mapping("a", "8", "eight"),
                                                            singleton_mapping("f", "asd", "asd")
                                                            ),
                                             singleton_mapping("x", "2", "two")))
               ==
               0
               );
}

BOOST_AUTO_TEST_CASE(test_simpleloose) {
	BOOST_TEST(
               combine_loose(
                              singleton_mapping("x", "3", "three"),
                              singleton_mapping("x", "3", "three"))
               ==
               singleton_mapping("x", "3", "three")
               );
}



