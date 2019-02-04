// Just a skeleton for meaningful test cases to be added later

#define BOOST_TEST_MODULE Num 256 Tests
#include <boost/test/included/unit_test.hpp> 

#include "num256.cpp"  // shouldn't include .cpps, so ... sue me

BOOST_AUTO_TEST_CASE(test_add) {
	BOOST_TEST(
			   add_256("0xd323232323232323232323232323232dd323232323232323232323232323232d",
					   "0x1111111111111111111111111111111111111111111111111111111111111111")
			   ==
			   "0xe434343434343434343434343434343ee434343434343434343434343434343e");
	BOOST_TEST(
			   add_256("0xeff23",
					   "0xfe")
			   ==
			   "0xf0021");
}

BOOST_AUTO_TEST_CASE(test_sub) {
	BOOST_TEST(
			   sub_256("0xd323232323232323232323232323232dd323232323232323232323232323232d",
					   "0x1111111111111111111111111111111111111111111111111111111111111111")
			   ==
			   "0xc212121212121212121212121212121cc212121212121212121212121212121c");
}

BOOST_AUTO_TEST_CASE(test_exp) {
	BOOST_TEST(
			   exp_256("0x666f",
					   "0x3")
			   ==
			   "0x10666ef0504f");
	BOOST_TEST(
			   exp_256("0x666f",
					   "0x3ff")
			   ==
			   "0x103691d9c197615a89b9b351f6122823614a541f92725975095e5f7f28a3f4f9");
	// no clue if the latter is correct, but at least it has the right number of digits
}

// unit tests from EIP
BOOST_AUTO_TEST_CASE(test_shl) {
	BOOST_TEST(
			   shl_256("0x0",
					   "0x0000000000000000000000000000000000000000000000000000000000000001")
			   ==
			   "0x1");
	BOOST_TEST(
			   shl_256("0x1",
					   "0x0000000000000000000000000000000000000000000000000000000000000001")
			   ==
			   "0x2");
}


