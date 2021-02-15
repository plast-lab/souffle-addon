#define BOOST_TEST_MODULE Keccak Tests
#include <boost/test/included/unit_test.hpp> 

#include "keccak256.cpp"

BOOST_AUTO_TEST_CASE(test_hash_empty) {
	BOOST_TEST(
        keccak_256("")
	    ==
	    "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
}

BOOST_AUTO_TEST_CASE(test_hash_simple) {
	BOOST_TEST(
        keccak_256("hi")
	    ==
	    "0x7624778dedc75f8b322b9fa1632a610d40b85e106c7d9bf0e743a9ce291b9c6f"
    );
}

BOOST_AUTO_TEST_CASE(test_hash_signature) {
	BOOST_TEST(
        keccak_256("transfer(address,uint256)")
	    ==
	    "0xa9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"
    );
}
