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

BOOST_AUTO_TEST_CASE(test_hex_to_str) {
	BOOST_TEST(
        hex_to_str("0x72656365697665417070726f76616c28616464726573732c75696e743235362c616464726573732c627974657329")
	    ==
	    "receiveApproval(address,uint256,address,bytes)"
    );
}

BOOST_AUTO_TEST_CASE(test_hash_hex_to_str) {
	BOOST_TEST(
        keccak_256(hex_to_str("0x7472616e7366657228616464726573732c75696e7432353629"))
	    ==
	    "0xa9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"
    );
}