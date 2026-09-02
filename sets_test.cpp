#define BOOST_TEST_MODULE SET Tests
#include <boost/test/included/unit_test.hpp> 

#include "sets.cpp"

BOOST_AUTO_TEST_CASE(test_len_empty) {
    BOOST_TEST(
        len_set(empty_set())
        ==
        0
    );
}