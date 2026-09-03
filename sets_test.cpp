#define BOOST_TEST_MODULE SET Tests
#include <boost/test/included/unit_test.hpp> 

#include "sets.cpp"

// Copy a functor result immediately. Needed because add_set/union_set/
// set_to_string each return a pointer into their own thread_local buffer,
// which the *next call to that same function* overwrites. Not copying and
// then comparing two such results via set_eq gives a vacuous pass.
static std::string S(const char* p) { return std::string(p); }


BOOST_AUTO_TEST_CASE(test_len_empty) {
    BOOST_TEST(len_set(empty_set()) == 0);
}

BOOST_AUTO_TEST_CASE(test_in_empty_is_false) {
    BOOST_TEST(in_set(empty_set(), "x") == 0);
}

BOOST_AUTO_TEST_CASE(test_empty_is_stable) {
    BOOST_TEST(set_eq(empty_set(), empty_set()) == 1);
}

BOOST_AUTO_TEST_CASE(test_to_string_empty) {
    BOOST_TEST(set_to_string(empty_set()) == "{}");
}

// --- single insertion -----------------------------------------------------
BOOST_AUTO_TEST_CASE(test_add_one) {
    const char* s = add_set(empty_set(), "x");
    BOOST_TEST(len_set(s) == 1);
    BOOST_TEST(in_set(s, "x") == 1);
    BOOST_TEST(in_set(s, "y") == 0);
    BOOST_TEST(set_to_string(s) == "{x}");
}

BOOST_AUTO_TEST_CASE(test_add_does_not_mutate_original) {
    const char* empty = empty_set();
    const char* s = add_set(empty, "x");
    BOOST_TEST(len_set(empty) == 0);
    BOOST_TEST(len_set(s) == 1);
}

// --- cases that genuinely require copies -----------------------------------

BOOST_AUTO_TEST_CASE(test_add_duplicate_is_idempotent) {
    std::string s1 = S(add_set(empty_set(), "x")); // copy: next add_set clobbers
    std::string s2 = S(add_set(s1.c_str(), "x"));  // adding "x" again
    BOOST_TEST(len_set(s2.c_str()) == 1);
    BOOST_TEST(set_eq(s1.c_str(), s2.c_str()) == 1);
}

BOOST_AUTO_TEST_CASE(test_insertion_order_independence) {
    std::string ab = S(add_set(add_set(empty_set(), "a"), "b"));
    std::string ba = S(add_set(add_set(empty_set(), "b"), "a"));
    BOOST_TEST(set_eq(ab.c_str(), ba.c_str()) == 1);
    BOOST_TEST(len_set(ab.c_str()) == 2);
}

BOOST_AUTO_TEST_CASE(test_set_eq_distinguishes_different_sets) {
    std::string a = S(add_set(empty_set(), "a"));
    std::string b = S(add_set(empty_set(), "b"));
    BOOST_TEST(set_eq(a.c_str(), b.c_str()) == 0);
    BOOST_TEST(set_eq(a.c_str(), empty_set()) == 0);
}

BOOST_AUTO_TEST_CASE(test_add_two_membership) {
    // Nested single expression is safe without a copy: the inner add_set
    // result is consumed by the outer call before the buffer is reused.
    const char* s = add_set(add_set(empty_set(), "a"), "b");
    BOOST_TEST(len_set(s) == 2);
    BOOST_TEST(in_set(s, "a") == 1);
    BOOST_TEST(in_set(s, "b") == 1);
    BOOST_TEST(in_set(s, "c") == 0);
}

// --- union ----------------------------------------------------------------

BOOST_AUTO_TEST_CASE(test_union_basic) {
    std::string a = S(add_set(empty_set(), "a"));
    std::string b = S(add_set(empty_set(), "b"));
    const char* u = union_set(a.c_str(), b.c_str()); // union_set: own buffer
    BOOST_TEST(len_set(u) == 2);
    BOOST_TEST(in_set(u, "a") == 1);
    BOOST_TEST(in_set(u, "b") == 1);
}

BOOST_AUTO_TEST_CASE(test_union_with_empty_is_identity) {
    std::string a = S(add_set(empty_set(), "a"));
    std::string u = S(union_set(a.c_str(), empty_set()));
    BOOST_TEST(set_eq(a.c_str(), u.c_str()) == 1);
}

BOOST_AUTO_TEST_CASE(test_union_equals_sequential_adds) {
    std::string a  = S(add_set(empty_set(), "a"));
    std::string b  = S(add_set(empty_set(), "b"));
    std::string u  = S(union_set(a.c_str(), b.c_str()));
    std::string ab = S(add_set(add_set(empty_set(), "a"), "b"));
    BOOST_TEST(set_eq(u.c_str(), ab.c_str()) == 1); // union == sequential inserts
}

// --- robustness / bad handles ---------------------------------------------

BOOST_AUTO_TEST_CASE(test_bad_handle_queries) {
    BOOST_TEST(in_set("garbage", "x") == 0);
    BOOST_TEST(len_set("garbage") == 0);
    BOOST_TEST(in_set("S999999", "x") == 0); // well-formed but out of range
    BOOST_TEST(len_set("S999999") == 0);
    BOOST_TEST(set_eq("garbage", "garbage") == 0); // bad handles never equal
    BOOST_TEST(set_to_string("garbage") == "{}");
}

BOOST_AUTO_TEST_CASE(test_to_string_multi_contains_members) {
    std::string s = S(add_set(add_set(empty_set(), "a"), "b"));
    std::string str = S(set_to_string(s.c_str()));
    BOOST_TEST(str.find("a") != std::string::npos);
    BOOST_TEST(str.find("b") != std::string::npos);
}