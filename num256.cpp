#include <string.h>
#include <boost/multiprecision/cpp_int.hpp>
#include <iostream>

using namespace boost::multiprecision;

#define STRING_LEN 67 // 2 (for "0x") + 1 (for '\0') + 64 bytes for
					  // the 32 bytes of data encoded in hex


extern "C" {

// Output always normalized to have:
// - "0x" as prefix
// - lower case letters for the hex digits (a-f)
// - no leading zeros (i.e., "0xff", not "0x000ff")

	// REVIEW: Lots of repetition, factor out in the future
	
	const char* add_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x + my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* sub_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x - my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* mul_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x * my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* div_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x / my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* mod_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x % my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}
	
	const char* and_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x & my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}
	
	const char* or_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x | my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* xor_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x ^ my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* gt_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x > my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* eq_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x == my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}
	
	const char* lt_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = my_x < my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	// Note use of max 256 int for modulo base
	const char* exp_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(x);
		uint256_t my_y(y);
		uint256_t result = powm(my_x, my_y, std::numeric_limits<uint256_t>::max());
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	// The next operations are for signed arithmetic, otherwise
	// identical to above.  Note the need to transform the result to
	// an unsigned int before converting to hex, since hex-conversion
	// for negative numbers is not supported by the Boost
	// multiprecision library.
	const char* smod_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		int256_t my_x(x);
		int256_t my_y(y);
		int256_t result = my_x % my_y;
		uint256_t unsigned_result(result);
		std::string str_result = unsigned_result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* sdiv_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		int256_t my_x(x);
		int256_t my_y(y);
		int256_t result = my_x / my_y;
		uint256_t unsigned_result(result);
		std::string str_result = unsigned_result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* sgt_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		int256_t my_x(x);
		int256_t my_y(y);
		int256_t result = my_x > my_y;
		uint256_t unsigned_result(result);
		std::string str_result = unsigned_result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	const char* slt_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		int256_t my_x(x);
		int256_t my_y(y);
		int256_t result = my_x < my_y;
		uint256_t unsigned_result(result);
		std::string str_result = unsigned_result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	/// Bitwise operations, per EIP-145
	// NOTE: INVERTED ARGUMENT ORDER!
	const char* shl_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(y);
		long my_y = strtol(x, NULL, 16);
		uint256_t result = my_x << my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	// NOTE: INVERTED ARGUMENT ORDER!
	const char* shr_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"}; 
		uint256_t my_x(y);
		long my_y = strtol(x, NULL, 16);
		uint256_t result = my_x >> my_y;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}

	// NOTE: INVERTED ARGUMENT ORDER!
	const char* sar_256(const char *x, const char *y) {
		thread_local static char out[STRING_LEN] = {"0x"};
		int256_t my_x(y);
		int256_t minus_zero = ((int256_t) 1) << 255;
		int256_t sign_bit = my_x & minus_zero;
		long my_y = strtol(x, NULL, 16);
		int256_t result;
		if (my_y >= 256) {
			if (sign_bit) result = -1;
			else result = 0;
		} else {  // there must be a better way to implement SAR w/ Boost, but who cares?
			for (result = my_x; my_y > 0; my_y--) {
				result = (result >> 1) | sign_bit;
			}
		}
		uint256_t unsigned_result(result);
		std::string str_result = unsigned_result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}
	
	const char* not_256(const char *x) {
		thread_local static char out[STRING_LEN] = {"0x"};
		uint256_t my_x(x);
		uint256_t result = ~my_x;
		std::string str_result = result.str(32, std::ios_base::hex);
		std::transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
		strcpy(out+2, str_result.c_str());
		return out;
	}
}


