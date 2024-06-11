#include <boost/multiprecision/cpp_int.hpp>
#include <boost/algorithm/hex.hpp>
#include <string.h>

using namespace boost::multiprecision;
using namespace std;

char num_to_hex(char num) {
    return num < 10 ? num + '0' : (num - 10) + 'a';
}

char hex_to_num(char hex_char) {
    return hex_char <= '9' ? hex_char - '0' : (hex_char - 'a') + 10;
}

extern "C"
{
  #include "keccak/KeccakHash.h"
  const char* keccak_256(const char* input) {
    thread_local static char out_str[67] = {"0x"};
    thread_local static char out[32] = {0};

    Keccak_HashInstance hi;
    Keccak_HashInitialize(&hi, 1088, 512, 256, 0x01);
    Keccak_HashUpdate(&hi, (const unsigned char*)input, strlen(input) * 8);
    Keccak_HashFinal(&hi, (unsigned char*)out);

    // this part is needed to normalize the hexadecimal output
    string str_result;
    boost::algorithm::hex(out, out + 32, std::back_inserter(str_result));
    transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
    str_result.erase(0, str_result.find_first_not_of('0'));
    strcpy(out_str+2, str_result.c_str());;
  
    return out_str;
  }

  const char* hex_keccak_256(const char* input) {
    thread_local static char out_str[67] = {"0x"};
    thread_local static char out[32] = {};

    const size_t input_len = strlen(input);
    const size_t input_byte_len = input_len/2 - 1;

    char* input_bytes = (char*) malloc(sizeof(char) * input_byte_len);

    for (size_t i = 0; i < input_byte_len; ++i)
        input_bytes[i] = (hex_to_num(input[2 + 2*i]) << 4) + hex_to_num(input[2 + 2*i + 1]);

    Keccak_HashInstance hi;
    Keccak_HashInitialize(&hi, 1088, 512, 256, 0x01);
    Keccak_HashUpdate(&hi, (const unsigned char*)input_bytes, input_byte_len * 8);
    Keccak_HashFinal(&hi, (unsigned char*)out);

    free(input_bytes);
    // this part is needed to normalize the hexadecimal output
    string str_result;
    boost::algorithm::hex(out, out + 32, std::back_inserter(str_result));
    transform(str_result.begin(), str_result.end(), str_result.begin(), ::tolower);
    str_result.erase(0, str_result.find_first_not_of('0'));
    strcpy(out_str+2, str_result.c_str());;
  
    return out_str;
  }

  const char* hex_to_str(const char* input) {
    thread_local static char* out = (char*) malloc(sizeof(char) * (strlen(input)/2));

    for (int i = 1; i < strlen(input)/2; i++){
        out[i - 1] = hex_to_num(input[2*i])*16 + hex_to_num(input[2*i + 1]);
    }
    out[strlen(input)/2 - 1] = '\0';

    return out;
  }
}
