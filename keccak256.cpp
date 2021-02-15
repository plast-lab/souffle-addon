#include <boost/multiprecision/cpp_int.hpp>
#include <string.h>

using namespace boost::multiprecision;
using namespace std;

char num_to_hex(char num) {
    return num < 10 ? num + '0' : (num - 10) + 'a';
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

    for (int i = 0; i < 32; ++i) {
        unsigned char c = out[i];
        out_str[2 + 2*i]     = num_to_hex(c >> 4);
        out_str[2 + 2*i + 1] = num_to_hex(c & 0x0f);
    }
  
    return out_str;
  }
}
