/* Stub <inttypes.h>: Clang's resource-directory inttypes.h does an #include_next that the freestanding
   build cannot satisfy; the vendored openssl/e_os2.h only needs the <stdint.h> types. Not upstream. */
#ifndef SSL_STUB_INTTYPES_H
#define SSL_STUB_INTTYPES_H
#include <stdint.h>
#endif
