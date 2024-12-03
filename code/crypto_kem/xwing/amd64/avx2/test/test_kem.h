#ifndef CRYPTO_KEM_H
#define CRYPTO_KEM_H

#include <stdint.h>

#define MLKEM_PUBLICKEYBYTES            1184
#define MLKEM_SECRETKEYBYTES            2400
#define MLKEM_CIPHERTEXTBYTES           1088
#define MLKEM_SYMBYTES                  32
#define X25519_BYTES                    32 
#define XWING_BYTES                     32 
#define XWING_LABEL_BYTES               6 
#define XWING_SEEDBYTES                 32
#define XWING_PUBLICKEYBYTES            MLKEM_PUBLICKEYBYTES  + X25519_BYTES
#define XWING_SECRETKEYBYTES            XWING_SEEDBYTES 
#define XWING_EXPANDED_SECRETKEYBYTES   MLKEM_SECRETKEYBYTES + X25519_BYTES
#define XWING_CIPHERTEXTBYTES           MLKEM_CIPHERTEXTBYTES + X25519_BYTES
#define XWING_EXPANDED_SEEDBYTES        XWING_SEEDBYTES + XWING_SEEDBYTES + XWING_SEEDBYTES
#define XWING_ENC_SEEDBYTES             XWING_SEEDBYTES + XWING_SEEDBYTES
#define XWING_HASH_INPUTBYTES           MLKEM_SYMBYTES + X25519_BYTES + X25519_BYTES + X25519_BYTES


void jade_kem_xwing_xwing_amd64_avx2_keypair_derand(
                         unsigned char *pk,
                         unsigned char *sk,
                         const unsigned char *randomness);

void jade_kem_xwing_xwing_amd64_avx2_enc_derand(unsigned char *c,
                     const unsigned char *m,
                     const unsigned char *pk,
                     const unsigned char *coins);


void jade_kem_xwing_xwing_amd64_avx2_dec(unsigned char *m,
                     const unsigned char *c,
                     const unsigned char *sk);



#endif
