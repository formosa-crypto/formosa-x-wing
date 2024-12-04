#include <stdio.h>
#include <stdio.h>
#include "test_vectors.h"
#include "test_kem.h"

int main(void)
{
  unsigned char sk0[XWING_SECRETKEYBYTES];  
  unsigned char pk0[XWING_PUBLICKEYBYTES];  
  unsigned char ct0[XWING_CIPHERTEXTBYTES];  
  unsigned char shk0[XWING_BYTES];
  unsigned char shk1[XWING_BYTES];
  int ss_ok = 0;
  int pk_ok = 0;
  int ct_ok = 0;
  
  unsigned char randomness0[MLKEM_SYMBYTES];
  unsigned char randomness1[2*MLKEM_SYMBYTES];
  
  FILE *urandom = fopen("/dev/urandom", "r");
  fread(randomness0, 32, 1, urandom);
  fread(randomness1, 64, 1, urandom);
  fclose(urandom);
   
  jade_kem_xwing_xwing_amd64_avx2_keypair_derand(pk0, sk0, XWING_SEED_TEST_VECTOR);
    
  for(int i = 0; i < XWING_PUBLICKEYBYTES; i++) {
    if (pk0[i] != XWING_PUBLICKEY_TEST_VECTOR[i]) {
      printf("error crypto_kem_keypair pk: %d %d %d\n", i, pk0[i], XWING_PUBLICKEY_TEST_VECTOR[i]);    
      pk_ok = 1;
    }
  }


 if(pk_ok == 0) printf("pk ok!\n\n");
 if(pk_ok == 1) printf("\npk BAD!\n\n");
  
  jade_kem_xwing_xwing_amd64_avx2_enc_derand(ct0, shk0, XWING_PUBLICKEY_TEST_VECTOR, XWING_ESEED_TEST_VECTOR);

  for(int i = 0; i < XWING_CIPHERTEXTBYTES; i++) {
    if (ct0[i] != XWING_CIPHERTEXT_TEST_VECTOR[i]) {
      printf("error crypto_kem_enc ct: %d %d %d\n", i, ct0[i], XWING_CIPHERTEXT_TEST_VECTOR[i]);
      ct_ok = 1;
    }
  }
        
  if(ct_ok == 0) printf("ct ok!\n\n");
  if(ct_ok == 1) printf("\nct BAD!\n\n");
  
  for(int i = 0; i < XWING_BYTES; i++) {
    if (shk0[i] != XWING_SHAREDSECRET_TEST_VECTOR[i]) {
      printf("error crypto_kem_enc ss: %d %d %d\n", i, shk0[i], XWING_SHAREDSECRET_TEST_VECTOR[i]);    
      ss_ok = 1;    
    }
  }
      
  if(ss_ok == 0) printf("ss (decaps) ok!\n\n");
  if(ss_ok == 1) printf("\nss (decaps) BAD!\n\n");


  jade_kem_xwing_xwing_amd64_avx2_dec(shk1, ct0, sk0);

  for(int i = 0; i < XWING_BYTES; i++) {
    if (shk1[i] != shk0[i]) {
      printf("error crypto_kem_dec: %d %d %d\n", i, shk1[i], shk0[i]);
      ss_ok = 1; 
    }   
  }
  
  if(ss_ok == 0) printf("ss decaps = ss encaps ok!\n\n");
  if(ss_ok == 1) printf("ss decaps != ss encaps ok BAD!\n\n");
  
  //for(int i = 0; i < XWING_BYTES; i++) {
  //  if (shk1[i] != XWING_SHAREDSECRET_TEST_VECTOR[i]) {
  //    printf("error crypto_kem_dec: %d %d %d\n", i, shk1[i], XWING_SHAREDSECRET_TEST_VECTOR[i]);
  //    ss2_ok = 1; 
  //  }   
  //}
  
  // if(ss2_ok == 0) printf("ss2 ok!\n\n");
  // if(ss2_ok == 1) printf("\nss2 BAD!\n\n");

  return 0;
}
