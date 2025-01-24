#ifndef RSA
#define RSA

#include "mpint.h"

typedef struct {
  mpint_t e;
  mpint_t N;
} pk;

typedef pk pk_t[1];

typedef struct {
  mpint_t d;
  mpint_t N;
} sk;

typedef sk sk_t[1];

typedef struct {
  pk_t pk;
  sk_t sk;
} keypair;

typedef keypair keypair_t[1];

#define OK 0
#define KO 1

static mpint_t e = {{1, ZPOS, {0x10001}}};

int generate_key_pair_given_bits(keypair_t r, int bits);
int encrypt(mpint_t ciphertext, mpint_t plaintext, pk_t pk);
int decrypt(mpint_t plaintext, mpint_t ciphertext, sk_t sk);

void print_pk(pk_t pk);
void print_sk(sk_t sk);
void print_keypair(keypair_t keypair);

#endif
