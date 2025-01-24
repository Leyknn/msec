#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "mpint.h"

#include "rsa.h"


int generate_key_pair_given_bits(keypair_t r, int bits) {
  printf("Start key generation\n");
  mpint_t phi, one, p, q;
  mpint_rand_prime_given_bits(p, bits);
  mpint_rand_prime_given_bits(q, bits);
  printf("p and q have been generated\n");
  mpint_set_one(one);
  mpint_set_zero(r->pk->e);
  mpint_deep_copy(r->pk->e, e);
  printf("e has been set\n");
  mpint_mul(r->pk->N, p, q);
  mpint_deep_copy(r->sk->N, r->pk->N);
  printf("N has been set\n");
  mpint_sub_inplace(p, one);
  mpint_sub_inplace(q, one);
  mpint_mul(phi, p, q);
  modint_inv(r->sk->d, r->pk->e, phi);
  printf("d has been set\n");
  return OK;
}

int encrypt(mpint_t ciphertext, mpint_t plaintext, pk_t pk) {
  UINT N_prime;
  montgomery_m_prime(&N_prime, pk->N);

  mpint_t montgomery_plaintext;
  mpint_deep_copy(montgomery_plaintext, plaintext);

  modint_mod_to_montgomery(montgomery_plaintext, pk->N);
  modint_exp_mpint(ciphertext, montgomery_plaintext, pk->e, pk->N, N_prime);
  modint_montgomery_to_mod(ciphertext, pk->N, N_prime);

  return OK;
}

int decrypt(mpint_t plaintext, mpint_t ciphertext, sk_t sk) {
  UINT N_prime;
  montgomery_m_prime(&N_prime, sk->N);

  mpint_t montgomery_ciphertext;
  mpint_deep_copy(montgomery_ciphertext, ciphertext);

  modint_mod_to_montgomery(montgomery_ciphertext, sk->N);
  modint_exp_mpint(plaintext, montgomery_ciphertext, sk->d, sk->N, N_prime);
  modint_montgomery_to_mod(plaintext, sk->N, N_prime);

  return OK;
}

int verify(mpint_t ciphertext, mpint_t plaintext, pk_t pk) {
  UINT N_prime;
  montgomery_m_prime(&N_prime, pk->N);

  mpint_t montgomery_plaintext;
  mpint_deep_copy(montgomery_plaintext, plaintext);

  modint_mod_to_montgomery(montgomery_plaintext, pk->N);
  modint_exp_mpint(ciphertext, montgomery_plaintext, pk->e, pk->N, N_prime);
  modint_montgomery_to_mod(ciphertext, pk->N, N_prime);

  return OK;
}

int sign(mpint_t plaintext, mpint_t ciphertext, sk_t sk) {
  UINT N_prime;
  montgomery_m_prime(&N_prime, sk->N);

  mpint_t montgomery_ciphertext;
  mpint_deep_copy(montgomery_ciphertext, ciphertext);

  modint_mod_to_montgomery(montgomery_ciphertext, sk->N);
  modint_exp_mpint(plaintext, montgomery_ciphertext, sk->d, sk->N, N_prime);
  modint_montgomery_to_mod(plaintext, sk->N, N_prime);

  return OK;
}

void print_pk(pk_t pk) {
  printf("\npublic key:");
  printf("\n\te: ");
  mpint_print_str_hex(pk->e);
  printf("\n\tN: ");
  mpint_print_str_hex(pk->N);
}

void print_sk(sk_t sk) {
  printf("\nsecret key:");
  printf("\n\td: ");
  mpint_print_str_hex(sk->d);
  printf("\n\tN: ");
  mpint_print_str_hex(sk->N);
}

void print_keypair(keypair_t keypair) {
  printf("\nKey pair:");
  print_pk(keypair->pk);
  print_sk(keypair->sk);
  printf("\n");
}

int test_encrypt() {
  mpint_t plaintext, _plaintext, ciphertext;
  keypair_t keypair;

  int bitsize = 128;

  time_t begin = time(NULL);
  generate_key_pair_given_bits(keypair, bitsize);
  time_t end = time(NULL);
  printf("time : %lds", (end - begin));
  print_keypair(keypair);

  mpint_set_zero(plaintext);
  mpint_rand_odd_given_bits(plaintext, 2*bitsize-1);

  encrypt(ciphertext, plaintext, keypair->pk);

  decrypt(_plaintext, ciphertext, keypair->sk);


  if (mpint_cmp(plaintext,_plaintext)) {
    printf("\n! both plaintext are differents !\n");
    printf("original:\n\t");
    mpint_println_str_hex(plaintext);
    printf("\ndecrypted:\n\t");
    mpint_println_str_hex(_plaintext);
    return KO;
  }
  return OK;
}

int test_sign() {
  mpint_t plaintext, _plaintext, ciphertext;
  keypair_t keypair;

  int bitsize = 128;

  time_t begin = time(NULL);
  generate_key_pair_given_bits(keypair, bitsize);
  time_t end = time(NULL);
  printf("time : %lds", (end - begin));
  print_keypair(keypair);

  mpint_set_zero(plaintext);
  mpint_rand_odd_given_bits(plaintext, 2*bitsize-1);

  sign(ciphertext, plaintext, keypair->sk);

  verify(_plaintext, ciphertext, keypair->pk);


  if (mpint_cmp(plaintext,_plaintext)) {
    printf("\n! both plaintext are differents !\n");
    printf("original:\n\t");
    mpint_println_str_hex(plaintext);
    printf("\ndecrypted:\n\t");
    mpint_println_str_hex(_plaintext);
    return KO;
  }
  return OK;
}

int main() {
  srand(time(NULL));
  int res = 0;
  for (int i = 0; i<100; i++) {
    res += test_sign();
  }
  return res;
}