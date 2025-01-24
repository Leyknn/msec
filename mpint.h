#ifndef MPINT_H
#define MPINT_H

#include <stdint.h>

/* #define DEBUG */
#define WORD 32

#if WORD == 8
#define UINT uint8_t
#define MASK_FULL 0xff
#define MASK_LOW_HALF 0x0f
#define MASK_HIGH_HALF 0xf0
#define HALF 4
#elif WORD == 16
#define UINT uint16_t
#define MASK_FULL 0xffff
#define MASK_LOW_HALF 0x00ff
#define MASK_HIGH_HALF 0xff00
#define HALF 8
#elif WORD == 32
#define UINT uint32_t
#define MASK_FULL 0xffffffff
#define MASK_LOW_HALF 0x0000ffff
#define MASK_HIGH_HALF 0xffff0000
#define HALF 16
#elif WORD == 64
#define UINT uint64_t
#define MASK_FULL 0xffffffffffffffff
#define MASK_LOW_HALF 0x00000000ffffffff
#define MASK_HIGH_HALF 0xffffffff00000000
#define HALF 32
#endif

#define MPINTMAXSIZE 33
/* with 9, one can deal with 256 bits, with 8 words of 32 bits + one extra word */
#define ZPOS 0 /* sign is zero or positive */
#define NEG -1 /* sign is negative */

/* return codes for mpint_cmp comparison */
#define MPINT_EQ 0 /* a equals b */
#define MPINT_GT 1 /* a greater than b */
#define MPINT_LT -1 /* a less than b */

/* to be compatible with the statements such as if(something true) which returns 1 */
#define TRUE 1
#define FALSE 0

/* to be compatible with the error return code of Makefile being anything non-zero */
#define OK 0
#define KO 1

/* more specific error code return */
/* arbitrary number, just be sure to put something different than the other macros OK and KO above */

#define ERROR_IN_PLACE_NOT_POSSIBLE 15
#define ERROR_CARRY_OVERFLOW 16
#define ERROR_ABOVE_MPINTMAXSIZE 17
#define ERROR_FORMAT 18
#define ERROR_INPUT_NOT_REDUCED 19
#define ERROR_DIVISION_BY_ZERO 20
#define ERROR_INPUT 21

typedef struct {
  int used;
  int sign;
  UINT limbs[MPINTMAXSIZE];
}mpint;

typedef mpint mpint_t[1];  /* an array of size 1 to ease argument passing in functions */
typedef mpint * mpint_ptr; /* a pointer to a mpint, needed for example in testing with test vectors */
/* this idea of two types is directly inspired from mpz_t and mpz_ptr in GMP */

int mpint_set_zero(mpint_t a);
int mpint_is_zero(mpint_t a);
int mpint_set_one(mpint_t a);
int mpint_is_one(mpint_t a);

/* TP 1 */
int mpint_cmp_mgn(mpint_t a, mpint_t b);
int mpint_cmp(mpint_t a, mpint_t b);
int mpint_add_mgn(mpint_t r, mpint_t a, mpint_t b);
int mpint_add(mpint_t r, mpint_t a, mpint_t b);
int mpint_sub_mgn(mpint_t r, mpint_t a, mpint_t b);
int mpint_sub(mpint_t r, mpint_t a, mpint_t b);

/* TP 2 */
int uint_mul(UINT * rlow, UINT * rhigh, UINT a, UINT b);
void mpint_recompute_used(mpint_t r);
int mpint_mul_mgn(mpint_t r, mpint_t a, mpint_t b);
int mpint_mul(mpint_t r, mpint_t a, mpint_t b);

/* TP 3 */
/* either a deep copy function of addition, subtraction in place are needed */
int mpint_deep_copy(mpint_t r, mpint_t a);
int modint_add(mpint_t r, mpint_t m, mpint_t a, mpint_t b);
int modint_sub(mpint_t r, mpint_t m, mpint_t a, mpint_t b);
int modint_neg(mpint_t r, mpint_t m, mpint_t a);
int mpint_word_mul_mgn(mpint_t r, mpint_t a);
int mpint_word_div_mgn(mpint_t r, mpint_t a);
int mpint_uint_mul_mgn(mpint_t r, UINT u, mpint_t a);

/* TP 4 */
int mpint_add_mgn_inplace(mpint_t r, mpint_t a);/* r <- r + a */
int mpint_sub_mgn_inplace(mpint_t r, mpint_t a);/* r <- r - a */
int modint_mul(mpint_t r, mpint_t a, mpint_t b, mpint_t m, UINT m_prime);

/* TP 5 */
int mpint_dbl_mgn(mpint_t a);
int modint_exp_mpint(mpint_t r, mpint_t a, mpint_t e, mpint_t m, UINT m_prime);

/* TP 6 */
void mpint_adjust_size_used(mpint_t a);/* given */
int uint_div(UINT *q1, UINT *q0, UINT *r0, UINT a1, UINT a0, UINT b0); /* given */
int mpint_div_uint(mpint_t q, UINT *r, mpint_t a, UINT b);/* given */
int uint_gcd(UINT *r, UINT a, UINT b);
int mpint_gcd_uint(UINT *r, mpint_t a, UINT b);
int mpint_add_uint_mgn_inplace(mpint_t r, UINT a);
#ifdef DEBUG
int mpint_div_mgn(mpint_t q, mpint_t r, mpint_t a, mpint_t b, int debug); /* given */
int mpint_gcd(mpint_t r, mpint_t a, mpint_t b, int debug); /* given */
int mpint_div(mpint_t q, mpint_t r, mpint_t a, mpint_t b, int debug); /* given */
#else
int mpint_div_mgn(mpint_t q, mpint_t r, mpint_t a, mpint_t b); /* given */
int mpint_gcd(mpint_t r, mpint_t a, mpint_t b); /* given */
int mpint_div(mpint_t q, mpint_t r, mpint_t a, mpint_t b); /* given */
#endif
int mpint_sub_mgn_inplace_swap(mpint_t r, mpint_t a);/* r <- a - r */
int mpint_sub_inplace(mpint_t r, mpint_t a);/* r <- r - a with sign */
int mpint_xgcd(mpint_t g, mpint_t u, mpint_t v, mpint_t a, mpint_t b); /* given */

/* below is not tested */
int modint_inv(mpint_t r, mpint_t a, mpint_t m);

/* int modint_inv_uint(mpint_t r, UINT a, mpint_t m); */
int modint_mod_to_montgomery(mpint_t r, mpint_t m);
int montgomery_m_prime(UINT *m_prime, mpint_t m);
int modint_montgomery_to_mod(mpint_t r, mpint_t m, UINT m_prime);
int mpint_montgomery_to_mod(mpint_t a, mpint_t m, mpint_t r_inv);
int montgomery_r_inv(mpint_t Rinv, mpint_t m);

/* random integers */
int mpint_rand_odd_given_bits(mpint_t r, int bits);

/* Primality tests */
#define ERROR_IS_EVEN 2
#define IS_PROBABLE_PRIME 3
#define IS_COMPOSITE 4
int mpint_is_even(mpint_t a);
int mpint_set_uint(mpint_t r, UINT a);
int mpint_div_pow_2_inplace(mpint_t r, int i);
#ifdef DEBUG
int mpint_is_prime_fermat(mpint_t a_n_1, UINT *a, mpint_t n);
#else
int mpint_is_prime_fermat(mpint_t n);
#endif
int mpint_is_prime_miller_rabin(mpint_t n);
int mpint_rand_prime_given_bits(mpint_t r, int bits);

/* print functions */
void uint_print_hexa(UINT a);
void uint_print_dec(UINT u);
void mpint_print_hexa(mpint_t a);
void mpint_print_dec(mpint_t a);

void mpint_print_str_hex(mpint_t a);
void mpint_println_str_hex(mpint_t a);


#endif
