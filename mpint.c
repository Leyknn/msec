#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "mpint.h"

#define MAX(i, j) (((i) > (j)) ? (i) : (j))

int mpint_set_zero(mpint_t a){
  /* set mpint to zero, in place
   * [in,out] mpint_t a: to be set to zero
   * [out] return: error code OK
   * set all the limbs of a to zero, set the length of a to 1,
   * set the sign to ZPOS
   */
  int i;
  a->used = 1;
  for(i = 0; i < MPINTMAXSIZE; i++){
    a->limbs[i] = 0;
  }
  a->sign = ZPOS;
  return OK;
}

int mpint_is_zero(mpint_t a){
  /* test if a is zero
   * [in] mpint_t a: to be checked for being zero
   * [out] return: TRUE or FALSE
   */
  if ((a->sign == ZPOS) && (a->used == 1) && (a->limbs[0] == 0)) {
    return TRUE;
  }
  return FALSE;
}

int mpint_set_one(mpint_t a){
  /* set mpint to one, in place
   * [in,out] mpint_t a: to be set to one
   * [out] return: error code OK
   * set all the limbs of a to zero except the lowest to one,
   * set the length of a to 1
   * set the sign to ZPOS
   */
  int i;
  a->used = 1;
  a->limbs[0] = 1;
  for(i = 1; i < MPINTMAXSIZE; i++){
    a->limbs[i] = 0;
  }
  a->sign = ZPOS;
  return OK;
}

int mpint_is_one(mpint_t a){
  /* test if a is one
   * [in] mpint_t a: to be checked for being one
   * [out] return: TRUE or FALSE
   */
  if ((a->sign == ZPOS) && (a->used == 1) && (a->limbs[0] == 1)) {
    return TRUE;
  }
  return FALSE;
}

int mpint_add_mgn(mpint_t r, mpint_t a, mpint_t b){
  /* addition of the magnitudes (absolute values)
   * [in] mpint_t r: result where to store the new value
   * [in] mpint_t a: first operand
   * [in] mpint_t b: second operand
   * [out] return: an error code (OK, ERROR_CARRY_OVERFLOW)
   * add the absolute values of a and b (magnitudes) (no sign is checked)
   */
  int i, min, max;
  mpint_ptr l; /* pointer to the most long of a and b */
  UINT carry = 0; /* actually it is better to set carry to be a UINT like the limbs */
  /* first naive way */
  /* case with maximum values: all machine-words at 'ffffffff' + a carry */
  /* (2^32-1) + (2^32-1) + 1 = 2^33-1 and it fits in 33 bits */
  /* careful with the bound on i: should be the minimum of a->used and b->used */
  if (a->used <= b->used) {
    min = a->used;
    max = b->used;
    l = b; /* pointer to the largest one */
  } else {
    max = a->used;
    min = b->used;
    l = a;
  }
  r->limbs[0] = a->limbs[0] + b->limbs[0];
  if (r->limbs[0] < b->limbs[0]){
    carry = 1;
  }
  for (i = 1; i < min; i++){
    /* this code is wrong: it is false on the inputs
       a->limbs = {0xffffffff, 0x00000000}
       b->limbs = {0x00000001, 0xffffffff}
       because it does not detect the second carry overflow
    r->limbs[i] = a->limbs[i] + b->limbs[i] + carry;
    if (r->limbs[i] < a->limbs[i]) {
      carry = 1;
    }else{
      carry = 0;
    }
    */
    r->limbs[i] = b->limbs[i] + carry;
    carry = 0;
    if (r->limbs[i] < b->limbs[i]){
      carry = 1;
    }
    r->limbs[i] += a->limbs[i];
    if (r->limbs[i] < a->limbs[i]) {
      carry = 1;
    }
  }
  /* now from min to max: copy + add carry */
  for(i = min; i < max; i++){
    r->limbs[i] = l->limbs[i] + carry;
    carry = 0;
    if (r->limbs[i] < l->limbs[i]){
      carry = 1;
    }
  }
  i = max;
  /* now store the final carry if place */
  if ((carry != 0) && (max < MPINTMAXSIZE)){
    r->limbs[max] = 1;
    carry = 0;
    i = max+1;
  }
  /* recompute used */
  /* the number of used words of the result is at most the maximum of
     a->used and b->used, plus one in case there was a carry propagation */
  while((i > 1) && (r->limbs[i-1] == 0)){
    i--;
  }
  r->used = i;
  if (carry != 0) {
    return ERROR_CARRY_OVERFLOW;
  }
  return OK;
}

int mpint_sub_mgn(mpint_t r, mpint_t a, mpint_t b){
  /* subtraction of the magnitudes (absolute values)
   * [in] mpint_t r: result where to store the new value
   * [in] mpint_t a: first operand
   * [in] mpint_t b: second operand
   * [out] return: an error code (OK, ERROR_CARRY_OVERFLOW)
   * subtract the absolue value of b from a: r = |a| - |b|
   * assume |a| >= |b|
   */
  int i;
  /* assume |a| >= |b| and in particular, a->used >= b->used */
  UINT carry = 0;
  /* first naive way */
  for (i = 0; i < b->used; i++){
    /* in two steps is safer */
    /* r[i] = a[i]-b[i]-carry */
    r->limbs[i] = a->limbs[i] - carry;
    if ((a->limbs[i] >= carry) && (r->limbs[i] >= b->limbs[i])){
      carry = 0;
    }else{/* r[i] = 2^WORDSIZE + a[i] - b[i] - carry */
      carry = 1;
    }
    r->limbs[i] -= b->limbs[i];
  }
  /* now the limbs of a, assume the limbs of b are 0 */
  for (i = b->used; i < a->used; i++){
    /* r[i] = a[i]-carry */
    r->limbs[i] = a->limbs[i] - carry;
    if (a->limbs[i] >= carry){
      carry = 0;
    }else{/* r[i] = 2^WORDSIZE + a[i] - carry */
      carry = 1;
    }
  }  
  /* recompute used, knowing that a->used >= b->used */
  i = a->used;
  while((i > 1) && (r->limbs[i-1] == 0)){
    i--;
  }
  r->used = i;
  if (carry != 0) {
    return ERROR_CARRY_OVERFLOW;
  }
  return OK;
}

int mpint_add_mgn_inplace(mpint_t r, mpint_t a){
  /* addition of the magnitudes (absolute values)
   * [in,out] mpint_t r: 1st operand and result where to store the new value
   * [in] mpint_t a: second operand
   * [out] return: an error code (OK, ERROR_CARRY_OVERFLOW)
   * add the absolute values of r and a into r (magnitudes) (no sign is checked)
   */
  int i, min, max;
  mpint_ptr l; /* pointer to the most long of r and a */
  UINT carry = 0; /* actually it is better to set carry to be a UINT like the limbs */
  /* case with maximum values: all machine-words at 'ffffffff' + a carry */
  /* (2^32-1) + (2^32-1) + 1 = 2^33-1 and it fits in 33 bits */
  /* careful with the bound on i: should be the minimum of r->used and a->used */
  if (r->used < a->used) {
    min = r->used;
    max = a->used;
    l = a; /* pointer to the largest one */
  } else {
    max = r->used;
    min = a->used;
    l = r;
  }
  r->limbs[0] += a->limbs[0];
  if (r->limbs[0] < a->limbs[0]){
    carry = 1;
  }
  for (i = 1; i < min; i++){
    /* r[i] += a[i] + carry in two steps */
    r->limbs[i] += carry;
    if (r->limbs[i] < carry){
      carry = 1;
    } else {
      carry = 0;
    }
    r->limbs[i] += a->limbs[i];
    if (r->limbs[i] < a->limbs[i]) {
      carry = 1;
    }
  }
  /* now from min to max: copy + add carry */
  for(i = min; i < max; i++){
    r->limbs[i] = l->limbs[i] + carry;
    if (r->limbs[i] < carry){
      carry = 1;
    } else {
      carry = 0;
    }
  }
  i = max;
  /* now store the final carry if place */
  if ((carry != 0) && (max < MPINTMAXSIZE)){
    r->limbs[max] = 1;
    carry = 0;
    i = max+1;
  }
  /* recompute used */
  /* the number of used words of the result is at most the maximum of
     a->used and b->used, plus one in case there was a carry propagation */
  while((i > 1) && (r->limbs[i-1] == 0)){
    i--;
  }
  r->used = i;
  if (carry != 0) {
    return ERROR_CARRY_OVERFLOW;
  }
  return OK;
}

int mpint_sub_mgn_inplace(mpint_t r, mpint_t a){
  /* subtraction of the magnitudes (absolute values)
   * [in,out] mpint_t r: 1st operand and result where to store the new value
   * [in] mpint_t a: second operand
   * [out] return: an error code (OK, ERROR_CARRY_OVERFLOW)
   * subtract the absolue value of a from r and store into r: r = |r| - |a| (no sign is checked)
   * assume |r| >= |a|
   */
  int i;
  /* assume |r| >= |a| and in particular, r->used >= a->used */
  UINT carry = 0;
  UINT tmp;
  for (i = 0; i < a->used; i++){
    /* in two subtractions to be sure to catch the new carry */
    /* r[i] = r[i]-a[i]-carry */
    tmp = r->limbs[i] - carry;
    if ((r->limbs[i] >= carry) && (tmp >= a->limbs[i])){
      carry = 0;
    }else{/* r[i] = 2^WORDSIZE + r[i] - a[i] - carry */
      carry = 1;
    }
    r->limbs[i] = tmp - a->limbs[i];
  }
  /* now the limbs of r, assume the limbs of a are 0 */
  for (i = a->used; i < r->used; i++){/* r[i] = 2^WORDSIZE + r[i] - carry */
    if (r->limbs[i] < carry){
      r->limbs[i] -= carry;
      carry = 1;
    }else{/* r[i] = r[i]-carry */
      r->limbs[i] -= carry;
      carry = 0;
    }
  }
  /* recompute used, knowing that r->used >= a->used */
  while((r->used > 1) && (r->limbs[r->used-1] == 0)){
    r->used--;
  }
  if (carry != 0) {
    return ERROR_CARRY_OVERFLOW;
  }
  return OK;
}

int mpint_cmp_mgn(mpint_t a, mpint_t b){
  /* comparison of the absolute values of a and b
   * [in] mpint_t a: first operand
   * [in] mpint_t b: second operand
   * [out] return: MPINT_EQ, MPINT_GT, MPINT_LT
   */
  int i;
  /* to fix another bug found in mpint_div_mpint, locally adjust the size of a and b */
  int a_length = a->used;
  int b_length = b->used;
  while ((a_length > 1) && (a->limbs[a_length-1] == 0)) {
    a_length--;
  }
  while ((b_length > 1) && (b->limbs[b_length-1] == 0)) {
    b_length--;
  }
  if (a_length > b_length){
    return MPINT_GT;
  }
  if (a_length < b_length){
    return MPINT_LT;
  }
  i = a_length-1;
  while ((i >= 0) && (a->limbs[i] == b->limbs[i])) {
    i--;
  }
  if (i < 0) {
    return MPINT_EQ;
  }
  if (a->limbs[i] > b->limbs[i]){
    return MPINT_GT;
  }
  return MPINT_LT;
}

int mpint_cmp(mpint_t a, mpint_t b){
  /* comparison of relative integers (with sign)
   * [in] mpint_t a: first operand
   * [in] mpint_t b: second operand
   * [out] return: MPINT_EQ, MPINT_GT, MPINT_LT
   */
  if ((a->sign == ZPOS) && (b->sign == NEG)){
    return MPINT_GT;
  }
  if ((a->sign == NEG) && (b->sign == ZPOS)){
    return MPINT_LT;
  }
  /* a and b have same sign */
  if (a->sign == ZPOS){
    return mpint_cmp_mgn(a, b);
  }
  return mpint_cmp_mgn(b, a);
}

int mpint_add(mpint_t r, mpint_t a, mpint_t b){
  /* addition of relative integers (with sign)
   * [in] mpint_t r: result where to store the new value
   * [in] mpint_t a: first operand
   * [in] mpint_t b: second operand
   * [out] return: an error code (OK, KO, ERROR_CARRY_OVERFLOW)
   */
  if ((a->sign == ZPOS) && (b->sign == ZPOS)){
    r-> sign = ZPOS;
    return mpint_add_mgn(r, a, b);
  }
  if ((a->sign == NEG) && (b->sign == NEG)){
    r->sign = NEG;
    return mpint_add_mgn(r, a, b);
  }
  if ((a->sign == ZPOS) && (b->sign == NEG)){
    if (mpint_cmp_mgn(a, b) != MPINT_LT){/* a is not strictly smaller than b, |a|-|b| >= 0*/
      r->sign = ZPOS;
      return mpint_sub_mgn(r, a, b);
    }
    r->sign = NEG;
    return mpint_sub_mgn(r, b, a);
  }
  if ((a->sign == NEG) && (b->sign == ZPOS)){
    if (mpint_cmp_mgn(a, b) != MPINT_GT){/* a is not strictly larger than b, |b|-|a| >= 0 */
      r->sign = ZPOS;
      return mpint_sub_mgn(r, b, a);
    }
    r->sign = NEG;
    return mpint_sub_mgn(r, a, b);
  }
  return KO;
}

int mpint_sub(mpint_t r, mpint_t a, mpint_t b){
  /* subtraction of relative integers (with sign)
   * [in] mpint_t r: result where to store the new value
   * [in] mpint_t a: first operand
   * [in] mpint_t b: second operand
   * [out] return: an error code (OK, KO, ERROR_CARRY_OVERFLOW)
   */
  int a_cmp_b;
  if ((a->sign == ZPOS) && (b->sign == NEG)){
    r-> sign = ZPOS;
    return mpint_add_mgn(r, a, b);
  }
  if ((a->sign == NEG) && (b->sign == ZPOS)){
    r->sign = NEG;
    return mpint_add_mgn(r, a, b);
  }
  a_cmp_b = mpint_cmp_mgn(a, b);
  if ((a->sign == ZPOS) && (b->sign == ZPOS)){
    if ((a_cmp_b == MPINT_EQ) || (a_cmp_b == MPINT_GT)){
      r->sign = ZPOS;
      return mpint_sub_mgn(r, a, b);
    }
    r->sign = NEG;
    return mpint_sub_mgn(r, b, a);
  }
  if ((a->sign == NEG) && (b->sign == NEG)){
    if ((a_cmp_b == MPINT_EQ) || (a_cmp_b == MPINT_LT)){
      r->sign = ZPOS;
      return mpint_sub_mgn(r, b, a);
    }
    r->sign = NEG;
    return mpint_sub_mgn(r, a, b);
  }
  return KO;
}

int uint_mul(UINT * rlow, UINT * rhigh, UINT a, UINT b){
  /* multiply two full-bit marchine-words and provide the result into two words 
   * [in] a a unsigned int (uint32_t, uint64_t...)
   * [in] b a unsigned int (uint32_t, uint64_t...)
   * [out] rlow the least significant part of a*b (low weight bits)
   * [out] rhigh the most significant part of a*b (high weight bits)
   * return a code of error OK/KO
   */
  UINT a0, a1, b0, b1, a0b0, a1b1, a0b1, a1b0, crossed;
  UINT carry_half, carry_low;
  /* see mpint.h for MASK_LOW_HALF, HALF */
  /* MASK_LOW_HALF is a mark such as 0x0000ffff if WORD is 32 bit long */
  /* HALF is the half size of a word, in bits (such as 16 if WORD is 32 bit long) */
  a0 = a & MASK_LOW_HALF;
  a1 = a >> HALF;
  b0 = b & MASK_LOW_HALF;
  b1 = b >> HALF;

  a0b0 = a0*b0; /* no overflow */
  a1b1 = a1*b1; /* no overflow */
  a0b1 = a0*b1; /* no overflow */
  a1b0 = a1*b0; /* no overflow */

  crossed = a0b1 + a1b0;
  if (crossed < a0b1){
    carry_half = 1;
  }else{
    carry_half = 0;
  }
  *rlow = a0b0 + (crossed << HALF);
  if (*rlow < a0b0){
    carry_low = 1;
  }else{
    carry_low = 0;
  }
  *rhigh = a1b1 + (crossed >> HALF) + carry_low + (carry_half << HALF);
  return OK;
}

void mpint_recompute_used(mpint_t a){
  /* recompute the number of limbs used in a
   * that is, check for the high limbs that are zero
   * [in] mpint_t a
   * set a->used to the correct value
   * all limbs at a->limbs[a->used] and higher are zero
   */
  int u = MPINTMAXSIZE;
  while((u > 1) && (a->limbs[u-1] == 0)){
    u--;
  }
  a->used = u;
}

int mpint_mul_mgn(mpint_t r, mpint_t a, mpint_t b){
  /* multiply the magnitudes of a and b
   * [in] mpint_t a first operand
   * [in] mpint_t b second operand
   * [out] mpint_t r result, should have enough length
   * This is Algorithm 14.12 in the handbook of applied cryptography
   * https://cacr.uwaterloo.ca/hac/about/chap14.pdf
   */
  int i, j;
  UINT hi, lo, c;

  mpint_set_zero(r);
  r->used = a->used + b->used;
  if (r->used > MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  for (i = 0; i < a->used; i++){ /* a_i */
    c = 0;
    for (j = 0; j < b->used; j++){ /* b_j */
      uint_mul(&lo, &hi, a->limbs[i], b->limbs[j]);
      /* uv = w[i+j] + a_i*b_j + c */
      /* a_i*b_j -> [lo,hi] */
      lo = lo + c;
      if (lo < c){
        hi++;
      }
      lo = lo + r->limbs[i+j];
      if (lo < r->limbs[i+j]){
        hi++;
      }
      /* w_i+j = v, c = u */
      r->limbs[i+j] = lo;
      c = hi;
    }/* loop over b */
    r->limbs[i+b->used] = c;
  }/* loop over a */
  mpint_recompute_used(r);
  return OK;
}

int mpint_mul(mpint_t r, mpint_t a, mpint_t b){
  /* multiply a and b into r, update the sign of r
   * [in] mpint_t a first operand
   * [in] mpint_t b second operand
   * [out] mpint_t r result, should have enough length
   * call function mpint_mul_mgn
   * adjust the sign of the result according to the sign of a and b
   */
  int err;
  err = mpint_mul_mgn(r, a, b);
  if (err == OK){
    if ((a->sign == b->sign) || ((r->used <= 1) && (r->limbs[0] == 0))){
      r->sign = ZPOS;
    }else{
      r->sign = NEG;
    }
  }
  return err;
}

/* TP 3 */

int mpint_deep_copy(mpint_t r, mpint_t a){
  /* copy a into r: copy a->sign, a->used, and each word of a->limbs
   * [in] a
   * [out] r
   */
  int i = 0;
  r->sign = a->sign;
  r->used = a->used;
  for(i=0; i < a->used; i++){
    r->limbs[i] = a->limbs[i];
  }
  /* not strictly needed, but just in case */
  for(i=a->used; i < MPINTMAXSIZE; i++){
    r->limbs[i] = 0;
  }
  return OK;
}

int modint_add(mpint_t r, mpint_t m, mpint_t a, mpint_t b){
  /* compute r = a + b mod m
   * assume that a and b are already reduced: 0 <= a < m and 0 <= b < m
   * [in] a 1st operand, reduced: 0 <= a < m
   * [in] b 2nd operand, reduced: 0 <= b < m
   * [in] m module
   * [out] r result, reduced: 0 <= r < m
   * check that the word size of r is one word larger to ensure that there is
   * no carry overflow lost at some point
   */
  int code;
  mpint_t tmp;
  if (m->used == MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  if ((a->sign == NEG) || (b->sign == NEG) || (mpint_cmp_mgn(a, m) != MPINT_LT) || (mpint_cmp_mgn(b, m) != MPINT_LT)){
    return ERROR_INPUT_NOT_REDUCED;
  }
  code = mpint_add_mgn(r, a, b);
  /* code cannot be ERROR_CARRY_OVERFLOW */
  if (mpint_cmp_mgn(r, m) != MPINT_LT){ /* the result is larger than the module m, subtract m */
    mpint_sub(tmp, r, m);
    mpint_deep_copy(r, tmp);
  }
  return OK;
}

int modint_sub(mpint_t r, mpint_t m, mpint_t a, mpint_t b){
  /* compute r = a - b mod m
   * assume that a and b are already reduced: 0 <= a < m and 0 <= b < m
   * [in] a 1st operand, reduced: 0 <= a < m
   * [in] b 2nd operand, reduced: 0 <= b < m
   * [in] m module
   * [out] r result, reduced: 0 <= r < m
   * check that the word size of r is one word larger to ensure that there is
   * no carry overflow lost at some point
   */
  int code;
  mpint_t tmp;
  if (m->used == MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  if ((a->sign == NEG) || (b->sign == NEG) || (mpint_cmp_mgn(a, m) != MPINT_LT) || (mpint_cmp_mgn(b, m) != MPINT_LT)){
    return ERROR_INPUT_NOT_REDUCED;
  }
  code = mpint_sub(r, a, b);
  /* code cannot be ERROR_CARRY_OVERFLOW */
  if (r->sign == NEG){
    mpint_add(tmp, r, m); /* the sign should be ZPOS now */
    mpint_deep_copy(r, tmp);
  }
  return OK;
}

int modint_neg(mpint_t r, mpint_t m, mpint_t a){
  /* compute r = -a mod m
   * assume that a is already reduced: 0 <= a < m
   * [in] a 1st operand, reduced: 0 <= a < m
   * [in] m module
   * [out] r result, reduced: 0 <= r < m
   * check that the word size of r is one word larger to ensure that there is
   * no carry overflow lost at some point
   */
  if ((a->sign == NEG) || (mpint_cmp_mgn(a, m) != MPINT_LT)){
    return ERROR_INPUT_NOT_REDUCED;
  }
  if (mpint_is_zero(a) == TRUE){
    mpint_set_zero(r);
  } else {
    mpint_sub(r, m, a);
  }
  /* code cannot be ERROR_CARRY_OVERFLOW */
  /* result cannot be negative */
  return OK;
}

int mpint_word_mul_mgn(mpint_t r, mpint_t a){
  /* multiply by a machine-word, that is shift the limbs
   * [in] a
   * [out] r
   */
  int i;
  if (a->used == MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  r->sign = a->sign;
  r->used = a->used+1;
  /* decrease the counter i to be compatible with in-place affectation (r=a) */
  for(i=r->used-1; i > 0; i--){
    r->limbs[i] = a->limbs[i-1];
  }
  r->limbs[0] = (UINT)0;
  /* fill with zeros the other limbs */
  for(i=r->used; i < MPINTMAXSIZE; i++){
    r->limbs[i] = (UINT)0;
  }
  /* adjust r->used */
  while ((r->used > 1) && (r->limbs[r->used-1] == 0)){
    r->used--;
  }
  return OK;
}

int mpint_word_div_mgn(mpint_t r, mpint_t a){
  /* divide by a machine-word, that is shift the limbs by one word to the lsb,
   * a->limbs[0] is lost
   * [in] a
   * [out] r
   */
  int i;
  r->sign = a->sign;
  r->used = a->used-1;
  if (r->used == 0){ /* detect (a >> WORD) == 0 */
    r->used = 1;
    r->limbs[0] = 0;
    return OK;
  }
  for(i=0; i < r->used; i++){
    r->limbs[i] = a->limbs[i+1];
  }
  /* fill with zeros the other limbs */
  for(i=r->used; i < MPINTMAXSIZE; i++){
    r->limbs[i] = (UINT)0;
  }
  /* adjust r->used */
  while ((r->used > 1) && (r->limbs[r->used-1] == 0)){
    r->used--;
  }
  return OK;
}

int mpint_uint_mul_mgn(mpint_t r, UINT u, mpint_t a){
  /* multiply a mpint_t by a machine-word. The result will be one limb larger
   * [in] a
   * [in] u
   * [out] r
   * return: ERROR_ABOVE_MPINTMAXSIZE if there is no extra machine-word left free
   */
  int i;
  UINT rlow;
  if (a->used == MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  r->used = a->used + 1;
  /* trick: the address of (pointer to) the first element in the array r->limbs,
     that is the address of r->limbs[0], is r->limbs.
     The address of the second element r->limbs[1] is r->limbs+1.
  */
  /* without simplification of notations:
     uint_mul(&(r->limbs[0]), &(r->limbs[1]), a->limbs[0], u); */
  uint_mul(r->limbs, r->limbs + 1, a->limbs[0], u);
  for(i=1; i < a->used; i++){
    /* at each step, multiply a_i by u, this produces two machine-words rlow and rhigh.
       accumulate r_{i+1} which was rhigh of the previous step.
       &(rlimbs->[i+1] <-> rlimbs+i+1 */
    uint_mul(&rlow, r->limbs + i + 1, a->limbs[i], u);
    r->limbs[i] += rlow;
    if (r->limbs[i] < rlow){ /* carry */
      r->limbs[i+1] ++;
      /* and there is no  more carry propagation because a*b+c fits in 2*WORDSIZE */
    }
  }
  /* adjust r->used */
  while((r->used > 1) && (r->limbs[r->used-1] == 0)){
    r->used--;
  }
  return OK;
}

/* TP 4 */
/* if you wrote the function with another order of the inputs this is fine,
   you might need to adapt the test file */
int modint_mul(mpint_t r, mpint_t a, mpint_t b, mpint_t m, UINT m_prime){
  /* Algorithm 14.36 in the Handbook of Applied Cryptography
   * [in] a: multi-precision modular integer, reduced, 0 <= a < m
   * [in] b: multi-precision modular integer, reduced, 0 <= b < m
   * [in] m: multi-precision positive integer, module, odd (m % 2 == 1)
   * [in] m_prime: single-precision unsigned integer, m' = -1/m mod 2^WORD where WORD is defined in mpint.h
   * [out] r: multi-precision modular integer, reduced, 0 <= r < m
   * r = a * b * R^(-1) mod m
   *
   * R = 2^(WORD * m->used) so that R is a power of 2 and R > m
   * assumes that there is one free machine-word in the mpint_t, that is m->used < MPINTMAXSIZE
   */
  if (m->used == MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  mpint_set_zero(r);
  int i, code;
  UINT ui, uj, uk;
  mpint_t tmp1, tmp2;
  mpint_set_zero(tmp1);
  mpint_set_zero(tmp2);  
  for (i = 0; i < m->used; i++){
    /* 2.1 ui <- (r0 + ai*b0)*m_prime mod 2^WORD */
    /* 1. ai*b0 */
    uint_mul(&uj, &uk, a->limbs[i], b->limbs[0]);
    /* 2. r0 + ai*b0 mod 2^WORD, do not take into account the carry because of reduction mod 2^WORD */
    uj += r->limbs[0];
    /* 3. (r0 + ai*b0)*m_prime mod 2^WORD */
    uint_mul(&ui, &uk, uj, m_prime);
    /* 2.2 r <- (r + ai*b + ui*m)/2^WORD */
    /* 4. tmp1 = ui*m, and because m->used <= MPINTMAXSIZE-1, the result fits in the mpint_t tmp1 */
    code = mpint_uint_mul_mgn(tmp1, ui, m);
    /* 5. tmp2 <- r + ui*m, and the result should fit in tmp2 */
    code = mpint_add_mgn(tmp2, r, tmp1); /* now r and tmp1 are free */
    mpint_set_zero(tmp1);
    mpint_set_zero(r);  
    /* 6. ai*b, and because a->used <= MPINTMAXSIZE-1, the result fits in the mpint_t */
    code = mpint_uint_mul_mgn(r, a->limbs[i], b);
    /* 7. tmp1 <- r + ai*b, but here there might be an overflow !!! */
    code = mpint_add_mgn(tmp1, r, tmp2); /* now r and tmp2 are free */
    /* sometimes, code is ERROR_CARRY_OVERFLOW here */
    mpint_set_zero(r);
    /* divide by 2^WORD */
    mpint_word_div_mgn(r, tmp1);
    /* and now check if there was a carry at the previous step */
    if (code == ERROR_CARRY_OVERFLOW) {
      /* add the lost carry in the extra (supposed) free limb of r */
      r->limbs[MPINTMAXSIZE-1] = (UINT)1;
      r->used = MPINTMAXSIZE;
      /* if or while? */
      while (mpint_cmp_mgn(r, m) != MPINT_LT) {
	mpint_set_zero(tmp1);
	mpint_sub(tmp1, r, m);
	mpint_deep_copy(r, tmp1);
      }
    }
  }
  /* if r >= m then r <- r-m */
  while (mpint_cmp_mgn(r, m) != MPINT_LT) {
    mpint_set_zero(tmp1);
    mpint_sub(tmp1, r, m);
    mpint_deep_copy(r, tmp1);
  }
  return OK;
}

/* TP 5 */

int mpint_dbl_mgn(mpint_t a){
  /* return a <- a << 1 (with shift of one bit to the msb)
   * [in,out] a: multi-precision integer
   */
  int i;
  UINT carry;
  /* get the final carry: the mos significant bit of the most significant word of a */
  carry = a->limbs[a->used - 1] >> (WORD - 1);
  for (i = a->used-1; i > 0; i--) {
    a->limbs[i] = (a->limbs[i] << 1) | (a->limbs[i-1] >> (WORD -1));
  }
  a->limbs[0] = a->limbs[0] << 1;

  if (carry != 0){
    if (a->used < MPINTMAXSIZE){
      a->limbs[a->used] = carry;
      a->used ++;
    } else {
      /* adjust a->used */
      while ((a->used > 1) && (a->limbs[a->used-1] == 0)){
	a->used --;
      }
      return ERROR_CARRY_OVERFLOW;
    }
  }
  return OK;
}

int modint_exp_mpint(mpint_t r, mpint_t a, mpint_t e, mpint_t m, UINT m_prime){
  /* r = a^e modulo m using Montgomery multiplication
   * [in] a: 1st operand, modular multi-precision integer, assumes it is reduced: 0 <= a < m
   * [in] e: exponent, positive multi-precision integer
   * [in] m: module, positive multi-precision integer
   * [in] m_prime: single-precision positive integer, inverse of m modulo 2^WORD
   * [out] r: result, modular multi-precision integer, reduced: 0 <= r < m
   */
  int i, j;
  mpint_t tmp;
  mpint_ptr r1, r2, rswap;
  UINT ej, eij;
  r1 = r;
  r2 = tmp;
  /* by convention, anything to the power 0 is 1, except 0, check if the input a is zero */
  if (mpint_is_zero(a) == TRUE){
    mpint_set_zero(r);
    return OK;
  }
  /* adjust e->used just in case? */
  while ((e->used > 1) && (e->limbs[e->used-1] == 0)) {
    e->used --;
  }
  if (mpint_is_zero(e) == TRUE){
    mpint_set_one(r);
    return OK;
  }
  j = e->used-1;
  ej = e->limbs[j];
  /* assume that ej != 0 */
  i = WORD-1;
  while ((i > 0) && ((ej >> i) == 0)) {
    i--;
  }
  mpint_deep_copy(r1, a); /* for the 1st non-zero bit */
  i--;
  for ( ; i >= 0; i--){
    modint_mul(r2, r1, r1, m, m_prime); /* square */
    eij = (ej >> i) & 1;
    if (eij != 0){
      modint_mul(r1, r2, a, m, m_prime); /* mul */
    } else { /* swap r1 and r2 */
      rswap = r1;
      r1 = r2;
      r2 = rswap;
    }
  }	
  for (j = e->used-2; j >= 0; j--){
    ej = e->limbs[j];
    for (i = WORD-1; i >= 0; i--){
      modint_mul(r2, r1, r1, m, m_prime); /* square */
      eij = (ej >> i) & 1;
      if (eij != 0){
	modint_mul(r1, r2, a, m, m_prime); /* mul */
      } else { /* swap r1 and r2 */
	rswap = r1;
	r1 = r2;
	r2 = rswap;
      }
    }
  }
  if (r1 != r){
    mpint_deep_copy(r, r1);
  }
  return OK;
}

/* TP 6 */

void mpint_adjust_size_used(mpint_t a){
  /* [in,out] a
   * return OK
   */
  if (a->used > MPINTMAXSIZE){
    a->used = MPINTMAXSIZE;
  }
  if (a->used == 0) {
    a->used = 1;
    a->limbs[0] = 0;
  }
  /* fill-in with zeros above index i = a->used */
  for(int i = a->used; i < MPINTMAXSIZE; i++){
    a->limbs[i] = 0;
  }
  /* adjust a->used: decrease it if there are zeros */
  while ((a->used > 1) && (a->limbs[a->used - 1] == 0)){
    a->used--;
  }
}

int uint_div(UINT *q1, UINT *q0, UINT *r0, UINT a1, UINT a0, UINT b0){
  /* Divide double-precision {a1, a0} by single-precision b0, a1*2^WORD + a0 = (q1*2^WORD + q0)*b0 + r0
   * [in] a1
   * [in] a0
   * [in] b0
   * [out] q1
   * [out] q0
   * [out] r0
   * can r0 be the address of a1: NO
   * Since b0 is a single-precision machine-word,
   * the remainder is also a single-precision machine-word r0.
   * It might be that the quotient is a double-precision integer, q1*2^WORD + q0 with q1 != 0.
   */
  if (b0 == 0) {
    *q1 = 0;
    *q0 = 0;
    *r0 = 0;
    return ERROR_DIVISION_BY_ZERO;
  }
  if (a1 == 0) {
    /* easy case where this is single-precision */
    *q1 = 0;
    *q0 = a0 / b0;
    *r0 = a0 % b0;
    return OK;
  }
  /* now we are sure this is a double-precision division and b0 is non-zero. */
  /* if the high half part of b0 is zero, no need for a complicated algorithm,
     this boilds down to exercise 16 in the Knuth Vol 2. */
  if ((b0 >> HALF) == 0) {
    /* exercise 16: divide u_{n-1} u_{n-2} ... u_1 u_0 by v a single-digit precision integer,
       producing quotient w_{n-1} w_{n-2}...w_1 w_0 and remainder r. */
    /* and we are sure b0 != 0 here */
    *r0 = 0;
    /* n = 4 as (a1 a0) = (a1hi a1lo a0hi a0lo) = (u3 u2 u1 u0) in 4 half-words */
    /* j = 3 = n-1, *r0 = 0 at start, do not write it */
    /* q1 high, u3 / b0, u3 % b0 */
    *q1 = ((a1 >> HALF) / b0) << HALF;
    *r0 = (a1 >> HALF) % b0; /* *r0 always < MASK_LOW_HALF */
    /* j = 2 */
    /* q1 low */
    *q1 |= ((*r0 << HALF) | (a1 & MASK_LOW_HALF)) / b0;
    *r0 = ((*r0 << HALF) | (a1 & MASK_LOW_HALF)) % b0;
    /* *q1 = (q_hi << HALF) | q_lo; */
    /* j = 1 */
    *q0 = (((*r0 << HALF) | (a0 >> HALF)) / b0) << HALF;
    *r0 = ((*r0 << HALF) | (a0 >> HALF)) % b0;
    /* j = 0 */
    *q0 |= ((*r0 << HALF) | (a0 & MASK_LOW_HALF)) / b0;
    *r0 = ((*r0 << HALF) | (a0 & MASK_LOW_HALF)) % b0;
    /* *q0 = (q_hi << HALF) | q_lo; */
    return OK;
  }
  /* now, this is serious: a1 != 0, b0 >> HALF != 0
   it corresponds to applying the generic algorithm D of Knuth with
   u = (u3 u2 u1 u0) = (a1hi a1lo a0hi a0lo) and v = (v1 v0) = (b0hi b0lo) */
  /* D1. Normalize. */
  /* shift b0 to the left until the msb of b0 is at position WORD-1 */
  int i = WORD - 1, j;
  while ((i > 0) && ((b0 >> i) == 0)) { /* in fact, i > HALF as we said b0>>HALF is non-zero */
    i--;
  }
  /* b0 >> i is non-zero, b0 >> (i+1) is zero -> there are WORD-1-i zeros at the msb bits of b0 */
  /* extreme cases: i = 0, in this case there are WORD-1 bits at zero,
     i = WORD-1, in this cases there is no zero */
  /* shift of j = WORD-1-i to the left if needed */
  /* recall that b0 is non-zero, 0 <= j <= HALF-1 */
  j = WORD-1-i;
  UINT a_2 = 0, a_1 = a1, a_0 = a0, b_0 = b0;
  if (j > 0) {
    b_0 = b0 << j;
    a_2 = a1 >> (WORD - j); /* and in theory, a2 <= MASK_LOW_HALF */
    a_1 = (a1 << j) | (a0 >> (WORD - j));
    a_0 = a0 << j;
  }
  /* UINT u4 = a_2, u3 = (a_1 >> HALF), u2 = (a_1 & MASK_LOW_HALF), u1 = (a_0 >> HALF), u0 = (a_0 & MASK_LOW_HALF); */
  UINT v1 = (b_0 >> HALF), v0 = (b_0 & MASK_LOW_HALF);
  /* n = 2, m = 2 */
  /* D2. j = m */
  /* j = 2; */
  /* divide (u4 u3 u2) = (a_2 a_1) by (v1 v0) to get a single quotient digit qj = q2 */
  /* D3. q_, where 0xffffffff >= b0 >= 0x80000000, and
     a2 = (a1 >> (HALF+1)) au plus, donc a2 a HALF-1 bits non-nuls,
     0 <= a2 <= 0x7fff, non ?
  */
  /* 0xffffffff / 0x8000 = 0x1ffff */
  /* 0x7fffffff / 0x8000 = 0xffff */
  UINT tmp = (a_2 << HALF) | (a_1 >> HALF);
  UINT q_ = tmp / v1; /* and q_ should be a half-machine word most of the cases? */
  UINT r_ = tmp % v1;
  /* test if q_ = (1 << HALF) or if q_ * v0 > ((r_ << HALF) + u2) */
  /* I am sure that q_ * v0 does not overflow? yes because there is the test (q_ > MASK_LOW_HALF just before) */
  while (((q_ > MASK_LOW_HALF) || ((q_ * v0) > ((r_ << HALF) | (a_1 & MASK_LOW_HALF)))) && (r_ <= MASK_LOW_HALF) && (q_ > 0)) {
    q_--;
    r_ += v1;
  }
  /* D4 Replace (u4 u3 u2) by (u4 u3 u2) - q_*(v1 v0) */
  UINT m1, m0;
  uint_mul(&m0, &m1, q_, b_0); /* b0 = (v1 v0) */
  /* (u4 u3 u2) - (m1 m0) <=> (a2 a1) - (m1 m0) see ui as half-words, mi as full-words but high half of m1 should be 0 */
  if ((a_2 < m1) || ((a_2 == m1) && (a_1 < m0))){
    /* carry = 1; */
    /* D6: I subtract here 1 to q and subtract b0 to (m1 m0) */
    q_--;
    if (m0 < b_0){
      m1--;
    }
    m0 -= b_0;
  }
  if (a_1 < m0) {
    a_2--; /* anyway, a2 < (1 << HALF) */
  }
  a_1 -= m0;
  a_2 -= m1; /* and if a2 < m1: no, D6 already done, should be fine */
  /* a2 should be 0 */
  if (a_2 != 0){
    return KO;
  }
  /* D5 */
  *q1 = q_; /* the result is (q2 q1 q0) in half-machine words, (*q1 *q0) in full-machine words */
  /* if (carry != 0) { */
    /* D6 decrease qj by one and add (0 v1 v0) to (u4 u3 u2) --> already done just above */
  /* j--; */
  /* j = 1 */
  /* go back to D3 */
  
  /* divide (u3 u2 u1) by (v1 v0) to get a single quotient digit qj = q1 */
  /* D3 find q_ = (u3 u2) / v1 and r_ = (u3 u2) % v1 */
  /* (u3 u2) <-> a1 */
  q_ = a_1 / v1;
  r_ = a_1 % v1;
  /* test if q_ = (1 << HALF) or if q_ * v0 > ((r_ << HALF) + u1), where u1 is the half high part of a_0 */
  while (((q_ > MASK_LOW_HALF) || ((q_ * v0) > ((r_ << HALF) | (a_0 >> HALF)) )) && (r_ <= MASK_LOW_HALF) && (q_ > 0)) {
    q_--;
    r_ += v1;
  }
  /* D4 multiply q_ * (v1 v0) and subtract to (u3 u2 u1) = (a1 a0_hi) */
  uint_mul(&m0, &m1, q_, b_0); /* b0 = (v1 v0) */
  /* (u3 u2 u1) <-> (a_1 a_0high) */
  tmp = (a_1 << HALF) | (a_0 >> HALF); /* tmp = u2u1 */
  /* re-use a_2 to store u3 */
  a_2 = a_1 >> HALF;
  /* D5 D6: if (u3 u2 u1) = (u3 u2u1) < (m1 m0), decrease q_ by one and subtract b0 = (v1 v0) to (m1 m0) */
  if ((a_2 < m1) || ((a_2 == m1) && (tmp < m0))) {
    q_--;
    if (m0 < b_0){
      m1--;
    }
    m0 -= b_0;
  }
  /* D4 subtract (m1 m0) to (u3 u2 u1) */
  if (tmp < m0){
    a_2 --;
  }
  tmp -= m0;
  a_2 -= m1; /* we should have u3 == 0 now */
  if (a_2 != 0){
    return KO;
  }
  /* D5 */
  *q0 = (q_ << HALF);
  /* D7 */
  /* j--; */
  /* j = 0; */
  /* go back to D3 */
  
  /* divide (u2 u1 u0) by (v1 v0) to get a single quotient digit qj = q0 */
  /* D3 find q_ = (u2 u1) / v1 and r_ = (u2 u1) % v1 */
  q_ = tmp / v1;
  r_ = tmp % v1;
  /* test if q_ = (1 << HALF) or if q_ * v0 > ((r_ << HALF) + u0) */
  while (((q_ > MASK_LOW_HALF) || ((q_ * v0) > ((r_ << HALF) | (a_0 & MASK_LOW_HALF)) )) && (r_ <= MASK_LOW_HALF) && (q_ > 0)) {
    q_--;
    r_ += v1;
  }
  /* D4 multiply q_ * (v1 v0) and subtract to (u2 u1 u0) = (u2 a_0) */
  uint_mul(&m0, &m1, q_, b_0); /* b0 = (v1 v0) */
  /* (u2 u1 u0) <-> (u2 a_0) */
  a_2 = tmp >> HALF; /* a_2 <- u2 */
  a_0 = (tmp << HALF) | (a_0 & MASK_LOW_HALF);
  /* D5 D6: if (u2 u1 u0) < (m1 m0), decrease q_ by one and subtract b0 = (v1 v0) to (m1 m0) */
  if ((a_2 < m1) || ((a_2 == m1) && (a_0 < m0))) {
    q_--;
    if (m0 < b_0){
      m1--;
    }
    m0 -= b_0;
  }
  /* D4 subtract (m1 m0) to (u2 u1 u0) */
  if (a_0 < m0){
    a_2--;
  }
  a_0 -= m0;
  a_2 -= m1; /* and u2 should be 0 here */
  if (a_2 != 0){
    return KO;
  }
  /* D5 */
  *q0 |= (q_ & MASK_LOW_HALF);
  /* D7 */
  /* j--; */
  /* j = -1; */
  /* done */
  *r0 = a_0;
  /* D8, unnormalize the remainder */
  j = WORD-1-i;
  if (j != 0){
    *r0 >>= j;
  }
  return OK;
}

int mpint_div_uint(mpint_t q, UINT *r, mpint_t a, UINT b){
  /* divide the multi-precision integer a by the single-precision b.
   * This is Knuth, exercise 16 p. 282 in the section 4.3.1 about multi-precision.
   * [in] a dividend, multi-precision
   * [in] b divisor, single-precision
   * [out] q quotient, q = floor(a/b)
   * [out] r remainder, r = a % b
   */
  /* Knuth.
     dividend u = (u_{n-1} u_{n-2} ... u_1 u_0),
     divisor v (single-precision)
     output: quotient (w_{n-1} w_{n-2} w_1 w_0) and remainder r.
     1. set r <- 0, j <- n-1
     2. set w_j <- floor((r*2^WORD + u_j)/v), r <- (r*2^WORD + u_j) % v
     3. Decrease j by 1, and return to step 2. if j >= 0.
  */
  mpint_adjust_size_used(a);
  int n = a->used;
  int j;
  int code;
  *r = 0;
  UINT r0 = 0, q0 = 0, q1 = 0;
  /* I am not using mpint_set_zero to allow for in-place division */
  if (q != a) { /* not in place */
    mpint_set_zero(q);
  }
  if (b == 0) {
    return ERROR_DIVISION_BY_ZERO;
  }
  q->used = a->used;
  q->sign = ZPOS;    
  for(j=n-1; j >= 0; j--) {
    code = uint_div(&q1, &q0, r, r0, a->limbs[j], b);
    if (code != OK){
      return code;
    }
    /* since r < b, we have q1 = 0 */
    r0 = *r;
    q->limbs[j] = q0;
  }
  mpint_adjust_size_used(q);
  return OK;
}

#ifdef DEBUG
int mpint_div_mgn(mpint_t q, mpint_t r, mpint_t a, mpint_t b, int debug){
#else
int mpint_div_mgn(mpint_t q, mpint_t r, mpint_t a, mpint_t b){
#endif
  /* Euclidean division of a and b: find quotient q and remainder r such that a = b*q + r and 0 <= r < b.
   * [out] q quotient
   * [out] r remainder, positive, 0 <= r < b
   * [in] a dividend, only magnitude is considered
   * [in] b divisor, only magnitude is considered
   * Volume 2 of Donald Knuth's The art of computer programming, Algorithm D.
   * B = 2^WORD with the notations in mpint.h
   * size requirement: one extra free word in a, q, that is a->used < MPINTMAXSIZE
   * only the magnitude of a and b is considered.
   */
  /* a = a_{m+n-1} ... a_1 a_0
     b = b_{n-1} ... b_1 b_0   where b_{n-1} != 0 and n > 1
     q = q_m q_{m-1} ... q_0
     r = r_{n-1} ... r_1 r_0
  */
  /* If 0 <= a < b, then q = 0 and r = a. */
  mpint_t a_new, ujn_uj, b_new, tmp, tmp1, tmp2;
  /* ujn_uj contains the current words u_{j+n} ... u_{j} */
  int code;
  UINT q1_, q0_, r1, r0;
  UINT aj1, aj0, bn_1, bn_2, m1, m0;
  /* maybe adjust a->used and b->used just to be sure */
  mpint_adjust_size_used(a);
  mpint_adjust_size_used(b);
  int k = a->used;
  int n = b->used;
  int m = k - n; /* one wants to have k-1 == m+n-1, ok */
#ifdef DEBUG
  if (debug == TRUE){
    printf("inside mpint_div_mpint, debug = TRUE\n");
  }
#endif
  if (a == q) {
    return ERROR_IN_PLACE_NOT_POSSIBLE;
  }
  /* not in place */
  mpint_set_zero(q);
  q->sign = ZPOS;
  mpint_set_zero(r);
  r->sign = ZPOS;

  /* before all, test that b is non-zero */
  if (mpint_is_zero(b) == TRUE) {
    return ERROR_DIVISION_BY_ZERO;
  }
  /* test if b has length 1, in that case, call the function for simple-precision b */
  if (b->used == 1) {
    /* address of r->limbs[0] is &r->limbs[0] = r->limbs */
    return mpint_div_uint(q, r->limbs, a, b->limbs[0]);
  }
  if (mpint_cmp_mgn(a, b) == MPINT_LT) {
    mpint_deep_copy(r, a);
    /* and q was already set to 0 */
    r->sign = ZPOS;
    return OK;
  }
  q->used = m+1;
  r->used = n;
  /* D1. Normalize: set d = (B-1)/b_{n-1} */
  /*
     UINT d = MASK_FULL / b->limbs[b->used - 1];

     It produces an error for example with b = {0x3, 0x1} -->
     the scaling factor is d = (2^WORD-1)/0x1 = 2^WORD-1,
     but then d * b overflows because b_0 > b_1, and
     d * b = {0xfffffffd, 0x1, 0x1}
  */
  /* count the number of leading zeros in the binary representation of b */
  int ctr = 0;
  while ((b->limbs[b->used - 1] >> (WORD-1-ctr) == 0) && (ctr < WORD - 1)) {
    ctr++;
  }
  UINT d = 0x1;
  d = d << ctr;
  /* TODO: use a binary shift */
  /* multiply a by d, b by d. b should not increase in size but a might. */
  code = mpint_uint_mul_mgn(a_new, d, a);
  if (code == ERROR_ABOVE_MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  code = mpint_uint_mul_mgn(b_new, d, b);
  if (code == ERROR_ABOVE_MPINTMAXSIZE){
    return ERROR_ABOVE_MPINTMAXSIZE;
  }

  if (b_new->used != b->used){
#ifdef DEBUG
    if(debug == TRUE){
      printf("b_new->used != b->used, d = ");
      uint_print_dec(d);
      printf(" = ");
      uint_print_hexa(d);
      printf(" b = ");
      mpint_print_hexa(b);
      printf(" b_new = ");
      mpint_print_hexa(b_new);
      printf(" return KO\n");
    }
#endif
    return KO;
  }
  /* D2. initialize j = m, where a_new->used = m+n+1, b_new->used = n */
  /* copy the words of indices a_{j+n} ... a_{j+1} a_{j} with j=m into ujn_uj */
  ujn_uj->sign = ZPOS;
  ujn_uj->used = b_new->used + 1;
  if ((a_new->used < m+n+1) && (m+n+1 <= MPINTMAXSIZE)) {
    a_new->limbs[m+n] = 0;
  }
  for(int i = n; i >= 0; i--){
    ujn_uj->limbs[i] = a_new->limbs[m+i];
  }
  bn_1 = b_new->limbs[b_new->used-1];
  bn_2 = b_new->limbs[b_new->used-2]; /* it does not exist if b has length 1 -> b->used >= 2 */
#ifdef DEBUG
  if (debug == TRUE) {
    printf("k = a->used = %d, n = b->used = %d, m = k-n = %d ", k, n, m);
    printf("ujn_uj = ");
    mpint_print_hexa(ujn_uj);
    printf(" a_new = ");
    mpint_print_hexa(a_new);
    printf("\n");
  }
#endif
  for (int j = m; j >= 0; j--) {
    /* divide ujn_uj = [a_{j+n} .. a_{j+1} a_j] by b=[b_{n-1} ... b_1 b_0] to get a single quotient digit q_j */
    /* D3. Calculate q_ = hat(q) */
    /* set q_ = floor( (a_{j+n}*B + a_{j+n-1})/b_{n-1} ) */
    /* floor = partie entiere inferieure */
    aj1 = ujn_uj->limbs[n];/* I shifted j places to the right the words of ujn_uj -> stored at indices n ... 0 */
    aj0 = ujn_uj->limbs[n-1];
    q1_ = 0;
    q0_ = 0;
    r0 = 0;
    r1 = 0;
    code = uint_div(&q1_, &q0_, &r0, aj1, aj0, bn_1);
    if (code != OK) {
      return code;
    }
#ifdef DEBUG
    if (debug == TRUE) {
      printf("j = %d ujn_uj = ", j);
      mpint_print_hexa(ujn_uj);
      printf(" scaling factor d = %u = ", d);
      uint_print_hexa(d);
      printf(", aj1 = ");
      uint_print_hexa(aj1);
      printf(" aj0 = ");
      uint_print_hexa(aj0);
      printf(" bn_1 = ");
      uint_print_hexa(bn_1);
      printf(" q1_ = ");
      uint_print_hexa(q1_);
      printf(" q0_ = ");
      uint_print_hexa(q0_);
      printf(" r0 = ");
      uint_print_hexa(r0);
      printf("\n");
    }
#endif
    /* decrease q_ = (q1_ q0_) in case it is too large */
    /* r1 is used to detect r > 2^WORD */
    while ((q1_ != 0) && (r1 == 0)) { /* decrease q_ = (q1_ q0_) by one */
      /* condition r0 <= (MASK_FULL - bn_1) ? */
      if (q0_ == 0) {
	q1_--;
      }
      q0_--;
      r0 += bn_1; /* check for overflow */
      if (r0 < bn_1) {
	r1++;
      }
    }
    if ((q1_ == 0) && (r1 == 0)) {
      /* test if q0_ * b_{n-2} > 2^WORD * r0 + u_{j+n-2} */
      uint_mul(&m0, &m1, q0_, bn_2);
#ifdef DEBUG
      if (debug == TRUE) {
	printf("test if q0_ * b_{n-2} > 2^WORD * r0 + u_{j+n-2}\n");
	printf("q0_ * b_{n-2} = m1 m0 =   ");
	uint_print_hexa(m1);
	printf(" ");
	uint_print_hexa(m0);
	printf("\n2^WORD * r0 + u_{j+n-2} = ");
	uint_print_hexa(r0);
	printf(" ");
	uint_print_hexa(ujn_uj->limbs[n-2]);
	printf("\n");
      }
#endif
      /* remember that the limbs of ujn_uj are stored at places n ... 0 for indices n+j ... j
	 hence index j+n-2 -> is actually n-2 */
      while ((q0_ != 0) && (r1 == 0) && ((m1 > r0) || ((m1 == r0) && (m0 > ujn_uj->limbs[n-2])))){
#ifdef DEBUG
	if (debug == TRUE) {
	  printf("test if q0_ * b_{n-2} > 2^WORD * r0 + u_{j+n-2} : TRUE, will decrement q0_");
	  printf("\n");
	}
#endif
	q0_--;
	r0 += bn_1; /* check for overflow */
	if (r0 < bn_1) {
	  r1++;
	}
	uint_mul(&m0, &m1, q0_, bn_2);
      }
    }
    /* q_ * b_new */
    /* it might be possible to have an overflow if q1_ != 0 */
    /* the best would be to have the mpint with two extra words instead of one */
    mpint_set_zero(tmp); /* the sign at least should be set to ZPOS */
    mpint_set_zero(tmp1); /* the sign at least should be set to ZPOS */
    mpint_set_zero(tmp2); /* the sign at least should be set to ZPOS */
    mpint_uint_mul_mgn(tmp, q0_, b_new);
    if (q1_ != 0) {
      mpint_uint_mul_mgn(tmp1, q1_, b_new);
      /* fingers crossed that it does not overflow the highest most significant word */
      /* does mpint_uint_mul_mgn adjusts tmp1->used? --> yes it does. */
      mpint_word_mul_mgn(tmp2, tmp1);
      /* tmp2 = q1_*2^WORD * b_new */
      code = mpint_add_mgn_inplace(tmp, tmp2);
      /* check that there is no overflow */
      if (code == ERROR_CARRY_OVERFLOW){
	return code; /* I don't know how to deal with that */
      }
    }
    /* subtract */
    /* code = mpint_sub_mgn_inplace(ujn_uj, tmp); */
    /* if (code == ERROR_CARRY_OVERFLOW) { */
      /* add back, step D6 */
    /* } */
    /* alternatively, compare and add back prior to subtract */
#ifdef DEBUG
    if (debug == TRUE) {
      printf("ujn_uj = ");
      mpint_print_hexa(ujn_uj);
      printf(" q1_ = ");
      uint_print_hexa(q1_);
      printf(" q0_ = ");
      uint_print_hexa(q0_);
      printf(" r1 = ");
      uint_print_hexa(r1);
      printf(" r0 = ");
      uint_print_hexa(r0);
      printf(" q_*b_new = ");
      mpint_print_hexa(tmp);
      printf(" then do ujn_uj - q_*b_new \n");
      /* ah, another bug. The size of ujn_uj is one more word, so there is a leading word with 0, but the size of tmp is exact (it tight), so while comparing the size, the answer is wrong. */
      code = mpint_cmp_mgn(ujn_uj, tmp);
      printf("mpint_cmp_mgn(ujn_uj, tmp) = %d (EQ = %d, GT = %d LT = %d)\n", code, MPINT_EQ, MPINT_GT, MPINT_LT);
    }
#endif
    if (mpint_cmp_mgn(ujn_uj, tmp) == MPINT_LT){
      /* add back, step D6 */
      if ((q0_ == 0) && (q1_ != 0)) {
	q1_--;
      }
      q0_--;
      /* subtract b to tmp */
      code = mpint_sub_mgn_inplace(tmp, b_new);
#ifdef DEBUG
      if (debug == TRUE) {
	printf("  subtract 1 to (q1 q0) = {");
	uint_print_hexa(q1_);
	printf(" ");
	uint_print_hexa(q0_);
	printf(" tmp = ");
	mpint_print_hexa(tmp);
	printf("\n");
      }
#endif
    }
    /* subtract tmp to ujn_uj */
    code = mpint_sub_mgn_inplace(ujn_uj, tmp);
    if (code != OK){
      return code;
    }
    if (ujn_uj->limbs[b_new->used] != 0) {
      return KO;
    }
    /* D5. set qj <= q_ */
    q->limbs[j] = q0_;
    /* there is the problem of q1_ non-zero */
    int i = j+1;
    while ((i < MPINTMAXSIZE) && (q1_ != 0)){
      q->limbs[i] += q1_;
      if (q->limbs[i] == 0) {
	q1_ = 1;
      }
      i++;
    }
    /* ok, so this step canceled the leading word of ujn_uj,
       now shift it by one word to the left and introduce a_new[j] */
    /* D7 */
    if (j > 0) {
      mpint_word_mul_mgn(ujn_uj, ujn_uj);
      ujn_uj->limbs[0] = a_new->limbs[j-1];
    }
  }
  /* D8 unnormalize */
  mpint_adjust_size_used(q);
  /* q is the quotient, the remainder is stored in ujn_uj but should be divided by d */
  code = mpint_div_uint(r, &r0, ujn_uj, d);
  mpint_adjust_size_used(r);
  if (code != OK) {
    return code;
  }
  if (r0 != 0) {
    return KO;
  }
  return OK;
}

 int mpint_add_uint_mgn_inplace(mpint_t r, UINT a){
/* increment in place a mpint: r <- r+a
 * [in,out] r input and output
 * [in] a single precision
 */
  UINT carry = a;
  int i = 0;
  while ((i < r->used) && (carry != 0)) {
    r->limbs[i] += carry;
    if (r->limbs[i] < carry) {
      carry = 1;
    } else {
      carry = 0;
    }
    i++;
  }
  if ((i == r->used) && (carry != 0)){
    if (r->used == MPINTMAXSIZE) {
      return ERROR_CARRY_OVERFLOW;
    }
    r->limbs[r->used] = carry;
    r->used++;
  }
  return OK;
}

/* Euclidean division with sign */
#ifdef DEBUG
int mpint_div(mpint_t q, mpint_t r, mpint_t a, mpint_t b, int debug){
#else
int mpint_div(mpint_t q, mpint_t r, mpint_t a, mpint_t b){
#endif
  /* Euclidean division a = b * q + r with sign: a is a relative integer, b >= 0, 0 <= r < b
   * [in] a first oprand, dividende, can be negative or positive
   * [in] b second operand, divisor, should be positive
   * [out] r remainder, 0 <= r < b
   * [out] q quotient, can be positive or negative
   */
  int code;
  if (b->sign == NEG) {
    return ERROR_DIVISION_BY_ZERO;
  }
#ifdef DEBUG
  if (debug == TRUE) {
    printf("DEBUG mode activated\n");
  }
  code = mpint_div_mgn(q, r, a, b, debug);
#else
  code = mpint_div_mgn(q, r, a, b);
#endif
  /* just in case there was some mpint_deep_copy but with negative a or b... --> should be fixed now
  q->sign = ZPOS;
  r->sign = ZPOS;
  */
  if (code != OK) {
    return code;
  }
  /* now adjust the signs of q and r according to the signs of a and b */
  /* a > 0, => q->sign = b->sign */
  if (a->sign == ZPOS) {
    q->sign = b->sign;
    return OK;
  }
  if (a->sign == NEG) {
    /* |a| = |b| * |q| + |r|
       b > 0:
      -|a| = |b| *-|q| - |r|
      if r != 0:
        a  =  b  *-|q| - b + b - |r|
        a  =  b  *-(|q|+1) + (b - |r|)
       b < 0:
      -|a| = -|b| * |q| - |r|
      if r != 0:
        a  =  b  * |q| - |b| + |b| - |r|
        a  =  b  * (|q|+1) + (|b| - |r|)
     in all cases, if r!=0, then q=(oppositive of b sign)(|q|+1), r = |b|-|r|
     */
    if (mpint_is_zero(r)) {
      if (b->sign == ZPOS) {
	q->sign = NEG;
      }
      return OK;
    }
    code = mpint_add_uint_mgn_inplace(q, 1);
    if (code != OK) {
      return code;
    }
    if (b->sign == ZPOS) {
      q->sign = NEG;
    }
#ifdef DEBUG
    if (debug == TRUE) {
      printf("r = ");
      mpint_print_hexa(r); /* r can be negative here... */
      printf(" b = ");
      mpint_print_hexa(b);
      printf(" call r = b-r -> r = ");
    }
#endif
    code = mpint_sub_mgn_inplace_swap(r, b);/* r = b-r */
#ifdef DEBUG
    if (debug == TRUE) {
      mpint_print_hexa(r);
    }
#endif
    return code;
  }
}

/* PGCD */

int uint_gcd(UINT *r, UINT a, UINT b){
  /* Greatest Common Divisor of a and b
   * [in] a first operand
   * [in] b second operand
   * [out] r result: gcd(a,b), positive, 1 <= r <= min(a, b)
   * Euclidean algorithm, Knuth Volume 2, p. 333, Section 4.5.2
   * Algorithm A p. 337
   * gcd(0, 0) = 0, gcd(u, 0) = |u|, gcd(u, v) = gcd(v, u), gcd(-u, v) = gcd(u, v)
   */
  UINT a_, b_, r_;
  if (a < b) {
    a_ = b;
    b_ = a;
  } else {
    a_ = a;
    b_ = b;
  }
  if (b_ == 0) {
    *r = a_;
    return OK;
  }
  while (b_ != 0) {
    r_ = a_ % b_;
    a_ = b_;
    b_ = r_;
  }
  *r = a_;
  return OK;
}
 
int mpint_gcd_uint(UINT *r, mpint_t a, UINT b){
  /* r = GCD(a, b) where a is multi-precision and b is simple-precision
   * [out] r, simple precision because 0 <= r < b
   * [in] a first operand, multi-precision
   * [in] b second operand, single-precision
   * if b = 0 and a non-zero and not single-precision, then r = 0 by convention
   */
  if (a->used == 1){
    return uint_gcd(r, a->limbs[0], b);
  }
  /* a->used > 1 and then |a| > b */
  if (b == 0){
    *r = 0;
    return OK;
  }
  int code;
  mpint_t q;
  UINT r1;
  code = mpint_div_uint(q, &r1, a, b);
  if (code != OK) {
    return code;
  }
  if (r1 == 0) {
    *r = b;
    return OK;
  }
  return uint_gcd(r, b, r1);
}

#ifdef DEBUG
int mpint_gcd(mpint_t r, mpint_t a, mpint_t b, int debug){
#else
int mpint_gcd(mpint_t r, mpint_t a, mpint_t b){
#endif
  /* Greatest Common Divisor of |a| and |b|
   * [in] a first operand
   * [in] b second operand
   * [out] r result: gcd(a,b), positive, 1 <= r <= min(|a|, |b|)
   * Euclidean algorithm, Knuth Volume 2, p. 333, Section 4.5.2
   * Algorithm A p. 337
   * gcd(0, 0) = 0, gcd(u, 0) = |u|, gcd(u, v) = gcd(v, u), gcd(-u, v) = gcd(u, v)
   */
  mpint_t q, a_, b_;
  mpint_ptr ptr = r, pta = a_, ptb = b_, pta_tmp;
  int code = 0;
  if (mpint_cmp_mgn(a, b) == MPINT_LT) {
    mpint_deep_copy(a_, b);
    mpint_deep_copy(b_, a);
  } else {
    mpint_deep_copy(a_, a);
    mpint_deep_copy(b_, b);
  }
  if (mpint_is_zero(ptb) == TRUE){
    mpint_deep_copy(r, pta);
    return OK;
  }
  int i = 0;
  while (mpint_is_zero(ptb) == FALSE) {
#ifdef DEBUG    
    if (debug == TRUE) {
      printf("i=%d in while loop gcd, a = ", i);
      mpint_print_hexa(pta);
      printf(" b = ");
      mpint_print_hexa(ptb);
      printf("\ncall mpint_div_mgn(q, r, a, b)\n");
    }
    code = mpint_div_mgn(q, ptr, pta, ptb, debug);
    if (debug == TRUE) {
      printf("outside mpint_div_mgn, code = %d, outputs are q = ", code);
      mpint_print_hexa(q);
      printf(" r = ");
      mpint_print_hexa(ptr);
      printf("\n");
    }
#else
    code = mpint_div_mgn(q, ptr, pta, ptb);
#endif
    if (code != OK) {
      return code;
    }
    /* forget about q */
    /* a_ <- b_ */
    /* b_ <- r */
    pta_tmp = pta;
    pta = ptb;
    ptb = ptr;
    ptr = pta_tmp;
    i++;
  }
  if (r != pta) {
    mpint_deep_copy(r, pta);
    r->sign = ZPOS;
  }
  return OK;
}

int mpint_binary_gcd(mpint_t r, mpint_t a, mpint_t b){
  /* Greatest Common Divisor of |a| and |b|
   * [in] a first operand
   * [in] b second operand
   * [out] r result: gcd(a,b), positive, 1 <= r <= min(|a|, |b|)
   * Euclidean algorithm, Knuth Volume 2, p. 333, Section 4.5.2
   * Algorithm B p. 338
   * gcd(0, 0) = 0, gcd(u, 0) = |u|, gcd(u, v) = gcd(v, u), gcd(-u, v) = gcd(u, v)
   */
  return OK;
}

/* auxiliary function for xgcd */
int mpint_sub_mgn_inplace_swap(mpint_t r, mpint_t a){
  /* subtraction of the magnitudes (absolute values), r <- a - r
   * [in,out] mpint_t r: 2nd operand and result where to store the new value
   * [in] mpint_t a: 1st operand
   * [out] return: an error code (OK, ERROR_CARRY_OVERFLOW)
   * subtract the absolue value of r from a and store into r: r = |a| - |r| (no sign is checked)
   * assume |a| >= |r|
   * see also int mpint_sub_mgn_inplace(mpint_t r, mpint_t a)
   */
  int i;
  /* assume |a| >= |r| and in particular, a->used >= r->used */
  UINT carry = 0;
  UINT tmp;
  for (i = 0; i < r->used; i++){
    /* in two subtractions to be sure to catch the new carry */
    /* r[i] = a[i]-r[i]-carry */
    tmp = a->limbs[i] - carry;
    if ((a->limbs[i] >= carry) && (tmp >= r->limbs[i])){
      carry = 0;
    }else{/* r[i] = 2^WORDSIZE + a[i] - r[i] - carry */
      carry = 1;
    }
    r->limbs[i] = tmp - r->limbs[i];
  }
  /* now the most significant limbs of a, assume the limbs of r are 0 */
  for (i = r->used; i < a->used; i++){/* r[i] = 2^WORDSIZE + a[i] - carry */
    if (a->limbs[i] < carry){
      r->limbs[i] = a->limbs[i] - carry;
      carry = 1;
    }else{/* r[i] = a[i]-carry */
      r->limbs[i] = a->limbs[i] - carry;
      carry = 0;
    }
  }
  /* recompute used, knowing that new r->used <= a->used */
  r->used = a->used;
  while((r->used > 1) && (r->limbs[r->used-1] == 0)){
    r->used--;
  }
  if (carry != 0) {
    return ERROR_CARRY_OVERFLOW;
  }
  return OK;
}

int mpint_sub_inplace(mpint_t r, mpint_t a){
  /* subtraction of relative integers (with sign), in place: r <- r - a
   * [in] mpint_t r: first operand and result where to store the new value
   * [in] mpint_t a: second operand
   * [out] return: an error code (OK, KO, ERROR_CARRY_OVERFLOW)
   */
  int r_cmp_a;
  if ((r->sign == ZPOS) && (a->sign == NEG)){
    /* r-> sign = ZPOS; -> already */
    return mpint_add_mgn_inplace(r, a);
  }
  if ((r->sign == NEG) && (a->sign == ZPOS)){
    /* r->sign = NEG; -> already */
    return mpint_add_mgn_inplace(r, a);
  }
  r_cmp_a = mpint_cmp_mgn(r, a);
  if ((r->sign == ZPOS) && (a->sign == ZPOS)){
    if ((r_cmp_a == MPINT_EQ) || (r_cmp_a == MPINT_GT)){
      /* r->sign = ZPOS; -> already */
      return mpint_sub_mgn_inplace(r, a);
    }
    r->sign = NEG;
    return mpint_sub_mgn_inplace_swap(r, a); /* r <- a - r --> not yet implemented... */
  }
  if ((r->sign == NEG) && (a->sign == NEG)){
    if ((r_cmp_a == MPINT_EQ) || (r_cmp_a == MPINT_LT)){
      r->sign = ZPOS;
      return mpint_sub_mgn_inplace_swap(r, a); /* --> r <- a - r */
    }
    r->sign = NEG;
    return mpint_sub_mgn_inplace(r, a); /* r <- r - a */
  }
  return KO;
}

/* PGCD etendu */
int mpint_xgcd(mpint_t gcd, mpint_t u, mpint_t v, mpint_t a, mpint_t b){
  /* eXtended Greatest Common Divisor of |a| and |b|, gcd(a,b) = u*a + b*v (with sign!)
   * [in] a first operand
   * [in] b second operand
   * [out] gcd: gcd(a,b), positive, 1 <= gcd <= min(|a|, |b|)
   * [out] u  : relative multi-precision integer, gcd = u*a + b*v
   * [out] v  : relative multi-precision integer, gcd = u*a + b*v
   * eXtended Euclidean algorithm, Knuth Volume 2, p. 333
   * Algorithm X p. 342
   */
  if (mpint_is_zero(a) == TRUE) {
    mpint_deep_copy(gcd, b);
    mpint_set_zero(u);
    mpint_set_one(v);
    /* ensure that the gcd is positive, not negative (if b < 0) */
    if (b->sign == NEG) {
      gcd->sign = ZPOS;
      v->sign = NEG;
    }
    return OK;
  }
  if (mpint_is_zero(b) == TRUE) {
    mpint_deep_copy(gcd, a);
    mpint_set_one(u);
    mpint_set_zero(v);
    /* ensure that the gcd is positive, not negative (if a < 0) */
    if (a->sign == NEG) {
      gcd->sign = ZPOS;
      u->sign = NEG;
    }
    return OK;
  }
  /* if |a| < |b|, swap a and b and remember */
  mpint_t r0, u0, v0, q1, r2;
  mpint_ptr ptr2 = r2, ptr1 = gcd, ptr0 = r0, ptu0 = u0, ptv0 = v0, ptu1 = u, ptv1 = v, ptr_tmp; /* ptr_tmp to swap ptr */
  int swap = FALSE;
  if (mpint_cmp_mgn(a, b) == MPINT_LT) {
    mpint_deep_copy(ptr1, a);
    mpint_deep_copy(ptr0, b);
    swap = TRUE;
  } else {
    mpint_deep_copy(ptr0, a);
    mpint_deep_copy(ptr1, b);
  }
  mpint_set_one(ptu0);
  mpint_set_zero(ptv0);
  mpint_set_zero(ptu1);
  mpint_set_one(ptv1);
  /* u0*a + v0*b == r0 >= 0
     u1*a + v1*b == r1 >= 0 */
  if (ptr1->sign == NEG) {
    ptr1->sign = ZPOS;
    ptv1->sign = NEG;
  }
  if (ptr0->sign == NEG) {
    ptr0->sign = ZPOS;
    ptu0->sign = NEG;
  }
  /* (u1=0) * a + (v1 = 1) * b = b ( = r1) */
  /* (u0=1) * a + (v0 = 0) * b = a ( = r0) */
  int code;
#ifdef DEBUG
  code = mpint_div_mgn(q1, ptr2, ptr0, ptr1, FALSE); /* and r0 = a >= r1 = b */
#else
  code = mpint_div_mgn(q1, ptr2, ptr0, ptr1); /* and r0 = a >= r1 = b */
#endif
  /* |r1| = |q1| * |r0| + |r2| */
  /* if r1 or r0 are negative, what happens? */
  /* if r1 < 0 and r0 < 0, -> -|r1| = |q1| * -|r0| - |r2| -> -|r1| = |q1| * -|r0| -|r0| + |r0| - |r2| */
  if (code != OK){
    return code;
  }
  while (mpint_is_zero(ptr2) == FALSE) {
    /* u2 = u0 - q1*u1
       u0 <- u1
       u1 <- u2
       v2 = v0 - q1*v1
       v0 = v1
       v1 = v2
       r0 = r1
       r1 = r2
       r2 = r0 % r1
       q1 = r0 // r1
    */
    mpint_mul(ptr0, q1, ptu1);     /* r0 <- q1 * u1, can be negative */
    mpint_sub_inplace(ptu0, ptr0); /* u0 <- u0 - r0, with sign */
    mpint_mul(ptr0, q1, ptv1);     /* r0 <- q1 * v1, can be negative */
    mpint_sub_inplace(ptv0, ptr0); /* v0 <- v0 - r0, with sign */
    ptr_tmp = ptu0;                /* u1 <-> u0 */
    ptu0 = ptu1;
    ptu1 = ptr_tmp;
    ptr_tmp = ptv0;                /* v1 <-> v0 */
    ptv0 = ptv1;
    ptv1 = ptr_tmp;
    /* r0 <- r1, r1 <- r2 */
    ptr_tmp = ptr0;
    ptr0 = ptr1;
    ptr1 = ptr2;
    ptr2 = ptr_tmp;
#ifdef DEBUG
    code = mpint_div_mgn(q1, ptr2, ptr0, ptr1, FALSE); /* and r0 >= r1 != 0 */
#else
    code = mpint_div_mgn(q1, ptr2, ptr0, ptr1); /* and r0 >= r1 != 0 */
#endif
    if (code != OK){
      return code;
    }
  }
  /* copy the final result gcd=r1, u=u1, v=v1 in the appropriate mpint but check before that it is not overriding some data */
  /* gcd = ptr1 */
  /* u = ptu1 */
  /* v = ptv1 */
  /* free mpint not gcd, u or v is q1 */
  /* q1 is free anyway... */
  ptr_tmp = q1;
  if (gcd != ptr1) {
    /* pointers differ, affect ptr1 to gcd but check that gcd does not contain data first */
    if (gcd == ptu1) { /* move the target pointed by ptu1 to a temporary place */
      mpint_deep_copy(ptr_tmp, gcd);
      ptu1 = ptr_tmp;
    } else if (gcd == ptv1) {
      mpint_deep_copy(ptr_tmp, gcd);
      ptv1 = ptr_tmp;
    }
    mpint_deep_copy(gcd, ptr1);
    ptr_tmp = ptr1;
  }

  if (swap == TRUE) {
    /* u,v = v1, u1 */
    /* u <- ptv1 */
    if (u != ptv1) {
      if (u == ptu1) {
	mpint_deep_copy(ptr_tmp, ptu1);
	ptu1 = ptr_tmp;
      }
      mpint_deep_copy(u, ptv1);
    }
    if (v != ptu1) {
      mpint_deep_copy(v, ptu1);
    }
    return OK;
  }
  /* u, v = u1, v1 */
  if (u != ptu1) {
    if (u == ptv1) {
      mpint_deep_copy(ptr_tmp, ptv1);
      ptv1 = ptr_tmp;
    }
    mpint_deep_copy(u, ptu1);
  }
  if (v != ptv1) {
    mpint_deep_copy(v, ptv1);
  }
  return OK;
}

int mpint_binary_xgcd(mpint_t gcd, mpint_t u, mpint_t v, mpint_t a, mpint_t b){
  /* eXtended Greatest Common Divisor of |a| and |b|, gcd(a,b) = u*a + b*v (with sign!)
   * [in] a first operand
   * [in] b second operand
   * [out] gcd: gcd(a,b), positive, 1 <= gcd <= min(|a|, |b|)
   * [out] u  : relative multi-precision integer, gcd = u*a + b*v
   * [out] v  : relative multi-precision integer, gcd = u*a + b*v
   * eXtended Euclidean algorithm, Knuth Volume 2, 4.5.2, p. 356, Exercice 39. Solutions p. 646
   * Algorithm Y
   */
  return OK;  
}
/* inverse modulaire */
int modint_inv(mpint_t r, mpint_t a, mpint_t m){
  /* inverse of a modulo m
   * [in] a, operand, 0 <= a < m expected
   * [in] m, module, 1 < m
   * [out] r, result r = 1/a mod m
   * the inverse is computed thanks to the formula with xgcd: gcd(a, m) = u*a + v*m
   * if gcd(a,m) is not 1, there is no inverse and ERROR_DIVISION_BY_ZERO is returned
   */
  int code;
  mpint_t gcd, v;
  mpint_set_zero(r);
  if (m->sign == NEG) {
    return ERROR_FORMAT;
  }
  if (mpint_is_zero(m) == TRUE) {
    return ERROR_DIVISION_BY_ZERO;
  }
  if ((a->sign == NEG) || (mpint_cmp_mgn(a, m) != MPINT_LT)) {
    return ERROR_INPUT_NOT_REDUCED;
  }
  code = mpint_xgcd(gcd, r, v, a, m);
  if (code != OK) {
    mpint_set_zero(r);
    return code;
  }
  if (mpint_is_one(gcd) == FALSE) {
    mpint_set_zero(r);
    return ERROR_DIVISION_BY_ZERO;
  }
  if (r->sign == NEG) {
    /* r <- r + m, since r is negative, r <- m - |r| */
    /* mpint_add_inplace(r, m); is not implemented */
    mpint_sub_mgn_inplace_swap(r, m);
    r->sign = ZPOS;
  }
  return OK;
}

/* conversion en représentation de Montgomery */
/* a -> a * R mod m --> R étant une puissance de 2^WORD, on a dit qu'on faisait des doublements et des réductions si besoin */
int modint_mod_to_montgomery(mpint_t r, mpint_t m){
  /* Compute the Montgomery representation of r, r = r * R mod m, R = 2^(WORD * m->used)
   * [in, out] r, operand, 0 <= r < m expected
               and result, r = r * R mod m, 0 <= r < m
   * [in] m, module, 1 < m
   */
  if (m->sign == NEG) {
    return ERROR_FORMAT;
  }
  if (mpint_is_zero(m) == TRUE) {
    return ERROR_DIVISION_BY_ZERO;
  }
  if ((r->sign == NEG) || (mpint_cmp_mgn(r, m) != MPINT_LT)) {
    return ERROR_INPUT_NOT_REDUCED;
  }
  if (mpint_is_zero(r)) {
    return OK;
  }
  int code = 0;
  for(int i = 0; i < m->used; i++) {
    for (int j = 0; j < WORD; j++) {
      code = mpint_dbl_mgn(r);
      if (code != OK) {
	return code;
      }
      if (mpint_cmp_mgn(r, m) != MPINT_LT) {
	code = mpint_sub_mgn_inplace(r, m);
	if (code != OK) {
	  return code;
	}
	/* since 0 <= r < m,
	         0 <= 2*r < 2*m, and
	        -m <= 2*r-m < m
	   so one subtraction is enough (no loop needed)
	*/
      }
    }
  }
  return OK;
}

int montgomery_m_prime(UINT *m_prime, mpint_t m){
  /* compute m_prime = -1/m mod 2^WORD with xgcd
   * [in] m module
   * [out] m_prime = -m^(-1) mod 2^WORD
   */
  if (mpint_is_even(m) == TRUE) {
    return ERROR_IS_EVEN;
  }
  mpint_t gcd, u, v, base;
  /* set base to be equal to 2^WORD: 2 limbs, least significant = 0, most significant = 1 */
  mpint_set_zero(base);
  base->limbs[1] = 1;
  base->used = 2;
  int code = mpint_xgcd(gcd, u, v, m, base);
  if (code != OK) {
    return code;
  }
  if (mpint_is_one(gcd) == FALSE){
    return ERROR_DIVISION_BY_ZERO;
  }
  mpint_adjust_size_used(u);
  if (u->used != 1) {
    return KO;
  }
  /* one wants the negative of u, mutualize with ensuring u > 0 */
  /* if u < 0, then the answer is m' = -u = |u| > 0, do nothing */
  /* if u > 0, the answer is m' = -u = base - u */
  /* TODO */
  if (u->sign == ZPOS) {
    mpint_sub_mgn_inplace_swap(u, base); /* u <- base - |u| */
  }
  *m_prime = u->limbs[0];
  return OK;
}

int montgomery_r_inv(mpint_t Rinv, mpint_t m){
  /* compute Rinv = 1/R mod m, R = 2^(WORD*m->used)
   * [in] m module
   * [out] Rinv = R^(-1) mod m
   * since R fills all the space of a mpint as it is 2^(WORD*m->used),
   * it will fail in mpint_div -> precompute manually (R-m) that should fits in the limbs
   */
  /* 2^(WORD*m->used) - m */
  mpint_set_zero(Rinv);
  if (m->used == MPINTMAXSIZE) {
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  if (mpint_is_zero(m) == TRUE){
    ERROR_INPUT;
  }
  if (mpint_is_one(m) == TRUE){
    ERROR_INPUT;
  }
  /* Rinv = 2^(WORD*m->used) */
  mpint_t R;
  mpint_set_zero(R);
  R->used = m->used+1;
  R->limbs[R->used-1] = 1;
  /* Rinv = Rinv - m */
  mpint_sub_mgn_inplace(R, m);
  /* now, xgcd, where R should fit in the same size as m->used */
  if (R->used >= MPINTMAXSIZE) {
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  mpint_t gcd, v;
  int code = mpint_xgcd(gcd, Rinv, v, R, m);
  if (code != OK) {
    return code;
  }
  if (mpint_is_one(gcd) == FALSE){
    return ERROR_DIVISION_BY_ZERO;
  }
  /* Rinv should be smaller than m in magnitude */
  if (mpint_cmp_mgn(Rinv, m) != MPINT_LT) {
    /* or reduce? */
    return ERROR_INPUT_NOT_REDUCED;
  }
  /* Rinv can be negative, adjust */
  if (Rinv->sign == NEG) {
    mpint_sub_mgn_inplace_swap(Rinv, m);/* Rinv <- Rinv + m = m - |Rinv| */
    Rinv->sign = ZPOS;
  }
  return OK;
}

int modint_montgomery_to_mod(mpint_t r, mpint_t m, UINT m_prime){
  /* Undo the Montgomery representation of r, r = r * R^(-1) mod m, R = 2^(WORD * m->used)
   * [in, out] r, operand, 0 <= r < m expected
               and result, r = r * R^(-1) mod m, 0 <= r < m
   * [in] m, module, 1 < m
   * the computation is done implicitly thanks to modint_mul(r, r, 1, m, m_prime)
   */
   mpint_t tmp, one;
   mpint_set_one(one);
   mpint_deep_copy(tmp, r);
   mpint_set_zero(r);
   return modint_mul(r, tmp, one, m, m_prime);
}

int mpint_montgomery_to_mod(mpint_t a, mpint_t m, mpint_t r_inv){
  /* Undo the Montgomery representation of a, a = a * R^(-1) mod m, R = 2^(WORD * m->used)
   * [in, out] a, operand, 0 <= a < m is expected
               and result, a = a * R^(-1) mod m, 0 <= a < m
   * [in] m, module, 1 < m
   * [in] r_inv = R^(-1) mod m, R = 2^(WORD * m->used)
   * note that modint_mul cannot be used here to perform a * Rinv mod m
   * as the aim is to cancel the R factor in a.
   * a non-satisfying solution here is to do a double-and-add over r_inv bits
   */
  /* read the bits of r_inv */
  /* use dbl and add inplace */
  mpint_t a0;
  mpint_deep_copy(a0, a);
  int i, j;
  mpint_adjust_size_used(r_inv);
  j = r_inv->used-1;
  UINT eij, ej = r_inv->limbs[j];
  /* assume that ej != 0 */
  i = WORD-1;
  while ((i > 0) && ((ej >> i) == 0)) {
    i--;
  }
  /* the leading non-zero bit of r corresponds to initializing the result to a */
  i--;
  /* first loop on the leading word of r */
  for ( ; i >= 0; i--){
    /* a = n-1 < n
       2*a = 2*n-2 < 2n (so 1 subtraction)
       2*a+a = 3*n-3 < 3n
       3*a = 3*n-3 -> 3*n-3-2*n = n-3 mod n
       reduce each time
     */
    mpint_dbl_mgn(a); /* dbl */
    if (mpint_cmp_mgn(a, m) != MPINT_LT) { /* a is no more reduced mod m */
      mpint_sub_mgn_inplace(a, m); /* a <- a - m */
    }
    eij = (ej >> i) & 1;
    if (eij != 0){
      mpint_add_mgn_inplace(a, a0); /* add */
      if (mpint_cmp_mgn(a, m) != MPINT_LT) { /* a is no more reduced mod m */
	mpint_sub_mgn_inplace(a, m); /* a <- a - m */
      }
    }
  }
  /* main loop */
  for (j = r_inv->used-2; j >= 0; j--){
    ej = r_inv->limbs[j];
    for (i = WORD-1; i >= 0; i--){
      mpint_dbl_mgn(a); /* dbl */
      if (mpint_cmp_mgn(a, m) != MPINT_LT) { /* a is no more reduced mod m */
	mpint_sub_mgn_inplace(a, m); /* a <- a - m */
      }
      eij = (ej >> i) & 1;
      if (eij != 0){
	mpint_add_mgn_inplace(a, a0); /* add */
	if (mpint_cmp_mgn(a, m) != MPINT_LT) { /* a is no more reduced mod m */
	  mpint_sub_mgn_inplace(a, m); /* a <- a - m */
	}
      }
    }
  }
  return OK;
}

/* generation de nombres aleatoires */

int mpint_rand_odd_given_bits(mpint_t r, int bits){
  /* generate a random number r of exactly the number of bits, odd */
  if ((MPINTMAXSIZE - 1) * WORD < bits) {
    return ERROR_ABOVE_MPINTMAXSIZE;
  }
  r->used = bits / WORD;
  for(int i = 0; i < r->used; i++) {
    r->limbs[i] = (UINT) rand();
  }
  /* set 1 for the least significant bit -> odd */
  r->limbs[0] |= 1;
  r->limbs[r->used-1] |= (1 << (WORD - 1));
  /* set the leading bit of the most significant limb to be 1 */
  return OK;
}

int mpint_is_even(mpint_t a){
  /* return if a is even (TRUE/FALSE)
   * [in] a
   * return TRUE/FALSE
   */
  if ((a->limbs[0] & 1) == 0) {
    return TRUE;
  }
  return FALSE;
}

/* test de primalité de Fermat */

int mpint_set_uint(mpint_t r, UINT a){
  /* make a UINT as mpint_t with one limb
   * [in] a
   * [out] r
   */
  mpint_set_zero(r);
  r->limbs[0] = a;
  return OK;
}

#ifdef DEBUG
int mpint_is_prime_fermat(mpint_t value, UINT *witness, mpint_t n){
  /* Fermat (pseudo-)primality test
   * [in] n, odd integer
   * [out] value, the base a to the power (n-1) that does not give zero
   * [out] a, the witness base, a^(n-1) != 1 mod n => n is composite
   * return: error code (including n is even), or one of:
   * is probable prime, is composite
   */
#else
int mpint_is_prime_fermat(mpint_t n){
  /* Fermat (pseudo-)primality test
   * [in] n, odd integer
   * return: error code (including n is even), or one of:
   * is probable prime, is composite
   */
#endif
  /* check that n is odd, in fact n >= 3 */
  if ((n->sign == NEG) || (mpint_is_zero(n) == TRUE) || (mpint_is_one(n) == TRUE)) {
    return ERROR_INPUT;
  }
  if (mpint_is_even(n) == TRUE) {
    return ERROR_IS_EVEN;
  }
  /* compute n-1 */
  mpint_t n_1;
  mpint_set_one(n_1);
  mpint_sub_mgn_inplace_swap(n_1, n); /* n_1 <- n - 1 */

  /* Montgomery parameter m_prime */
  UINT n_prime;
  int code = montgomery_m_prime(&n_prime, n);
  if (code != OK) {
    return code;
  }
  /* take a base, a = 2 to start */
  UINT bases[8] = {2, 3, 5, 7, 11, 13, 17, 19};
  mpint_t a, base;
  int counter = 0;
  UINT n_mod_a;
  mpint_t one_montg;
  mpint_set_one(one_montg);
  code = modint_mod_to_montgomery(one_montg, n);
  if (code != OK) {
    return code;
  }
#ifndef DEBUG
  UINT w;
  UINT* witness = &w;
#endif
  while (counter < 8) {
    *witness = bases[counter];
    mpint_set_uint(a, *witness);
    if (mpint_cmp_mgn(a, n_1) == MPINT_LT){
      /* check just in case that gcd(a, n) = 1
	 since a is prime, it boils down to checking that n mod a is non-zero */
      code = mpint_div_uint(base, &n_mod_a, n, *witness);
      if (code != OK) {
	return code;
      }
      if (n_mod_a == 0) {
	return IS_COMPOSITE;
      }
      /* compute the Montgomery representation of a */
      code = modint_mod_to_montgomery(a, n); /* in place */
      if (code != OK) {
	return code;
      }
      code = modint_exp_mpint(base, a, n_1, n, n_prime);
      if (code != OK) {
	return code;
      }
      /* code = modint_montgomery_to_mod(base, n, n_prime); */
      /* Fermat test: a^(n-1) = 1 ? */
      if (mpint_cmp_mgn(base, one_montg) != MPINT_EQ) {
	return IS_COMPOSITE;
      }
    } else {
      counter = 8;
    }
    counter++;
  }
  return IS_PROBABLE_PRIME;
}

int mpint_div_pow_2_inplace(mpint_t r, int i){
  /* shift i bits to the right
   * [in,out] r
   * [in] i number of bits to shift, i >= 0
   * if i = 0, r stays unchanged
   * if i >= WORD, also shift the words
   * if i >= WORD * r->used, r is set to zero
   */
   if (i < 0) {
     return KO;
   }
   if (i == 0) {
     return OK;
   }
   if (i >= WORD * r->used) {
     mpint_set_zero(r);
     return OK;
   }
   int j = i / WORD;
   int k = i % WORD;
   for (int l = j; l < r->used; l++) {
     r->limbs[l-j] = r->limbs[l];
   }
   r->used -= j;
   /* now shift by k to the right */
   for (int l = 0; l+1 < r-> used; l++) {
     r->limbs[l] = (r->limbs[l] >> k) | (r->limbs[l+1] << (WORD-k));
   }
   r->limbs[r->used-1] >>= k;
   return OK;
}

/* TODO test de primalité de Miller Rabin */

int mpint_is_prime_miller_rabin(mpint_t n){
  /* TODO TP 6: Miller-Rabin primality test
   * [in] n, odd integer
   * return: error code (including n is even), or one of:
   * is probable prime, is composite
   * the bases tested are (at most) a = 2, 3, 5, 7, 11, 13, 17, 19
   */
  /* check that n is odd, in fact n >= 3 */
  if ((n->sign == NEG) || (mpint_is_zero(n) == TRUE) || (mpint_is_one(n) == TRUE)) {
    return ERROR_INPUT;
  }
  if (mpint_is_even(n) == TRUE) {
    return ERROR_IS_EVEN;
  }
  /* compute n-1 = 2^s * m */
  /* compute n-1 */
  mpint_t n_1, m, base1, base2, mont_one, mont_n_1;
  mpint_ptr a1 = base1, a2 = base2, ptr_tmp;
  mpint_set_one(m);
  mpint_sub_mgn_inplace_swap(m, n); /* m <- n - 1 */
  /* here compute the Montgomery representation of n-1 for later */
  mpint_deep_copy(n_1, m);
  mpint_deep_copy(mont_n_1, m);
  /* compute m = (n-1)/2^s */
  int i = 0;
  while (i < MPINTMAXSIZE && m->limbs[i] == 0) {
    i++;
  }
  int j = 0;
  while ((j < WORD) && ((m->limbs[i] >> j) & 1) == 0) {
    j++;
  }
  int s = i*WORD + j;
  int code = mpint_div_pow_2_inplace(m, s);
  if (code != OK) {
    return code;
  }

  /* set up a mechanism to work modulo n -> compute n_prime the inverse of n mod 2^WORD */
  UINT n_prime;
  code = montgomery_m_prime(&n_prime, n);
  if (code != OK) {
    return code;
  }
  /* take a base, a = 2 to start */
  UINT bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499};
  UINT witness, n_mod_a;
  /* also needed: the Montgomery representation of 1 and -1 for comparison */
  mpint_set_one(mont_one);
  code = modint_mod_to_montgomery(mont_one, n); /* in place */
  if (code != OK) {
    return code;
  }
  code = modint_mod_to_montgomery(mont_n_1, n); /* in place */
  if (code != OK) {
    return code;
  }
  int counter = 0;
  //int nb_bases = MAX(2, 11 - log2((double) n->used*WORD)); // 1024 : 2; 512 : 2 256 : 3
  int nb_bases = 2;
  while (counter < nb_bases) {
    witness = bases[counter];
    mpint_set_uint(a1, witness);
    if (mpint_cmp_mgn(a1, n_1) == MPINT_LT){
      /* check just in case that gcd(a, n) = 1
	    since a is prime, it boils down to checking that n mod a is non-zero */
      code = mpint_div_uint(a2, &n_mod_a, n, witness);
      if (code != OK) {
	      return code;
      }
      if (n_mod_a == 0) {
	      return IS_COMPOSITE;
      }
      /* compute the Montgomery representation of a */
      code = modint_mod_to_montgomery(a1, n); /* in place */
      if (code != OK) {
	      return code;
      }
      code = modint_exp_mpint(a2, a1, m, n, n_prime);
      if (code != OK) {
	      return code;
      }
      /* Miller Rabin test 1: a^m = 1 ? */
      if (mpint_cmp_mgn(a2, mont_one) != MPINT_EQ) {
	      /* second loop */
	      i = 0;
	      while ((i < s) && mpint_cmp_mgn(a2, mont_n_1) != MPINT_EQ) {
	        /* square the base */
	        modint_mul(a1, a2, a2, n, n_prime);
	        /* if a1 = 1 and a2 != -1 -> composite */
	        if (mpint_cmp_mgn(a1, mont_one) == MPINT_EQ) {
	          /* stop the loop if a1 = 1 as 1^i = 1, a non-trivial square root was found */
	          return IS_COMPOSITE;
	        }
	        ptr_tmp = a1;
	        a1 = a2;
	        a2 = ptr_tmp;
	        i++;
	      }
	      /* if a1 != 1 then n is composite */
	      if (mpint_cmp_mgn(a2, mont_one) != MPINT_EQ) {
	        return IS_COMPOSITE;
	      }
      }
    counter++;
    }
  }
  return IS_PROBABLE_PRIME;
}

int mpint_rand_prime_given_bits(mpint_t r, int bits) {
  do {
    mpint_rand_odd_given_bits(r, bits);
    mpint_print_str_hex(r);
    printf(": %d\n", mpint_is_prime_miller_rabin(r));
  } while (mpint_is_prime_miller_rabin(r) != IS_PROBABLE_PRIME);
  return OK;
}

/* print functions */

void uint_print_hexa(UINT u){
#if WORD == 64
  printf("%#018lx", u);
#else
  printf("%#010x", u);
#endif
}

void uint_print_dec(UINT u){
#if WORD == 64
  printf("%ul", u);
#else
  printf("%u", u);
#endif
}

void mpint_print_hexa(mpint_t a){
  int i;
  printf("{used=%d, sign=%d, limbs={", a->used, a->sign);
  for (i = 0; i < MPINTMAXSIZE-1; i++){
#if WORD == 64
    printf("%#lx, ", a->limbs[i]);
#else
    printf("%#x, ", a->limbs[i]);
#endif
  }
  i = MPINTMAXSIZE-1;
#if WORD == 64
  printf("%#lx}}", a->limbs[i]);
#else
  printf("%#x}}", a->limbs[i]);
#endif
}

void mpint_print_dec(mpint_t a){
  int i;
  printf("{used=%d, sign=%d, limbs={", a->used, a->sign);
  for (i = 0; i < MPINTMAXSIZE-1; i++){
#if WORD == 64
    printf("%ul, ", a->limbs[i]);
#else
    printf("%u, ", a->limbs[i]);
#endif
  }
  i = MPINTMAXSIZE-1;
#if WORD == 64
  printf("%u}}", a->limbs[i]);
#else
  printf("%u}}", a->limbs[i]);
#endif
}

void mpint_print_str_hex(mpint_t a){
  /* print as a string the limbs of a
   * [in] mpint_t a
   */
  /* the hi bits are written at the left */
  /* the low significant bits of a are written at the right */
  /* last word (msb), may be not full */
  if (a->sign == NEG){
    printf("-");
  }
#if WORD == 64
  printf("%#lx", a->limbs[a->used - 1]);
#else
  printf("%#x", a->limbs[a->used - 1]);
#endif
  for(int i = a->used - 2; i >= 0; i--){
#if WORD == 64
    printf("%016lx", a->limbs[i]);
#else
    printf("%08x", a->limbs[i]);
#endif
  }
}

void mpint_println_str_hex(mpint_t a){
  mpint_print_str_hex(a);
  printf("\n");
}