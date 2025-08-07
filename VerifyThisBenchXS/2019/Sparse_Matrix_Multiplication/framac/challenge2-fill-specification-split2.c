#include <stddef.h>

typedef struct {
  size_t row;
  size_t col;
  int v;
} coo;

/*@ lemma assoc:
     \forall integer a,b,c;
      (int)(a + (int)(b+c)) == (int)((int)(a+b)+c);
*/

/*@ predicate well_sorted(coo* mat, integer length) =
  \forall integer i,j; 0<=i<j< length ==>
    mat[i].row <= mat[j].row &&
    (mat[i].row == mat[j].row ==> mat[i].col < mat[j].col);
*/

/*@ predicate non_zero_coeff(coo* mat, integer length) =
  \forall integer idx; 0 <= idx < length ==> mat[idx].v !=0;
*/

/*@ predicate well_dimensioned(coo* mat, integer length, integer dim) =
  \forall integer idx; 0 <= idx < length ==>
  mat[idx].row < dim && mat[idx].col < dim;
*/

/*@ predicate well_formed(coo* mat, integer length,integer dim) =
  well_sorted(mat,length) && non_zero_coeff(mat,length)
  && well_dimensioned(mat,length,dim);
*/

/*@
  lemma wf_extend:
    \forall coo* mat, integer l1,l2, dim;
     0<l1<=l2 ==> well_formed(mat,l2,dim) ==> well_formed(mat,l1,dim);
*/

/*@ logic int coeff(
      coo* c,integer idx, integer length, integer i, integer j) =
      (idx >= length || idx < 0) ? (int)0 :
         (c[idx].row > i) ? (int)0 :
         (c[idx].row < i) ? coeff(c,idx+1,length,i,j) :
           (c[idx].col > j) ? (int)0 :
           (c[idx].col < j) ? coeff(c,idx+1,length,i,j) :
           c[idx].v;
*/

/*@
 lemma coeff_ident{L1,L2}:
  \forall coo* c, integer length, i, j;
  (\forall integer idx; 0<=idx<length ==> \at(c[idx],L1) == \at(c[idx],L2))
  ==>
  coeff{L1}(c,0,length,i,j) == coeff{L2}(c,0,length,i,j);

 lemma model_coeff_zero:
    \forall coo* c, integer length, dim, i, j;
    well_formed(c,length, dim) ==>
    coeff(c,0,length,i,j) == 0 ==>
    (\forall integer idx; 0<= idx < length ==>
      c[idx].row != i || c[idx].col !=j);

 lemma model_coeff_current:
  \forall coo* c, integer idx, dim;
  well_formed(c,idx,dim) ==> idx > 0 ==>
    coeff(c,0,idx,c[idx-1].row,c[idx-1].col) == c[idx-1].v;

 lemma model_coeff_submat:
    \forall coo* c, integer idx, dim, i, j;
    well_formed(c,idx,dim) ==> idx > 0 ==>
    i != c[idx-1].row || j != c[idx-1].col ==>
    coeff(c,0,idx,i,j) == coeff(c,0,idx-1,i,j);

 lemma model_coeff_smaller:
  \forall coo* c, integer idx, idx2, dim;
  well_formed(c,idx,dim) ==> idx > idx2 >=0 ==>
    coeff(c,0,idx2,c[idx-1].row,c[idx-1].col) == 0;

 lemma model_coeff_exists:
  \forall coo* c, integer length, dim, i, j;
  well_formed(c,length,dim) ==>
  (\exists integer idx; 0<= idx < length && c[idx].row == i && c[idx].col == j)
  ==>
  (\forall integer idx; 0 <= idx <length && c[idx].row == i && c[idx].col ==j
    ==> c[idx].v == coeff(c,0,length,i,j));
*/

/*@ logic int l_vec_mult(int* vec, coo* c,
                             integer pos_v, integer length_v,
                             integer j,
                             integer pos_c,
                             integer length_c) =
       pos_v >= length_v ? (int)0
       : (int)(l_vec_mult(vec,c,pos_v+1,length_v,j,pos_c,length_c)
               + (int)(vec[pos_v] * coeff(c,pos_c,length_c,pos_v,j)));
*/

/*@
  lemma l_vec_mult_ident{L1,L2}:
  \forall int* vec, coo* c, integer length_v, j, length_c;
  (\forall integer idx_v; 0 <= idx_v < length_v ==>
    \at(vec[idx_v],L1) == \at(vec[idx_v],L2)) ==>
  (\forall integer idx_c; 0 <= idx_c < length_c ==>
    \at(c[idx_c],L1) == \at(c[idx_c],L2)) ==>
  l_vec_mult{L1}(vec,c,0,length_v,j,0,length_c) ==
  l_vec_mult{L2}(vec,c,0,length_v,j,0,length_c);
*/

/*@ ghost
/@ requires \valid(vec + (0 .. length - 1));
   ensures all_zeroes: \forall integer j; 0 <= j < length ==>
     l_vec_mult(vec,mat,0,length,j,0,0) == 0;
   assigns \nothing;
@/
void zero_coeffs(int* vec, size_t length, coo* mat) {
  /@ loop invariant all_zeroes:
    \forall integer j; 0<= j < length ==>
       l_vec_mult(vec,mat,i,length,j,0,0) == 0;
     loop invariant lemma_ind: 0<=i<=length;
     loop assigns i;
  @/
  for (size_t i = length; i > 0; i--) { }
}
*/

/*@ ghost
/@ requires \valid(vec+(0 .. length - 1));
   requires \valid(mat+(0 .. mat_length - 1));
   requires mat_length > 0;
   requires well_formed(mat, mat_length, length);
   assigns \nothing;
   ensures neq_coeff:
     \forall integer j;
     0 <= j < length && j != mat[mat_length-1].col ==>
     l_vec_mult(vec,mat,0,length,j,0,mat_length) ==
     l_vec_mult(vec,mat,0,length,j,0,mat_length-1);
   ensures eq_coeff:
     \let i = mat[mat_length-1].row;
     \let j = mat[mat_length-1].col;
     l_vec_mult(vec,mat,0,length,j,0,mat_length) ==
       (int)(l_vec_mult(vec,mat,0,length,j,0,mat_length-1) +
             (int)(vec[i] * mat[mat_length-1].v));
@/
void compute_coeff(int* vec, size_t length, coo* mat, size_t mat_length) {
  /@ assert 0 <= mat[mat_length-1].row < length; @/
  /@ loop invariant cc_bounds: 0 <= i <= length;
      loop invariant neq_coeff:
       \forall integer j;
       0 <= j < length && j != mat[mat_length-1].col ==>
       l_vec_mult(vec,mat,i,length,j,0,mat_length) ==
       l_vec_mult(vec,mat,i,length,j,0,mat_length-1);
      loop invariant eq_coeff:
       \let k = mat[mat_length-1].row;
       \let j = mat[mat_length-1].col;
       l_vec_mult(vec,mat,i,length,j,0,mat_length) ==
         (int)(l_vec_mult(vec,mat,i,length,j,0,mat_length-1) +
               (int)(i > k ? 0 : vec[k] * mat[mat_length-1].v));
      loop assigns i;
  @/
  for(size_t i = length; i > 0; i--) { }
}
*/

/*@ requires TODO;
    assigns out[0 .. length - 1];

    ensures TODO;

*/
void vec_mult(int * vec, size_t length, coo* mat, size_t mat_length, int* out,
              int ** rep) {
  /*@ loop invariant 0 <= i <= length;
      loop invariant \forall integer j; 0 <= j < i ==> out[j] == 0;
      loop assigns i,out[0 .. length - 1];
      loop variant length - i;
  */
  for(size_t i = 0; i < length; i++) out[i] = 0;
  /*@ ghost zero_coeffs(vec,length,mat); */
  /*@ loop invariant bound: 0 <= i <= mat_length;

      loop invariant partial_mul:
        \forall integer j; 0<= j < length ==>
         out[j] == l_vec_mult(vec,mat,0,length,j,0,i);

      loop assigns i, out[0 .. length-1];
   */
  for(size_t i = 0; i < mat_length; i++) {
    out[mat[i].col]+= vec[mat[i].row] * mat[i].v;
    /*@ ghost compute_coeff(vec,length,mat,i+1); */
  }
}
