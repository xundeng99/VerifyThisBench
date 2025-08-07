#include <stddef.h>

/*@ predicate monotone_slice(int* a, size_t low, size_t up) =
  (\forall integer i,j; low <= i < j < up ==> a[i] < a[j]) ||
  (\forall integer i,j; low <= i <= j < up ==> a[i] >= a[j]);

*/

/*@
	requires length < 100;
    requires a_valid: \valid(a + (0 .. length - 1));
    requires res_valid: \valid(cutpoints + (0 .. length));
    requires sep: \separated(a + (0 .. length - 1), cutpoints + (0 .. length));
    assigns cutpoints[0 .. length];
    ensures pos: \result > 0;
    ensures beg: cutpoints[0] == 0;
    ensures end: cutpoints[\result - 1] == length;
    ensures bounds: \forall integer i; 0 <= i < \result ==>
      0<= cutpoints[i] <= length;
    ensures monotonic:
      \forall integer i; 0 <= i < \result - 1 ==>
      monotone_slice(a,cutpoints[i],cutpoints[i+1]);
*/
size_t monotonic(int* a, size_t length, size_t* cutpoints) {
  TODO
}
