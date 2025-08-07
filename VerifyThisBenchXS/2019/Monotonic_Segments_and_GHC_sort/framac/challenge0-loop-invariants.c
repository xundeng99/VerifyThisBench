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
  cutpoints[0] = 0;
  if (length == 0) return 1;
  size_t x = 0, y = 1;
  size_t res = 1;
  /*@
    loop invariant TODO;
   */
  while (y < length) {
    int increasing = a[x] < a[y];
    /*@
      loop invariant TODO;
    */
    while (y < length && (a[y-1] < a[y]) == increasing) y++;
    /*@ assert mono: monotone_slice(a,x,y); */
    cutpoints[res] = y;
    res++;
    /*@ assert mono_res: monotone_slice(a,cutpoints[res-2],cutpoints[res-1]);*/
    x = y;
    if (y < length) y++;
  }
  if (x < length) {
    /*@ assert last: x == length - 1; */
    /*@ assert mono_2: monotone_slice(a,x,length); */
    cutpoints[res] = length;
    res++;
    /*@ assert mono_3: monotone_slice(a,cutpoints[res - 2], cutpoints[res - 1]); */
  }
  return res;
}
