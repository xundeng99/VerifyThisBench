#include <stddef.h>

/*@ requires \valid(s + (0 .. length - 1));
    requires \valid(stack + (0 .. length - 1));
    requires \valid(left + (0 .. length - 1));
    requires \separated(stack + (0 .. length - 1),left + (0 .. length - 1));
    requires \separated(stack + (0 .. length - 1), s + (0 .. length - 1));
    requires \separated(left + (0 .. length - 1), s + (0 .. length - 1));

    assigns stack[0 .. length - 1], left[0 .. length - 1];

    ensures wf_left: \forall integer i; 0 <= i < length ==> 0 <= left[i] <= i;
    ensures left_small:
    \forall integer i; 0 <= i < length ==> 0 < left[i] ==>
     left[i] > 0 ==> s[left[i]-1] < s[i];
     ensures left_smallest:
     \forall integer i; 0 <= i < length ==>
        \forall integer j; left[i] <= j < i ==> s[j] >= s[i];
*/
void neighbor(int* s, size_t length, size_t* stack, size_t* left) {
  size_t sidx = 0;
  /*@ loop invariant TODO;
      loop assigns x, sidx, stack[0 .. length - 1], left[0 .. length - 1];
      loop variant length - x;
   */
  for (size_t x = 0; x < length; x++) {
    /*@
       loop invariant TODO;
        loop assigns sidx;
        loop variant sidx;
     */
    while (sidx > 0 && s[stack[sidx-1]-1] >= s[x]) sidx--;
    if (sidx == 0) {
      left[x] = 0;
    } else {
      /*@ assert head_ok:
            \forall integer i; stack[sidx-1]<=i<x ==> s[i] >= s[x];
      */
      left[x] = stack[sidx - 1];
    }
	//@ assert a1: left[x] > 0 ==> s[left[x] - 1] < s[x];
label:
    stack[sidx] = x + 1;
    /*@ assert s_untouched:
        \forall integer idx; 0 <= idx < length ==> s[idx] == \at(s[idx],Pre);
    */
    //@ assert same: left[x] == \at(left[x], label);
    //@ assert a2: left[x] > 0 ==> s[left[x] - 1] < s[x];
    sidx++;
  }
}
