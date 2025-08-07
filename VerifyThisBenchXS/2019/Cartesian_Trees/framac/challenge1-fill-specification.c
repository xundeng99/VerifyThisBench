#include <stddef.h>

/*@ 
    requires TODO;
    assigns stack[0 .. length - 1], left[0 .. length - 1];

    ensures TODO;
*/
void neighbor(int* s, size_t length, size_t* stack, size_t* left) {
  size_t sidx = 0;
  /*@ loop invariant s_untouched:
        \forall integer idx; 0 <= idx < length ==> s[idx] == \at(s[idx],Pre);
      loop invariant 0 <= x <= length;
      loop invariant 0 <= sidx <= x;
      loop invariant stack_left:
        \forall integer i; 0 <= i < sidx ==> 0 < stack[i] <= x;
      loop invariant wf_left:
        \forall integer i; 0 <= i < x ==> 0 <= left[i] <= i;
      loop invariant left_small:
        \forall integer i; 0 <= i < x ==> left[i] > 0 ==> s[left[i] - 1] < s[i];
      loop invariant left_smallest:
        \forall integer i; 0 <= i < x ==>
          \forall integer j; left[i] <= j < i ==> s[j] >= s[i];
      loop invariant stack_order:
        \forall integer i, j; 0<= i < j < sidx ==> 0 <= stack[i] < stack[j];
      loop invariant stack_sorder:
        \forall integer i, j;
          0<= i < j < sidx ==> s[stack[i]-1] < s[stack[j]-1];
      loop invariant s_begin:
      sidx > 0 ==>
        \forall integer i; 0<=i<stack[0] ==> s[i] >= s[stack[0] - 1];
      loop invariant step_n:
        x > 0 ==> sidx > 0 && stack[sidx - 1] == x;
      loop invariant stack_summary:
        \forall integer i; 0<= i < sidx - 1 ==>
          \forall integer j; stack[i] <= j < stack[i+1]-1 ==>
                 s[j] >= s[stack[i+1]-1];
      loop invariant stack_push: sidx > 0 ==> stack[sidx-1] == x;
      loop assigns x, sidx, stack[0 .. length - 1], left[0 .. length - 1];
      loop variant length - x;
   */
  for (size_t x = 0; x < length; x++) {
    /*@
       loop invariant s_untouched_inner:
        \forall integer idx; 0 <= idx < length ==> s[idx] == \at(s[idx],Pre);
        loop invariant 0 <= sidx <= \at(sidx,LoopEntry);
        loop invariant left_bigger:
          sidx > 0 ==>
          \forall integer i;
             stack[sidx-1] <= i < x ==> s[i] >= s[x];
        loop invariant stack_empty:
          sidx == 0 ==>
          \forall integer i; 0 <= i < x ==> s[i] >= s[x];
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
