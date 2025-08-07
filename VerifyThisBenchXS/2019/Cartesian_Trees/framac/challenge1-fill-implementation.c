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
  TODO;
}
