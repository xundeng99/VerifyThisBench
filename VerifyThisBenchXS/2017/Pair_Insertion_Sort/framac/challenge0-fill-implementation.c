// Command: frama-c -wp program.c
// Frama-c version : Silicon (last release)
// The algorithm is proved to sort, but does not ensure the preservation of the elements of the initial array


/*@ requires n >= 0;
    requires \valid(a+(0..n-1));
    assigns a[0..n-1];
    ensures sorted: \forall integer i, j; 0 <= i <= j < n ==> a[i] <= a[j]; // the final array is sorted (proved!)
*/
void pair_sort(int a[], int n) {
  TODO
}

