// Command: frama-c -wp program.c
// Frama-c version : Silicon (last release)
// The algorithm is proved to sort, but does not ensure the preservation of the elements of the initial array


/*@ requires n >= 0;
    requires \valid(a+(0..n-1));
    assigns a[0..n-1];
    ensures sorted: \forall integer i, j; 0 <= i <= j < n ==> a[i] <= a[j]; // the final array is sorted (proved!)
*/
void pair_sort(int a[], int n) {
  int i = 0; // i is running index (inc by 2 every iteration)

  /*@ loop invariant \forall integer k, l; 0 <= k <= l < i ==> a[k] <= a[l]; // the sub-array a[0..i-1] is sorted
      loop invariant 0 <= i <= n;
      //loop invariant same_elements{Pre, Here}(a, n);
      loop assigns i, a[0..n-1];
      loop variant n - 1 - i;
  */
  while (i < n-1) {
    int x = a[i];	// let x and y hold the next to elements in A
    int y = a[i+1];

    if (x < y) {	// ensure that x is not smaller than y
        int tmp = x;
        x = y;
        y = tmp;
    }
    //@ assert x == \max (a[i], a[i+1]);
    //@ assert y == \min (a[i], a[i+1]);

    int j = i - 1;	// j is the index used to find the insertion point
    /*@ loop invariant TODO;
        loop assigns a[0..n-1], j;
    */
    while (j >= 0 && a[j] > x)	{// find the insertion point for x
       a[j+2] = a[j];	// shift existing content by 2
       j = j - 1;
    }

    //@ assert \forall integer k, l; j+3 <= k <= l <= i+1 ==> a[k] <= a[l];
    a[j+2] = x;	// store x at its insertion place
	// A[j+1] is an available space now
    //@ assert \forall integer k, l; j+2 <= k <= l <= i+1 ==> a[k] <= a[l]; // the sub-array a[j+2..i+1] is sorted
    //@ assert \forall integer k, l; 0 <= k <= l <= j ==> a[k] <= a[l]; // the sub-array a[0..j] is sorted

    /*@ loop invariant \forall integer k, l; 0 <= k <= l <= j ==> a[k] <= a[l]; // the sub-array a[0..j] is sorted
        loop invariant \forall integer k, l; j+1 < k <= l <= i+1 ==> a[k] <= a[l]; // the sub-array a[j+2..i+1] is sorted
        loop invariant \forall integer k, l; 0 <= k <= j && j +1 < l <= i+1 ==> a[k] <= a[l]; // every element in a[0..j] is no more then every element in a[j+2..i+1]
        loop invariant \forall integer k; j+1 < k <= i+1 ==> y <= a[k]; // every element in a[j+2..i+1] is more than x
        loop invariant -1 <= j <= \at(j, LoopEntry); // j varies between -1 and its value at the loop entry
        loop assigns a[0..n-1], j;
    */
    while (j >= 0 && a[j] > y) {	// find the insertion point for y
        a[j+1] = a[j];	// shift existing content by 1
        j = j - 1;
    }
    //@ assert j > 0 ==> a[j] <= y; // if j is not zero, a[j] <= y
    a[j+1] = y;	// store y at its insertion place

    //@ assert \forall integer k, l; j+1 <= k <= l <= i+1 ==> a[k] <= a[l];
    //@ assert \forall integer k, l; 0 <= k <= l <= j+1 ==> a[k] <= a[l];
    //@ assert \forall integer k, l; 0 <= k <= l <= i+1 ==> a[k] <= a[l]; // a[0..i+1] is sorted

    i = i+2;
  }

  //@ assert i == n-1 || i == n; // i is n or n-1

  //@ assert \forall integer i, j; 0 <= i <= j < n - 1 ==> a[i] <= a[j]; // a[0..n-2] is sorted
  if (i == n-1) {	// if length(A) is odd, an extra
    int y = a[i];	// single insertion is needed for 
    int j = i - 1;	// the last element
    /*@ loop invariant \forall integer k, l; 0 <= k <= l <= j ==> a[k] <= a[l]; // every element in a[0..j] is more than x
        loop invariant \forall integer k, l; j+1 < k <= l < n ==> a[k] <= a[l]; // every element in a[j+2..n-1] is more than x
        loop invariant \forall integer k, l; 0 <= k <= j && j +1 < l < n ==> a[k] <= a[l]; // every element in a[0..j] is no more then every element in a[j+2..n-1]
        loop invariant \forall integer k; j+1 < k < n ==> y <= a[k]; // every element in a[j+2..n-1] is no less then y
        loop invariant -1 <= j <= i-1;
        loop assigns a[0..n-1], j;
    */
    while (j >= 0 && a[j] > y) {
        a[j+1] = a[j];
        j = j - 1;
    }
    a[j+1] = y;
  }
}

