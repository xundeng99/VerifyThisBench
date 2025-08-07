/*
challenge 1: maximum in an array

given: non-empty integer array
return: index of maximum

public static int max(int[] a) {
	int x = 0;
	int y = a.length-1;
	while (x != y) {
		if a[x] <= a[y]) {
			x++;
		}	else {
			y--;
		}
	}
	return x;
}
*/


method max(a: array<int>) returns (x: int)
	requires TODO;
	ensures TODO;
{
	var y := a.Length - 1;
	x := 0;
	while (x != y)
		invariant 0 <= x < a.Length;
		invariant 0 <= y < a.Length;
		invariant y >= x;
		invariant forall i :: 0 <= i <= x ==> a[i] <= a[x] || a[i] <= a[y];
		invariant forall i :: y <= i <= a.Length - 1 ==> a[i] <= a[x] || a[i] <= a[y];
		decreases y - x + 1;
	{
		if (a[x] <= a[y]) {
			x := x + 1;
		} else {
			y := y - 1;
		}
	}
}

