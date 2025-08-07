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
	requires a != null;
	requires a.Length > 0;
	ensures 0 <= x < a.Length;
	ensures forall i :: 0 <= i < a.Length ==> a[x] >= a[i];
{
	var y := a.Length - 1;
	x := 0;
	while (x != y)
		invariant TODO;
		decreases y - x + 1;
	{
		if (a[x] <= a[y]) {
			x := x + 1;
		} else {
			y := y - 1;
		}
	}
}

