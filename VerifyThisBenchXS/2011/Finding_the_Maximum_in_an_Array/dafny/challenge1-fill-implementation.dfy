/*
challenge 1: maximum in an array

given: non-empty integer array
return: index of maximum
*/


method max(a: array<int>) returns (x: int)
	requires a != null;
	requires a.Length > 0;
	ensures 0 <= x < a.Length;
	ensures forall i :: 0 <= i < a.Length ==> a[x] >= a[i];
{
	TODO
}

