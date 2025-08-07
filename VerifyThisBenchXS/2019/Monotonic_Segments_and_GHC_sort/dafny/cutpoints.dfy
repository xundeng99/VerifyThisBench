/*
   Verified implementation of an algorithm that computes the
   maximal monotonic cutpoints of an array of integers.

   To verify call Dafny:
   > dafny cutpoints.dfy

   Developed and verified using Dafny v1.9.9, Boogie 63b3602e12, Z3 4.5.0

   Author: Carlo A. Furia
*/

predicate ordered(s: seq<int>)
{
	forall j, k :: 0 <= j < k < |s| ==> s[j] <= s[k]
}

predicate increasing(s: seq<int>)
{
	forall j, k :: 0 <= j < k < |s| ==> s[j] < s[k]
}

predicate decreasing(s: seq<int>)
{
	forall j, k :: 0 <= j < k < |s| ==> s[j] >= s[k]
}

predicate monotonic(s: seq<int>)
{
	increasing(s) || decreasing(s)
}

// `c' is the sequence of monotonic cutpoints of `s'
predicate monotonic_cuts(s: seq<int>, c: seq<int>)
{
	increasing(c)
		&& |c| > 0
		&& (forall k :: 0 <= k < |c| ==> 0 <= c[k] <= |s|)
		&& (c[0] == 0 && c[|c|-1] == |s|)
		&& (forall k :: 0 < k < |c| ==> monotonic(s[c[k-1]..c[k]]))
}

// `c' is the sequence of *maximal* monotonic cutpoints of `s'
predicate maximal_cuts(s: seq<int>, c: seq<int>)
{
	monotonic_cuts(s, c)
		&& (forall k :: 0 < k < |c| - 1 ==> !monotonic(s[c[k-1]..c[k]+1]))
}

lemma extend_cuts(s: seq<int>, c: seq<int>, d: int)
	requires 0 <= d < |s|
	requires monotonic_cuts(s[..d], c)
	requires monotonic(s[d..])
	ensures monotonic_cuts(s[..], c + [|s|])
{
	var c2 := c + [|s|];
	assert monotonic(s[c2[|c2|-2]..c2[|c2|-1]]);
	assert forall k :: 0 < k < |c| ==> s[c[k-1]..c[k]] == s[..d][c[k-1]..c[k]];
}

lemma extend_max(s: seq<int>, x: int, y: int)
	requires 0 <= x < y < |s|
	requires monotonic(s[x..y])
	requires increasing(s[x..y]) ==> s[y-1] >= s[y]
	requires decreasing(s[x..y]) ==> s[y-1] < s[y]
	ensures !monotonic(s[x..y+1])
{
	assert s[x..y+1] == s[x..y] + [s[y]];
}


// compute the sequence of monotonic cutpoints of `a'
method monotonic_cutpoints(a: array<int>) returns(c: seq<int>)
	requires a != null
	ensures monotonic_cuts(a[..], c)
	ensures maximal_cuts(a[..], c)
{
	c := [0];
	var x, y := 0, 1;
	ghost var p := 0;  // left endpoint of "previous" segment
	while y < a.Length
		invariant 0 <= x < y <= a.Length + 1
		invariant y == x + 1
		invariant 0 <= p <= x
		invariant monotonic_cuts(a[..x], c)
		invariant forall k :: 0 < k < |c| - 1 ==> !monotonic(a[c[k-1]..c[k]+1])
		invariant 0 < x < a.Length ==> !monotonic(a[p..x+1])
		invariant |c| > 0 && c[0] == 0
		invariant |c| > 1 ==> c[|c|-2] == p
	{
		var inc := (a[x] < a[y]);
		assert a[..y][..x] == a[..x];
		extend_cuts(a[..y], c, x);
		while y < a.Length && (a[y-1] < a[y] <==> inc)
			invariant 0 <= x < y <= a.Length
			invariant monotonic_cuts(a[..x], c)
			invariant monotonic(a[x..y])
			invariant monotonic_cuts(a[..y], c + [y])
			invariant inc ==> increasing(a[x..y])
			invariant !inc ==> decreasing(a[x..y])
		{
        y := y + 1;
        assert a[..y][..x] == a[..x];
        extend_cuts(a[..y], c, x);
		}
		assert monotonic(a[x..y]);
    if (y < a.Length) {
	    extend_max(a[..], x, y);
	  }
    assert y < a.Length ==> !monotonic(a[x..y+1]);
		c := c + [y];
		p := x;
		x := y;
		y := x + 1;
	}
	if x < a.Length {
	  extend_cuts(a[..], c, x);
		c := c + [a.Length];
		assert a[..a.Length] == a[..];
	} else {
		assert a[..a.Length] == a[..];
	}
}
