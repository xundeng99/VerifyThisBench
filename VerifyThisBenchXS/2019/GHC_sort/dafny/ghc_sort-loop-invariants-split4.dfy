/*
   Verified implementation of a sorting algorithm similar
   to Haskell's GHC generic sorting method but using iteration instead
   of recursion (and reusing the computation of monotonic cutpoins).

   This file uses definitions in cutpoints.dfy. Hence, to verify
   this file call Dafny on both files:
   > dafny cutpoints.dfy ghc_sort.dfy

   Developed and verified using Dafny v1.9.9, Boogie 63b3602e12, Z3 4.5.0

   The implementation works on arrays overall, but uses sequences
   to conveniently represent segments that are extracted and manipulated.
   The specification (and hence proofs) that the output is a permutation 
   of the input is incomplete; that is, it is not added everywhere. 
   The missing parts require to introduce an inductive function that maps 
   a seq<seq<int>> to a multiset<int> of all the content. Doing so triggers 
   what seems to be a bug of Dafny (NullReferenceException) when introducing 
   the recursive case expression in:

   function multisetof(segs: seq<seq<int>>): multiset<int>
   { if |segs| == 0 then multiset([]) else multiset(segs[0]) + multisetof(segs[1..]) }

   A way around it would be to explicitly construct and return the multiset
   of every seq<seq<int>>, but the result would be somewhat ugly. Anyway,
   I verified the multiset specification where possible without a function
   like multisetof, and it poses no particular challenges to verification.

   Author: Carlo A. Furia
*/

// reverse sequence s
ghost method reverse(s: seq<int>) returns(r: seq<int>)
	requires decreasing(s)
	ensures ordered(r)
	ensures multiset(r) == multiset(s)
{
	r := [];
	var k := 0;
	while k < |s|
		invariant 0 <= k <= |s|
		invariant |r| == k
		invariant 0 < k < |s| ==> s[k] <= r[0]
		invariant ordered(r)
		invariant multiset(r) == multiset(s[..k])
	{
		assert s[..k+1] == s[..k] + [s[k]];
		r := [s[k]] + r;
		k := k + 1;
	}
	assert s[..k] == s;
}

// break down `a' into monotonic segments
method monotonic_segments(a: array<int>) returns(segs: seq<seq<int>>)
	requires a != null
	ensures forall k :: 0 <= k < |segs| ==> ordered(segs[k]);
{
	segs := [];
	ghost var c := [0];
	var x, y := 0, 1;
	while y < a.Length
		invariant 0 <= x < y <= a.Length + 1
		invariant y == x + 1
		invariant monotonic_cuts(a[..x], c);
		invariant |c| > 0 && c[0] == 0;
		invariant forall k :: 0 <= k < |segs| ==> ordered(segs[k]);
	{
		var inc := (a[x] < a[y]);
		assert a[..y][..x] == a[..x];
		extend_cuts(a[..y], c, x);
		while y < a.Length && (a[y-1] < a[y] <==> inc)
			invariant 0 <= x < y <= a.Length
			invariant monotonic_cuts(a[..x], c)
			invariant monotonic(a[x..y])
			invariant monotonic_cuts(a[..y], c + [y])
		{
        y := y + 1;
        assert a[..y][..x] == a[..x];
        extend_cuts(a[..y], c, x);
		}
		c := c + [y];
    var incseg := a[x..y];
		if decreasing(incseg) {
			incseg := reverse(incseg);
		}
		assert ordered(incseg);
		segs := segs + [incseg];
		x := y;
		y := x + 1;
	}
	if x < a.Length {
		segs := segs + [a[x..y]];
	  extend_cuts(a[..], c, x);
		c := c + [a.Length];
		assert a[..a.Length] == a[..];
	} else {
		assert a[..a.Length] == a[..];
	}
	assert forall k :: 0 <= k < |segs| ==> ordered(segs[k]);
}

// merge `left' and `right' respecting order
method merge_pair(left: seq<int>, right: seq<int>) returns(merged: seq<int>)
	requires ordered(left)
	requires ordered(right)
	ensures ordered(merged)
	ensures multiset(merged) == multiset(left) + multiset(right)
{
	var x, y := 0, 0;
	merged := [];
	while x < |left| && y < |right|
		decreases |left| + |right| - (x + y)
		invariant 0 <= x <= |left|
		invariant 0 <= y <= |right|
		invariant |merged| == x + y
		invariant 0 < |merged| && x < |left| ==> merged[|merged|-1] <= left[x]
		invariant 0 < |merged| && y < |right| ==> merged[|merged|-1] <= right[y]
		invariant ordered(merged)
		invariant multiset(merged) == multiset(left[..x]) + multiset(right[..y])
	{
		if left[x] < right[y] {
			assert left[..x+1] == left[..x] + [left[x]];
			merged := merged + [left[x]];
			x := x + 1;
		} else {
			assert right[..y+1] == right[..y] + [right[y]];
			merged := merged + [right[y]];
			y := y + 1;
		}
	}
	if x < |left| {
		assert left[..x] + left[x..] == left;
		merged := merged + left[x..];
		x := |left|;
	}
	if y < |right| {
		assert right[..y] + right[y..] == right;
		merged := merged + right[y..];
		y := |right|;
	}
	assert right[..y] == right;
	assert left[..x] == left;
}

// merge all segments in `segs' pairwise
method merge_once(segs: seq<seq<int>>) returns(merged: seq<seq<int>>)
	requires forall k :: 0 <= k < |segs| ==> ordered(segs[k])
	requires |segs| > 1
	ensures forall k :: 0 <= k < |merged| ==> ordered(merged[k])
	ensures |merged| < |segs|
{
	merged := [];
	var x := 0;
	while x + 1 < |segs|
		invariant TODO;
	{
		var left := segs[x];
		var right := segs[x+1];
		var m := merge_pair(left, right);
		merged := merged + [m];
		x := x + 2;
	}
	if x < |segs| {
		merged := merged + [segs[|segs|-1]];
	}
}

// sort using GHC's generic method (a kind of patience sorting)
method ghc_sort(a: array<int>) returns(result: array<int>)
	requires a != null
	ensures result != null
	ensures ordered(result[..])
{
	var segs := monotonic_segments(a);
	while |segs| > 1
		invariant forall k :: 0 <= k < |segs| ==> ordered(segs[k]);
	{
		segs := merge_once(segs);
	}
	var merged: seq<int>;
	if |segs| > 0 {
		merged := segs[0];
	} else {
		merged := [];
	}
	result := new int[|merged|];
	var k := 0;
	while k < |merged|
		invariant 0 <= k <= |merged|
		invariant result[..k] == merged[..k]
	{
		result[k] := merged[k];
		k := k + 1;
	}
}
