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
	TODO;
}

// break down `a' into monotonic segments
method monotonic_segments(a: array<int>) returns(segs: seq<seq<int>>)
	requires a != null
	ensures forall k :: 0 <= k < |segs| ==> ordered(segs[k]);
{
	TODO;
}

// merge `left' and `right' respecting order
method merge_pair(left: seq<int>, right: seq<int>) returns(merged: seq<int>)
	requires ordered(left)
	requires ordered(right)
	ensures ordered(merged)
	ensures multiset(merged) == multiset(left) + multiset(right)
{
	TODO;
}

// merge all segments in `segs' pairwise
method merge_once(segs: seq<seq<int>>) returns(merged: seq<seq<int>>)
	requires forall k :: 0 <= k < |segs| ==> ordered(segs[k])
	requires |segs| > 1
	ensures forall k :: 0 <= k < |merged| ==> ordered(merged[k])
	ensures |merged| < |segs|
{
	TODO;
}

// sort using GHC's generic method (a kind of patience sorting)
method ghc_sort(a: array<int>) returns(result: array<int>)
	requires a != null
	ensures result != null
	ensures ordered(result[..])
{
	TODO;
}
