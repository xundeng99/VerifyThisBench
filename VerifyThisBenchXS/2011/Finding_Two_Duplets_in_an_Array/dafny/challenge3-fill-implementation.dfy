
/*
COST Verification Competition
Please send solutions to vladimir@cost-ic0701.org

Challenge 3: Two equal elements

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

// Does 's' has duplicates?
function method has_duplicates(s: seq<int>): bool
{
	TODO
}

// The number of occurrences of 'x' in 's'.
function method occurrences(s: seq<int>, x: int): nat
{
	TODO
}

// The first element of 's' that has a duplicate.
function method first_duplicate(s: seq<int>): int
	requires has_duplicates(s);
	ensures first_duplicate(s) in s;
{
	TODO
}

// Lemma.
ghost method multiple_occurrences(s: seq<int>)
	requires has_duplicates(s);
	ensures occurrences(s, first_duplicate(s)) > 1;
{
	TODO
}

// Lemma.
ghost method occurrences_when_present(s: seq<int>, x: int)
	requires x in s;
	ensures occurrences(s, x) > 0;
{
	TODO
}		

// Lemma.
ghost method occurrences_remove(s: seq<int>, x: int, y: int)
	ensures occurrences(s, y) >= occurrences(remove(s, x), y);
{
	TODO
}

// Sequence 's' with 'x' removed.
function method remove(s: seq<int>, x: int): seq<int>
	ensures x !in remove(s, x);
{
	TODO
}

// Returns different values 'x' and 'y' which both have duplicates in 's'.
method find_two_duplicates(a: seq<int>) returns (x: int, y: int)
	requires |a| >= 4;
	requires has_duplicates(a);
	requires has_duplicates(remove(a, first_duplicate(a)));
	ensures occurrences(a, x) > 1;
	ensures occurrences(a, y) > 1;
	ensures x != y;
{
	TODO
}

