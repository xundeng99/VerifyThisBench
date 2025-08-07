predicate sorted(s: seq<int>) {
   forall i :: forall j :: 0 <= i <= j < |s| ==> s[i] <= s[j] }

method sort(A: array<int>)
   requires A != null
   modifies A
   ensures sorted(A[..])
{
   TODO
}
