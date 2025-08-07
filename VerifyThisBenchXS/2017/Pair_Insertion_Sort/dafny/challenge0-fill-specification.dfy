predicate sorted(s: seq<int>) {
   forall i :: forall j :: 0 <= i <= j < |s| ==> s[i] <= s[j] }

method sort(A: array<int>)
   requires TODO
   ensures TODO
{
   var i := 0;  // i is running index (inc by 2 every iteration)
   assert sorted(A[0..0]);
   while i < A.Length
     invariant 0 <= i <= A.Length
     invariant sorted(A[..i])
   {
     // let x and y hold the next to elements in A
     var x := A[i];

     var j := i - 1;	 // j is the index used to find the insertion point
     while j >= 0 && A[j] > x	// find the insertion point for x
       invariant sorted(A[j+2..i+1])
       invariant sorted(A[..j+1])
       invariant forall k :: forall m :: 0 <= k < j+1 && j+2 <= m <  
i+1 ==> A[k] <= A[m]
       invariant forall k :: j+2 <= k < i+1 ==> x <= A[k]
     {
        A[j+1] := A[j];  // shift existing content by 2
        j := j - 1;
     }
     A[j+1] := x;	 // store x at its insertion place

     i := i+1;
   }
}
