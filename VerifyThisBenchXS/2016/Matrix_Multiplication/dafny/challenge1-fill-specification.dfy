type matrix = array2<int>

predicate validMatrix(m: matrix) 
{
	m != null && m.Length0 > 0 && m.Length0 == m.Length1
}

predicate validMultiplication(a: matrix, b: matrix, c: matrix)
	requires TODO
	ensures TODO
{
	forall i,j | 0 <= i < a.Length0 && 0 <= j < a.Length0 :: c[i,j] == MatrixSum(a,b,i,j) 
}

function method MatrixSum(a: matrix, b: matrix, i: nat, j: nat) : int
	requires TODO
	ensures TODO
{
	sum(a,b,i,j,a.Length0)
}

function method sum(a: matrix, b: matrix, i: int, j: int, k: int) : int
	requires TODO
	ensures TODO
{
	if k == 0 then 0 else a[i,k-1] * b[k-1,j] + sum(a,b,i,j,k - 1)
}

method MatrixMultiplication(a: matrix, b: matrix) returns (c: matrix) 
	requires TODO
	ensures TODO
{
	var n := a.Length0;

	c := new int[n,n];

	forall i,j | 0 <= i < n && 0 <= j < n 
	{	
		c[i,j] := 0; 
	}
	assert forall i,j | 0 <= i < n && 0 <= j < n :: c[i,j] == 0;

	var i, k, j := 0, 0, 0;
	while (i < n) 
		invariant 0 <= i <= n

		invariant forall i',j' | 0 <= i' < i && 0 <= j' < n :: c[i',j'] == MatrixSum(a,b,i',j') 
		invariant forall i',j' | i <= i' < n && 0 <= j' < n :: c[i',j'] == 0;
	{
		k := 0;
		while (k < n)
			invariant 0 <= k <= n
			
			invariant forall i',j' | 0 <= i' < i && 0 <= j' < n :: c[i',j'] == MatrixSum(a,b,i',j')
			invariant forall i',j' | i < i' < n && 0 <= j' < n :: c[i',j'] == 0; 

			invariant forall j' | 0 <= j' < n :: c[i,j'] == sum(a,b,i,j',k) 
		{
			j := 0;
			while (j < n)
				invariant 0 <= j <= n
				
				invariant forall i',j' | 0 <= i' < i && 0 <= j' < n :: c[i',j'] == MatrixSum(a,b,i',j') 
				invariant forall i',j' | i < i' < n && 0 <= j' < n :: c[i',j'] == 0;

				invariant forall j' | j <= j' < n :: c[i,j'] == sum(a,b,i,j', k) 
				invariant forall j' | 0 <= j' < j :: c[i,j'] == sum(a,b,i,j', k+1) 
			{
				c[i,j] := c[i,j] + a[i,k] * b[k,j];
				j := j + 1;
			}
			k := k + 1;
		}
		i := i + 1;
	}
}
