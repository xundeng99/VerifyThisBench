type matrix = array2<int>

predicate validMatrix(m: matrix) 
{
	m != null && m.Length0 > 0 && m.Length0 == m.Length1
}

predicate validMultiplication(a: matrix, b: matrix, c: matrix)
	requires validMatrix(a) && validMatrix(b) && validMatrix(c)
	requires a.Length0 == b.Length0 == c.Length0
{
	forall i,j | 0 <= i < a.Length0 && 0 <= j < a.Length0 :: c[i,j] == MatrixSum(a,b,i,j) 
}

function method MatrixSum(a: matrix, b: matrix, i: nat, j: nat) : int
	requires validMatrix(a) && validMatrix(b)
	requires a.Length0 == b.Length0 
	requires i < a.Length0 && j < b.Length0
{
	sum(a,b,i,j,a.Length0)
}

function method sum(a: matrix, b: matrix, i: int, j: int, k: int) : int
	requires validMatrix(a) && validMatrix(b)
	requires a.Length0 == b.Length0 
	requires 0 <= i < a.Length0 && 0 <= j < b.Length0
	requires 0 <= k <= a.Length0
{
	if k == 0 then 0 else a[i,k-1] * b[k-1,j] + sum(a,b,i,j,k - 1)
}

method MatrixMultiplication(a: matrix, b: matrix) returns (c: matrix) 
	requires validMatrix(a) && validMatrix(b)
	requires a.Length0 == b.Length0
	ensures validMatrix(c)
	ensures a.Length0 == b.Length0 == c.Length0
	ensures validMultiplication(a,b,c)
{
	TODO
}
