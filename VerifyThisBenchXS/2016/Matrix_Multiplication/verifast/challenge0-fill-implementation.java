/*@

predicate vector(int[] X, int m; list<int> values) = X[..] |-> values &*& X.length == m;

predicate vectors(int[][] XsArray, list<int[]> Xs, int m; list<list<int> > vss) =
    switch (Xs) {
        case nil: return vss == nil;
        case cons(X, Xs0): return vector(X, m, ?vs) &*& vectors(XsArray, Xs0, m, ?vss0) &*& vss == cons(vs, vss0);
    };

predicate matrix(int[][] X, int n, int m; list<list<int> > rows) =
    X[..] |-> ?rowArrays &*& n == X.length &*&
    vectors(X, rowArrays, m, rows);

fixpoint int matrix_elem(list<list<int> > rows, int i, int j) { return nth(j, nth(i, rows)); }

fixpoint nat len<t>(list<t> xs) {
    switch (xs) {
        case nil: return zero;
        case cons(x, xs0): return succ(len(xs0));
    }
}

lemma_auto void len_eq_nat_of_int_length<t>(list<t> xs)
    requires true;
    ensures len(xs) == nat_of_int(length(xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            len_eq_nat_of_int_length(xs0);
    }
}

fixpoint int matrix_multiply_elem(list<int> Arow, int j, list<list<int> > Brows) {
    switch (Arow) {
        case nil: return 0;
        case cons(vA, Arow0): return vA * nth(j, head(Brows)) + matrix_multiply_elem(Arow0, j, tail(Brows));
    }
}

fixpoint list<int> matrix_multiply_row(nat fuel, list<int> row, int j, list<list<int> > B) {
    switch (fuel) {
        case zero: return nil;
        case succ(fuel0): return cons(matrix_multiply_elem(row, j, B), matrix_multiply_row(fuel0, row, j + 1, B));
    }
}

fixpoint list<list<int> > matrix_multiply(list<list<int> > A, list<list<int> > B) {
    switch (A) {
        case nil: return nil;
        case cons(row, rows0): return cons(matrix_multiply_row(len(row), row, 0, B), matrix_multiply(rows0, B));
    }
}

@*/

class Math {

    static void matrixMultiply(int[][] A, int[][] B, int[][] C)
    //@ requires [_]matrix(A, ?N, N, ?Arows) &*& [_]matrix(B, N, N, ?Brows) &*& matrix(C, N, N, _);
    //@ ensures matrix(C, N, N, matrix_multiply(Arows, Brows));
    {
        TODO
    }
}
