//should be a complete solution

import java.util.Arrays;

/*@

inductive bintree = leaf(int) | node(bintree, bintree);

predicate array_tree0(int[] a, int left, int right, bintree values) =
    right > left + 1 ?
        array_tree0(a, left - (right - left) / 2, left, ?lvalues) &*&
        array_tree0(a, right - (right - left) / 2, right, ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, ?l) &*& array_element(a, right, ?r) &*& values == node(leaf(l), leaf(r)) &*&
        right == left + 1;

fixpoint int treesum(bintree t) {
    switch (t) {
        case leaf(n): return n;
        case node(n1, n2): return treesum(n1) + treesum(n2);
    }
}

fixpoint bintree getleft(bintree t) {
    switch (t) {
        case leaf(n): return t;
        case node(t1, t2): return t1;
    }
}

fixpoint bintree getright(bintree t) {
    switch (t) {
        case leaf(n): return t;
        case node(t1, t2): return t2;
    }
}

fixpoint boolean isleaf(bintree t) {
    switch (t) {
        case leaf(n): return true;
        case node(t1, t2): return false;
    }
}

predicate array_tree1(int[] a, int left, int right, bintree values) =
    right > left + 1 ?
        array_tree1(a, left - (right - left) / 2, left, ?lvalues) &*& array_element(a, left, treesum(lvalues)) &*&
        array_tree1(a, right - (right - left) / 2, right, ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, ?l) &*& getleft(values) == leaf(l) &*& isleaf(getright(values)) == true &*& !isleaf(values) &*&
        right == left + 1;

predicate array_tree2(int[] a, int left, int right, int leftSum, bintree values) =
    right > left + 1 ?
        array_tree2(a, left - (right - left) / 2, left, leftSum, ?lvalues) &*&
        array_tree2(a, right - (right - left) / 2, right, leftSum + treesum(lvalues), ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, leftSum) &*& array_element(a, right, ?r) &*& getleft(values) == leaf(r - leftSum) &*& !isleaf(values) &*& isleaf(getright(values)) == true &*&
        right == left + 1;

fixpoint list<int> prefixSums(int leftSum, bintree b) {
    switch (b) {
        case leaf(n): return cons(leftSum, nil);
        case node(t1, t2): return append(prefixSums(leftSum, t1), prefixSums(leftSum + treesum(t1), t2));
    }
}

lemma void array_tree2_prefixsums()
    requires array_tree2(?a, ?left, ?right, ?leftSum, ?values);
    ensures array_slice(a, left + 1 - (right - left), right + 1, prefixSums(leftSum, values));
{
    TODO
}

@*/

class PrefixSumRec {

    private int[] a;

    PrefixSumRec(int [] a)
        //@ requires true;
        //@ ensures this.a |-> a;
    {
	TODO
    }


    public void upsweep(int left, int right)
        //@ requires a |-> ?a_ &*& array_tree0(a_, left, right, ?values);
        //@ ensures a |-> a_ &*& array_tree1(a_, left, right, values) &*& array_element(a_, right, treesum(values));
    {
       TODO
    }
    

    public void downsweep(int left, int right)
        //@ requires a |-> ?a_ &*& array_tree1(a_, left, right, ?values) &*& array_element(a_, right, ?leftSum);
        //@ ensures a |-> a_ &*& array_tree2(a_, left, right, leftSum, values);
    {
        TODO
    }

       
    public static void main (String [] args)
        //@ requires true;
        //@ ensures true;
    {
        TODO
    }

}


/*
[3, 1, 7, 0, 4, 1, 6, 3]
[3, 4, 7, 11, 4, 5, 6, 25]
[0, 3, 4, 11, 11, 15, 16, 22]



*/
