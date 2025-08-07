/*

COST Verification Competition
Please send solutions to vladimir@cost-ic0701.org

Challenge 2: Maximum in a tree


Given: A non-empty binary tree, where every node carries an integer.

Implement and verify a program that computes the maximum of the values
in the tree.

Please base your program on the following data structure signature:

public class Tree {

    int value;
    Tree left;
    Tree right;

}

You may represent empty trees as null references or as you consider
appropriate.

*/

class Tree {
	var value: int;
	var left: Tree;
	var right: Tree;
	
	ghost var Repr: set<object>;	// Set of all tree objects reachable from 'this' (including 'this')
	ghost var Values: set<int>;	// Set of all values in this tree
	
	// Valid implies tree is acyclic, as the representations of subtrees 
	// is strict subset of the representation of 'this'
	function Valid(): bool
		reads this, Repr;
		decreases Repr;
	{
		TODO
	}
	
	method max() returns (result: int)
		requires Valid();
		ensures Valid();
		ensures result in Values;
		ensures forall v :: v in Values ==> result >= v;
		decreases Repr;
	{
		TODO
	}
	
}
