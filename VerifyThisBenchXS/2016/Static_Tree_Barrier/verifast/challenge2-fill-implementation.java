/*@

typedef lemma void get_op(predicate(boolean) inv, predicate() pre, predicate(boolean) post)();
    requires inv(?value) &*& pre();
    ensures inv(value) &*& post(value);

typedef lemma void set_op(predicate(boolean) inv, boolean value, predicate() pre, predicate() post)();
    requires inv(?value0) &*& pre();
    ensures inv(value) &*& post();

@*/

class AtomicBoolean {
    //@ predicate valid(predicate(boolean) inv);
    AtomicBoolean()
        //@ requires exists<predicate(boolean)>(?inv) &*& inv(false);
        //@ ensures valid(inv);
    {
        throw new RuntimeException();
    }
    boolean get()
        //@ requires [_]valid(?inv) &*& is_get_op(?op, inv, ?pre, ?post) &*& pre();
        //@ ensures post(result);
    {
        throw new RuntimeException();
    }
    void set(boolean value)
        //@ requires [_]valid(?inv) &*& is_set_op(?op, inv, value, ?pre, ?post) &*& pre();
        //@ ensures post();
    {
        throw new RuntimeException();
    }
}

/*@

inductive tree = empty | tree(Node node, tree left, tree right);

predicate tree(Node node, Node parent; tree tree) =
    node == null ?
        tree == empty
    :
        tree1(node, parent, tree);

predicate tree1(Node node; Node parent, tree tree) =
    [_]node.sense |-> ?sense &*& [_]sense.valid(Node_inv(node)) &*&
    [_]node.left |-> ?left &*&
    [_]node.parent |-> parent &*&
    [_]node.leftTree |-> ?leftTree &*& [_]tree(left, node, leftTree) &*&
    [_]node.right |-> ?right &*&
    [_]node.rightTree |-> ?rightTree &*& [_]tree(right, node, rightTree) &*&
    tree == tree(node, leftTree, rightTree);

predicate senseValues(tree tree;) =
    switch (tree) {
        case empty: return true;
        case tree(node, left, right): return [1/2]node.senseValue |-> true &*& senseValues0(tree);
    };
    
predicate senseValues0(tree tree;) =
    switch (tree) {
        case empty: return true;
        case tree(node, left, right): return senseValues(left) &*& senseValues(right);
    };
    
predicate_ctor Node_inv(Node node)(boolean value) =
    [_]tree1(node, ?parent, ?tree) &*&
    [1/2]node.senseValue |-> value &*&
    value ?
        [1/2]node.grabbed |-> ?grabbed &*&
        [1/2]node.takenBack |-> false &*&
        grabbed ?
            parent != null
        :
            (parent == null ? true : senseValues(tree))
    :
        [1/2]node.grabbed |-> false &*&
        [1/2]node.takenBack |-> ?takenBack &*&
        takenBack ?
            true
        :
            [1/2]node.senseValue |-> false &*& senseValues0(tree);

predicate child(Node parent, Node child;) =
    parent != null &*&
    child == null ?
        true
    :
        [_]tree1(child, parent, _) &*&
        [1/2]child.grabbed |-> false;

predicate child_grabbed(Node parent, Node child;) =
    parent != null &*&
    child == null ?
        true
    :
        [1/2]child.grabbed |-> true &*&
        [_]tree1(child, parent, ?childTree) &*&
        senseValues(childTree);

predicate child_grabbed0(Node parent, Node child;) =
    parent != null &*&
    child == null ?
        true
    :
        [1/2]child.grabbed |-> true;

@*/

class Node {
	final Node left, right;
	//@ tree leftTree;
	//@ tree rightTree;
	//@ boolean senseValue;
	//@ boolean grabbed;
	//@ boolean takenBack;
	
	final Node parent;

	AtomicBoolean sense;
	int version;
	
	/*@
	
	predicate valid() =
	    [_]tree1(this, ?parent, ?thisTree) &*&
	    [1/2]this.senseValue |-> false &*&
	    [1/2]this.takenBack |-> true &*&
	    (parent == null ? [1/2]this.grabbed |-> false : true) &*&
	    [_]this.left |-> ?left &*& child(this, left) &*&
	    [_]this.right |-> ?right &*& child(this, right) &*&
	    version |-> _;
	
	@*/
	
	static void grab(Node child)
	    //@ requires child(?parent, child);
	    //@ ensures child_grabbed(parent, child);
	{
		TODO
	}
	
	void ungrab(Node child)
	    //@ requires child_grabbed(?parent, child);
	    //@ ensures child(parent, child);
	{
	    TODO
	}

	void barrier()
		//@ requires valid();
		//@ ensures  valid();
	{
		TODO
	}
}
