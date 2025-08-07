//Fixed issue in definition of orderedness.

struct tree {
    Tree left;
    int data;
    Tree right;
};

typedef struct tree *Tree;

/*@

inductive tree_ = empty | node(tree_, Tree, int, tree_);

fixpoint tree_ delete_min(tree_ t) {
    switch (t) {
        case empty: return empty;
        case node(t1, p, v, t2): return t1 == empty ? t2 : node(delete_min(t1), p, v, t2);
    }
}

predicate Tree(Tree t; tree_ vs) =
    t == 0 ?
        vs == empty
    :
        t->left |-> ?l &*& Tree(l, ?vsl) &*&
        t->right |-> ?r &*& Tree(r, ?vsr) &*&
        t->data |-> ?v &*& malloc_block_tree(t) &*&
        vs == node(vsl, t, v, vsr);
        
lemma_auto void Tree_inv()
    requires Tree(?t, ?vs);
    ensures Tree(t, vs) &*& t == getptr(vs);
{
    open Tree(_, _);
}

fixpoint tree_ getleft(tree_ t) {
    switch (t) {
        case empty: return empty;
        case node(l, p, v, r): return l;
    }
}

fixpoint tree_ getright(tree_ t) {
    switch (t) {
        case empty: return empty;
        case node(l, p, v, r): return r;
    }
}

fixpoint int getvalue(tree_ t) {
    switch (t) {
        case empty: return 0;
        case node(l, p, v, r): return v;
    }
}


fixpoint Tree getptr(tree_ t) {
    switch (t) {
        case empty: return 0;
        case node(l, p, v, r): return p;
    }
}

typedef lemma void fill_hole_lemma(predicate() pred, Tree t, tree_ vs, Tree pp, Tree r)();
    requires pred() &*& pp->left |-> r;
    ensures Tree(t, delete_min(vs));

fixpoint int min_value(tree_ vs) {
    switch (vs) {
        case empty: return 0;
        case node(t1, p, v, t2): return t1 == empty ? v : min_value(t1);
    }
}

fixpoint bool ordered_between(int min, tree_ t, int max) {
    switch (t) {
        case empty: return true;
        case node(t1, p, v, t2): return min <= v && v <= max && ordered_between(min, t1, v) && ordered_between(v, t2, max);
    }
}

lemma void ordered_between_weaken(int min0, int min1, tree_ t, int max0, int max1)
    requires ordered_between(min1, t, max0) == true &*& min0 <= min1 &*& max0 <= max1;
    ensures ordered_between(min0, t, max1) == true;
{
    switch (t) {
        case empty:
        case node(t1, p, v, t2):
            ordered_between_weaken(min0, min1, t1, v, v);
            ordered_between_weaken(v, v, t2, max0, max1);
    }
}

lemma_auto void delete_min_ordered_between(int min, tree_ t, int max)
    requires ordered_between(min, t, max) == true;
    ensures ordered_between(min, delete_min(t), max) == true;
{
    switch (t) {
        case empty:
        case node(t1, p, v, t2):
            if (t1 != empty) {
                delete_min_ordered_between(min, t1, v);
            } else {
                ordered_between_weaken(min, v, t2, max, max);
            }
    }
}

@*/

void search_tree_delete_min(Tree t, Tree *r1, int *r2)
   //@ requires Tree(t, ?vs) &*& vs != empty &*& pointer(r1, _) &*& integer(r2, _) &*& ordered_between(INT_MIN, vs, INT_MAX) == true;
   //@ ensures pointer(r1, ?tresult) &*& Tree(tresult, delete_min(vs)) &*& integer(r2, min_value(vs)) &*& ordered_between(INT_MIN, delete_min(vs), INT_MAX) == true;
{
   TODO
}
