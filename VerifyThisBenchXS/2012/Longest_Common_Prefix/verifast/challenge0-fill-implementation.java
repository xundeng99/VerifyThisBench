//Jan Smans:
//* verified with VeriFast (local build) with overflow check disabled
//* LCP only (not the extra)


/*@
fixpoint boolean forall_nth_core<t>(list<t> xs, fixpoint(list<t>, int, boolean) p, nat n) {
  switch(n) {
    case zero: return p(xs, int_of_nat(zero));
    case succ(n0): return p(xs, int_of_nat(n)) && forall_nth_core(xs, p, n0);
  }
}

fixpoint boolean forall_nth<t>(list<t> xs, fixpoint(list<t>, int, boolean) p) {
  switch(xs) {
    case nil: return true;
    case cons(h, t): return forall_nth_core(xs, p, nat_of_int(length(xs) - 1));
  }
}

lemma int not_forall_nth_nat<t>(list<t> vs, fixpoint (list<t>, int, boolean) p, nat n)
  requires ! forall_nth_core(vs, p, n);
  ensures 0 <= result &*& result <= int_of_nat(n) &*& ! p(vs,result);
{
  TODO
}

lemma int not_forall_nth<t>(list<t> vs, fixpoint (list<t>, int, boolean) p)
  requires ! forall_nth(vs, p);
  ensures 0 <= result &*& result < length(vs) &*& ! p(vs, result);
{
   TODO
}

lemma void forall_nth_elim_nat<t>(list<t> vs, fixpoint (list<t>, int, boolean) p, nat n, int i)
  requires forall_nth_core(vs, p, n) == true &*& 0 <= i && i <= int_of_nat(n);
  ensures p(vs, i) == true;
{
  TODO
}

lemma void forall_nth_elim<t>(list<t> vs, fixpoint (list<t>, int, boolean) p, int i)
  requires forall_nth(vs, p) == true &*& 0 <= i &*& i < length(vs);
  ensures p(vs, i) == true;
{
  TODO
}

fixpoint boolean ok(int x, int y, int l, list<int> vs, int i) {
  return i < 0 || i >= l || nth(x + i, vs) == nth(y + i, vs);
}
@*/

class LCP {
 private int lcp(int[] a, int x, int y) 
   //@ requires array_slice<int>(a, 0, a.length, ?vs) &*& 0 <= x &*& x < a.length &*& 0 <= y &*& y < a.length;
   /*@ ensures array_slice<int>(a, 0, a.length, vs) &*&
               forall_nth(vs, (ok)(x, y, result)) == true &*& // forall i in (0:l) :: nth(x + i) == nth(y + i)
               (x + result < a.length - 1 && y + result < a.length -1 ? nth<int>(x +result, vs) != nth(y + result, vs) : true);
    @*/
 {
    TODO
 }
}
