
require open ETT.XAst;

// TODO check confluence

/* De Bruijn indices */
constant symbol db0 : DBId;
constant symbol dbsucc : DBId → DBId;
symbol db1 : DBId ≔ dbsucc db0;
symbol db2 : DBId ≔ dbsucc db1;

symbol dbadd : DBId → DBId → DBId;
symbol dbprev : DBId → DBId;
// Increments the second argument if it is (not strictly) greater than the
// first, otherwise is the identity
symbol dbshift : DBId → DBId → DBId;

rule dbshift (dbsucc $i) (dbsucc $j) ↪ dbsucc (dbshift $i $j)
with dbshift db0 $d ↪ dbsucc $d
with dbshift (dbsucc _) db0 ↪ db0
with dbadd db0 $id ↪ $id
with dbadd $id db0 ↪ $id
with dbadd (dbsucc $n) $m ↪ dbsucc (dbadd $n $m)
with dbadd $n (dbsucc $m) ↪ dbsucc (dbadd $n $m)
with dbprev (dbsucc $n) ↪ $n;


// Increases all free variable by one, assuming all the variable strictly lower
// than the first argument to be bound
symbol shift : DBId → Term → Term;
rule shift $i (var $id) ↪ var (dbshift $i $id)
with shift $i (tabs $A $B $t) ↪ tabs (shift $i $A) (shift (dbsucc $i) $B) (shift (dbsucc $i) $t)
with shift $i (tapp $A $B $f $u) ↪ tapp (shift $i $A) (shift (dbsucc $i) $B) (shift $i $f) (shift $i $u)
with shift $i (tfun $A $B) ↪ tfun (shift $i $A) (shift (dbsucc $i) $B)
with shift _  (tsort $s) ↪ tsort $s
with shift $i (tpair $A $B $u $v) ↪ tpair (shift $i $A) (shift (dbsucc $i) $B) (shift $i $u) (shift $i $v)
with shift $i (π1 $A $B $p) ↪ π1 (shift $i $A) (shift (dbsucc $i) $B) (shift $i $p)
with shift $i (π2 $A $B $p) ↪ π2 (shift $i $A) (shift (dbsucc $i) $B) (shift $i $p)
with shift $i (tsum $A $B) ↪ tsum (shift $i $A) (shift (dbsucc $i) $B)
with shift $i (trefl $A $u) ↪ trefl (shift $i $A) (shift $i $u)
with shift $i (teq $A $u $v) ↪ teq (shift $i $A) (shift $i $u) (shift $i $v);
symbol Shift : Term → Term ≔ shift db0;
symbol Shift1 : Term → Term ≔ shift db1;
symbol Shift* : DBId → Term → Term;
symbol ShiftN : DBId → Term → Term;
rule Shift* db0 $t ↪ $t
with Shift* (dbsucc $n) $t ↪ Shift (Shift* $n $t)
with Shift* _ (tsort $s) ↪ tsort $s
with ShiftN $i $t ↪ Shift (Shift* $i $t);

// Select a term depending on whether two indices are equal, the first one is greater, or lower
symbol dbselect : DBId → DBId → Term → Term → Term → Term;
rule dbselect db0 db0 $eq _ _ ↪ $eq
with dbselect (dbsucc $i) (dbsucc $j) $eq $gt $lt ↪ dbselect $i $j $eq $gt $lt
with dbselect db0 (dbsucc _) _ _ $lt ↪ $lt
with dbselect (dbsucc _) db0 _ $gt _ ↪ $gt;

// Substitution (and shift everything above the substituted index)
symbol subst : DBId → Term → Term → Term;
rule subst $i $V (var $id) ↪ dbselect $i $id $V (var $id) (var (dbprev $id))
with subst $i $V (tabs $A $B $t) ↪ tabs (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst (dbsucc $i) (Shift $V) $t)
with subst $i $V (tapp $A $B $f $u) ↪ tapp (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $f) (subst $i $V $u)
with subst $i $V (tfun $A $B) ↪ tfun (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
with subst _  _  (tsort $s) ↪ tsort $s
with subst $i $V (tpair $A $B $u $v) ↪ tpair (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $u) (subst $i $V $v)
with subst $i $V (π1 $A $B $p) ↪ π1 (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $p)
with subst $i $V (π2 $A $B $p) ↪ π2 (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $p)
with subst $i $V (tsum $A $B) ↪ tsum (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
with subst $i $V (trefl $A $u) ↪ trefl (subst $i $V $A) (subst $i $V $u)
with subst $i $V (teq $A $u $v) ↪ teq (subst $i $V $A) (subst $i $V $u) (subst $i $V $v);
symbol apply1 (t u : Term) : Term ≔ subst db0 u t;

// Term equality, necessary to express commutation of different operations
constant symbol TEq : Term → Term → TYPE;
constant symbol TRefl (t : Term) : TEq t t;

// TODO Some substitution commutation
rule shift db0 (shift $i $t) ↪ shift (dbsucc $i) (Shift $t);
rule shift (dbsucc db0) (shift (dbsucc $i) $t) ↪ shift (dbsucc (dbsucc $i)) (Shift1 $t);
rule subst db0 _ (shift db0 $t) ↪ $t
with subst $id (var $id) (shift (dbsucc $id) $t) ↪ $t
with shift $id (subst db0 $u $t) ↪ subst db0 (shift $id $u) (shift (dbsucc $id) $t);

symbol teq_subst_apply (i : DBId) (u t1 t2 : Term) :
  TEq (subst i (Shift* i u) (apply1 t2 t1))
      (apply1 (subst (dbsucc i) (Shift* (dbsucc i) u) t2) (subst i (Shift* i u) t1));
symbol teq_subst_shift (i : DBId) (u t : Term) :
  TEq (subst (dbsucc i) (Shift u) (Shift t))
      (Shift (subst i u t));
symbol teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift (dbsucc i) (shift i t)))
      (shift i t);
symbol teq_select_shift (i id : DBId) (V : Term) :
  TEq (dbselect (dbsucc i) (dbsucc id) (Shift V) (var (dbsucc id)) (var id))
      (Shift (dbselect i id V (var id) (var (dbprev id))));
