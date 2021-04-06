
require ETT.itt as ITT;

constant symbol Prop : TYPE;
constant symbol mkProp : Π(s : ITT.Sort), ITT.U s → Prop;
symbol getSort : Prop → ITT.Sort;
symbol getProp : Π(P : Prop), ITT.U (getSort P);
rule getSort (mkProp $s _) ↪ $s;
rule getProp (mkProp _ $p) ↪ $p;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE ≔
  λ p, ITT.ε (getSort p) (getProp p);
builtin "P" ≔ π;

/* Sorts */
symbol Sort : TYPE;
constant symbol s0 : Sort;
constant symbol snext : Sort → Sort;
symbol smax : Sort → Sort → Sort;
rule smax s0 $n ↪ $n
with smax $n s0 ↪ $n
with smax (snext $n) (snext $m) ↪ snext (smax $n $m);

/* De Bruijn indices */
constant symbol DBId : TYPE;
constant symbol db0 : DBId;
constant symbol dbsucc : DBId → DBId;
// Increments the second argument if it is (not strictly) greater than the
// first, otherwise is the identity
symbol dbshift : DBId → DBId → DBId;
rule dbshift (dbsucc $i) (dbsucc $j) ↪ dbsucc (dbshift $i $j)
with dbshift db0 $d ↪ dbsucc $d
with dbshift (dbsucc _) db0 ↪ db0;

/* Terms */
inductive Term : TYPE ≔
// Dependent λ-calculus
| var : DBId → Term
| tabs
  : Term // Type of the argument
  → Term // Type of result
  → Term // Body of the abstraction
  → Term
| tapp
  : Term // Type of the argument of the function
  → Term // Type of the result
  → Term // Function
  → Term // Argument
  → Term
| tfun
  : Term // Type of the argument
  → Term // Type of the result
  → Term
| tsort : Sort → Term
// Dependent pairs
| tpair
  : Term // Type of the first element
  → Term // Type of the second element
  → Term // First element
  → Term // Second element
  → Term
| π1
  : Term // First type of the pair
  → Term // Second type of the pair
  → Term // The pair
  → Term
| π2
  : Term // First type of the pair
  → Term // Second type of the pair
  → Term // The pair
  → Term
| tsum
  : Term // Type of the first element
  → Term // Type of the second element
  → Term
// Propositional equality
| trefl
  : Term // Type
  → Term // Term
  → Term
| J
  : Term // Type of the term to rewrite A
  → Term // Term to rewrite u
  → Term // Proposition depending on the term and the equality aka P
  → Term // Proof of P(u, refl A u)
  → Term // Term to rewrite u by
  → Term // Proof of equality between the terms to rewrite
  → Term
| teq
  : Term // Type of the equality
  → Term → Term → Term
// Axioms
| funext
  : Term // Type of the argument
  → Term // Type of the result
  → Term // First function
  → Term // Second function
  → Term // Proof of equality point by point
  → Term
| uip
  : Term // Type
  → Term → Term // The two terms
  → Term → Term // The two equalities
  → Term;

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
with shift $i (J $A $u $P $w $v $p) ↪ J (shift $i $A) (shift $i $u) (shift (dbsucc (dbsucc $i)) $P)
                                         (shift $i $w) (shift $i $v) (shift $i $p)
with shift $i (teq $A $u $v) ↪ teq (shift $i $A) (shift $i $u) (shift $i $v)
with shift $i (funext $A $B $f $g $ext) ↪ funext (shift $i $A) (shift (dbsucc $i) $B)
                                                  (shift $i $f) (shift $i $g) (shift $i $ext)
with shift $i (uip $A $u $v $p $q) ↪ uip (shift $i $A) (shift $i $u) (shift $i $v) (shift $i $p) (shift $i $q);
symbol Shift : Term → Term ≔ shift db0;

// Select a term depending on whether two indices are equal
symbol dbselect : DBId → DBId → Term → Term → Term;
rule dbselect db0 db0 $if _ ↪ $if
with dbselect (dbsucc $i) (dbsucc $j) $if $else ↪ dbselect $i $j $if $else
with dbselect db0 (dbsucc _) _ $else ↪ $else
with dbselect (dbsucc _) db0 _ $else ↪ $else;

// Substitution
symbol subst : DBId → Term → Term → Term;
rule subst $i $V (var $id) ↪ dbselect $i $id $V (var $id)
with subst $i $V (tabs $A $B $t) ↪ tabs (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst (dbsucc $i) (Shift $V) $t)
with subst $i $V (tapp $A $B $f $u) ↪ tapp (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $f) (subst $i $V $u)
with subst $i $V (tfun $A $B) ↪ tfun (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
with subst _  _  (tsort $s) ↪ tsort $s
with subst $i $V (tpair $A $B $u $v) ↪ tpair (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $u) (subst $i $V $v)
with subst $i $V (π1 $A $B $p) ↪ π1 (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $p)
with subst $i $V (π2 $A $B $p) ↪ π2 (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B) (subst $i $V $p)
with subst $i $V (tsum $A $B) ↪ tsum (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
with subst $i $V (trefl $A $u) ↪ trefl (subst $i $V $A) (subst $i $V $u)
with subst $i $V (J $A $u $P $w $v $p) ↪ J (subst $i $V $A) (subst $i $V $u)
                                            (subst (dbsucc (dbsucc $i)) (Shift (Shift $V)) $P)
                                            (subst $i $V $w) (subst $i $V $v) (subst $i $V $p)
with subst $i $V (teq $A $u $v) ↪ teq (subst $i $V $A) (subst $i $V $u) (subst $i $V $v)
with subst $i $V (funext $A $B $f $g $ext) ↪ funext (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
                                                     (subst $i $V $f) (subst $i $V $g) (subst $i $V $ext)
with subst $i $V (uip $A $u $v $p $q) ↪ uip (subst $i $V $A) (subst $i $V $u) (subst $i $V $v) (subst $i $V $p) (subst $i $V $q);

/* Typing derivation */
// constant symbol Var : TYPE;
// constant symbol VAR : Var → Term → Sort → Term; // Represents a bound variable of type its argument
//
// inductive der : Term → Term → Sort → TYPE ≔
//
// // Types
// | der_sort : Π(s : Sort), der (tsort s) (tsort (snext s)) (snext (snext s))
// | der_prod :
//   Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s'))
//   → der (tfun A B) (tsort (smax s s')) (snext (smax s s'))
// | der_sigma :
//   Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s'))
//   → der (tsum A B) (tsort (smax s s')) (snext (smax s s'))
// | der_prop_type_eq :
//   Π(s : Sort), Π(A u v : Term),
//   der A (tsort s) (snext s) → der u A s → der v A s → der (teq A u v) (tsort s) (snext s)
//
// // Structural rules
// | der_var : Π(s : Sort), Π(A : Term), Π(v : Var), der (VAR v A s) A s
// | der_type_conv :
//   Π (u A B : Term), Π(s : Sort),
//   der u A s → der_eq (snext s) (tsort s) A B → der u B s
//
// // λ-calculus terms
// | der_abs :
//   Π(s s' : Sort), Π(A : Term), Π(t B : Term → Term),
//   der A (tsort s) (snext s) → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s'))
//   → (Π(v : Var), der (t (VAR v A s)) (B (VAR v A s)) s')
//   → der (tabs A B t) (tfun A B) (smax s s')
// | der_app :
//   Π(s s' : Sort), Π(A t u : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s'))
//   → der t (tfun A B) (smax s s') → der u A s → der (tapp A B t u) (B u) s'
// | der_pair :
//   Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → der u A s
//   → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s')) → der v (B u) s'
//   → der (tpair A B u v) (tsum A B) (smax s s')
// | der_π1 :
//   Π(s s' : Sort), Π(p A : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) →
//   der p (tsum A B) (smax s s') → der (π1 A B p) A s
// | der_π2 :
//   Π(s s' : Sort), Π(p A : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s')) →
//   der p (tsum A B) (smax s s') → der (π2 A B p) (B (π1 A B p)) s'
//
// // Equality terms
// | der_refl :
//   Π(s : Sort), Π(u A : Term),
//   der A (tsort s) (snext s) → der u A s → der (trefl A u) (teq A u u) s
// | der_uip :
//   Π(s : Sort), Π(e1 e2 u v A : Term),
//   der e1 (teq A u v) s → der e2 (teq A u v) s → der (uip A u v e1 e2) (teq (teq A u v) e1 e2) s
// | der_J :
//   Π(s s' : Sort), Π(A u v p w : Term), Π(P : Term → Term → Term),
//   der A (tsort s) (snext s) → der u A s → der v A s
//   → (Π(v1 v2 : Var), der (P (VAR v1 A s) (VAR v2 (teq A u (VAR v1 A s)) s)) (tsort s') (snext s'))
//   → der p (teq A u v) s → der w (P u (trefl A u)) s'
//   → der (J A u P w v p) (P v p) s'
// | der_funext :
//   Π(s : Sort), Π(f g A e : Term), Π(B : Term → Term),
//   der f (tfun A B) s → der g (tfun A B) s
//   → der e (tfun A (λ u, teq (B u) (tapp A B f u) (tapp A B g u))) s
//   → der (funext A B f g e) (teq (tfun A B) f g) s
//
// with der_eq : Sort → Term → Term → Term → TYPE ≔
//
// // Computation
// | der_eq_beta :
//   Π(s s' : Sort), Π(u A : Term), Π(t B : Term → Term),
//   der A (tsort s) (snext s) → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s'))
//   → (Π(v : Var), der (t (VAR v A s)) (B (VAR v A s)) s') → der u A s
//   → der_eq s' (B u) (tapp A B (tabs A B t) u) (t u)
// | der_eq_J :
//   Π(s s' : Sort), Π(u A w : Term), Π(P : Term → Term → Term),
//   der A (tsort s) (snext s) → der u A s
//   → (Π(v1 v2 : Var), der (P (VAR v1 A s) (VAR v2 (teq A u (VAR v1 A s)) s)) (tsort s') (snext s'))
//   → der w (P u (trefl A u)) s'
//   → der_eq s' (P u (trefl A u)) (J A u P w u (trefl A u)) w
// | der_eq_π1 :
//   Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → der u A s → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s')) → der v (B u) s'
//   → der_eq s A (π1 A B (tpair A B u v)) u
// | der_eq_π2 :
//   Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
//   der A (tsort s) (snext s) → der u A s → (Π(v : Var), der (B (VAR v A s)) (tsort s') (snext s')) → der v (B u) s'
//   → der_eq s' (B u) (π2 A B (tpair A B u v)) v
//
// // Conversion
// | der_eq_conversion :
//   Π(s : Sort), Π(t1 t2 T1 T2 : Term),
//   der T1 (tsort s) (snext s) → der T2 (tsort s) (snext s)
//   → der_eq s T1 t1 t2 → der_eq (snext s) (tsort s) T1 T2
//   → der_eq s T2 t1 t2
// | der_eq_lift :
//   Π(s : Sort), Π(e u v A : Term),
//   der e (teq A u v) s → der_eq s A u v
//
// // Congruence
// | der_eq_refl :
//   Π(s : Sort), Π(u A : Term), der u A s → der_eq s A u u
// | der_eq_trans :
//   Π(s : Sort), Π(u v w A : Term),
//   der_eq s A u v → der_eq s A v w → der_eq s A u w
// | der_eq_symm :
//   Π(s : Sort), Π(u v A : Term), der_eq s A u v → der_eq s A v u
// | der_eq_context :
//   Π(s s' : Sort), Π(u u' A B : Term), Π(C C' : Term → Term),
//   der_eq s A u u' → der B (tsort s') (snext s')
//   → (Π(v : Var), der_eq s' B (C (VAR v A s)) (C' (VAR v A s)))
//   → der_eq s' B (C u) (C' u');
//
//
//
// // Aliases
// symbol tarrow : Term → Term → Term
//  ≔ λ A B, tfun A (λ _, B);
//
// // Reification in ITT
// symbol ider : Term → Term → Sort → ITT.U ITT.s0;
// symbol ider_eq : Sort → Term → Term → Term → ITT.U ITT.s0;
// rule ITT.ε ITT.s0 (ider $t $T $s) ↪ der $t $T $s
// with ITT.ε ITT.s0 (ider_eq $s $T $t1 $t2) ↪ der_eq $s $T $t1 $t2;
