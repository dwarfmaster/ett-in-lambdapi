
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
with smax (snext $n) (snext $m) ↪ snext (smax $n $m)
with smax $s $s ↪ $s;
symbol sadd : Sort → Sort → Sort;
rule sadd s0 $n ↪ $n
with sadd $n s0 ↪ $n
with sadd (snext $n) $m ↪ snext (sadd $n $m)
with sadd $n (snext $m) ↪ snext (sadd $n $m);

/* De Bruijn indices */
constant symbol DBId : TYPE;
constant symbol db0 : DBId;
constant symbol dbsucc : DBId → DBId;
symbol dbadd : DBId → DBId → DBId;
symbol dbprev : DBId → DBId;
symbol db1 : DBId ≔ dbsucc db0;
symbol db2 : DBId ≔ dbsucc db1;
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
with shift $i (teq $A $u $v) ↪ teq (shift $i $A) (shift $i $u) (shift $i $v)
with shift $i (funext $A $B $f $g $ext) ↪ funext (shift $i $A) (shift (dbsucc $i) $B)
                                                  (shift $i $f) (shift $i $g) (shift $i $ext)
with shift $i (uip $A $u $v $p $q) ↪ uip (shift $i $A) (shift $i $u) (shift $i $v) (shift $i $p) (shift $i $q);
symbol Shift : Term → Term ≔ shift db0;
symbol ShiftN : DBId → Term → Term;
rule ShiftN db0 $t ↪ Shift $t
with ShiftN (dbsucc $n) $t ↪ Shift (ShiftN $n $t)
with ShiftN _ (tsort $s) ↪ tsort $s;

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
with subst $i $V (teq $A $u $v) ↪ teq (subst $i $V $A) (subst $i $V $u) (subst $i $V $v)
with subst $i $V (funext $A $B $f $g $ext) ↪ funext (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
                                                     (subst $i $V $f) (subst $i $V $g) (subst $i $V $ext)
with subst $i $V (uip $A $u $v $p $q) ↪ uip (subst $i $V $A) (subst $i $V $u) (subst $i $V $v) (subst $i $V $p) (subst $i $V $q);
rule subst db0 _ (Shift $t) ↪ $t;
symbol apply1 (t u : Term) : Term ≔ subst db0 u t;

// Typing context
constant symbol Context : TYPE;
constant symbol Push : Term → Sort → Context → Context;
constant symbol Empty : Context;
symbol Append : Context → Context → Context;
rule Append (Push $t $s $Γ) $Γ2 ↪ Push $t $s (Append $Γ $Γ2)
with Append Empty $Γ ↪ $Γ;

symbol get : Context → DBId → Term;
symbol getS : Context → DBId → Sort;
symbol getΓ : Context → DBId → Context;
rule get (Push $t _ _) db0 ↪ $t
with get (Push _ _ $t) (dbsucc $i) ↪ get $t $i
with getS (Push _ $s _) db0 ↪ $s
with getS (Push _ _ $t) (dbsucc $i) ↪ getS $t $i
with getΓ (Push _ _ $t) db0 ↪ $t
with getΓ (Push _ _ $t) (dbsucc $i) ↪ getΓ $t $i
with getΓ (getΓ $Γ $n) $m ↪ getΓ $Γ (dbsucc (dbadd $n $m));


// Typing derivation
inductive der_context : Context → TYPE ≔
| der_context_empty : der_context Empty
| der_context_push : Π(Γ : Context), Π(s : Sort), Π(A : Term),
  der Γ A (tsort s) (snext s) → der_context Γ → der_context (Push A s Γ)

with der : Context → Term → Term → Sort → TYPE ≔

// Types
| der_sort : Π(Γ : Context), Π(s : Sort),
  der_context Γ → der Γ (tsort s) (tsort (snext s)) (snext (snext s))
| der_prod :
  Π(Γ : Context), Π(s s' : Sort), Π(A B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ (tfun A B) (tsort (smax s s')) (snext (smax s s'))
| der_sigma :
  Π(Γ : Context), Π(s s' : Sort), Π(A B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ (tsum A B) (tsort (smax s s')) (snext (smax s s'))
| der_prop_type_eq :
  Π(Γ : Context), Π(s : Sort), Π(A u v : Term),
  der Γ A (tsort s) (snext s) → der Γ u A s → der Γ v A s → der Γ (teq A u v) (tsort s) (snext s)
// Structural rules
| der_var :
  Π(Γ : Context), Π(id : DBId), der_context Γ
  → der Γ (var id) (ShiftN id (get Γ id)) (getS Γ id)
| der_type_conv :
  Π(Γ : Context), Π(u A B : Term), Π(s : Sort),
  der Γ u A s → der_eq Γ (snext s) (tsort s) A B → der Γ u B s

// λ-calculus terms
| der_abs :
  Π(Γ : Context), Π(s s' : Sort), Π(A t B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der (Push A s Γ) t B s'
  → der Γ (tabs A B t) (tfun A B) (smax s s')
| der_app :
  Π(Γ : Context), Π(s s' : Sort), Π(A t u B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ t (tfun A B) (smax s s') → der Γ u A s → der Γ (tapp A B t u) (apply1 B u) s'
| der_pair :
  Π(Γ : Context), Π(s s' : Sort), Π(u A v B : Term),
  der Γ A (tsort s) (snext s) → der Γ u A s
  → der (Push A s Γ) B (tsort s') (snext s') → der Γ v (apply1 B u) s'
  → der Γ (tpair A B u v) (tsum A B) (smax s s')
| der_π1 :
  Π(Γ : Context), Π(s s' : Sort), Π(p A B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s') →
  der Γ p (tsum A B) (smax s s') → der Γ (π1 A B p) A s
| der_π2 :
  Π(Γ : Context), Π(s s' : Sort), Π(p A B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s') →
  der Γ p (tsum A B) (smax s s') → der Γ (π2 A B p) (apply1 B (π1 A B p)) s'

// Equality terms
| der_refl :
  Π(Γ : Context), Π(s : Sort), Π(u A : Term),
  der Γ A (tsort s) (snext s) → der Γ u A s → der Γ (trefl A u) (teq A u u) s
| der_uip :
  Π(Γ : Context), Π(s : Sort), Π(e1 e2 u v A : Term),
  der Γ e1 (teq A u v) s → der Γ e2 (teq A u v) s → der Γ (uip A u v e1 e2) (teq (teq A u v) e1 e2) s
| der_funext :
  Π(Γ : Context), Π(s s' : Sort), Π(f g A e B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ f (tfun A B) (smax s s') → der Γ g (tfun A B) (smax s s')
  → der Γ e (tfun A (teq B (tapp A B f (var db0)) (tapp A B g (var db0)))) (smax s s')
  → der Γ (funext A B f g e) (teq (tfun A B) f g) (smax s s')

with der_eq : Context → Sort → Term → Term → Term → TYPE ≔

// Computation
| der_eq_beta :
  Π(Γ : Context), Π(s s' : Sort), Π(u A t B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der (Push A s Γ) t B s' → der Γ u A s
  → der_eq Γ s' (apply1 B u) (tapp A B (tabs A B t) u) (apply1 t u)
| der_eq_π1 :
  Π(Γ : Context), Π(s s' : Sort), Π(u A v B : Term),
  der Γ A (tsort s) (snext s) → der Γ u A s → der (Push A s Γ) B (tsort s') (snext s') → der Γ v (apply1 B u) s'
  → der_eq Γ s A (π1 A B (tpair A B u v)) u
| der_eq_π2 :
  Π(Γ : Context), Π(s s' : Sort), Π(u A v B : Term),
  der Γ A (tsort s) (snext s) → der Γ u A s → der (Push A s Γ) B (tsort s') (snext s') → der Γ v (apply1 B u) s'
  → der_eq Γ s' (apply1 B u) (π2 A B (tpair A B u v)) v

// Conversion
| der_eq_conversion :
  Π(Γ : Context), Π(s : Sort), Π(t1 t2 T1 T2 : Term),
  der_eq Γ s T1 t1 t2 → der_eq Γ (snext s) (tsort s) T1 T2
  → der_eq Γ s T2 t1 t2
| der_eq_lift :
  Π(Γ : Context), Π(s : Sort), Π(e u v A : Term),
  der Γ e (teq A u v) s → der_eq Γ s A u v

// Congruence
| der_eq_refl :
  Π(Γ : Context), Π(s : Sort), Π(u A : Term), der Γ u A s → der_eq Γ s A u u
| der_eq_trans :
  Π(Γ : Context), Π(s : Sort), Π(u v w A : Term),
  der_eq Γ s A u v → der_eq Γ s A v w → der_eq Γ s A u w
| der_eq_symm :
  Π(Γ : Context), Π(s : Sort), Π(u v A : Term),
  der_eq Γ s A u v → der_eq Γ s A v u

// Context
// Prod
| der_eq_ctx_prod_domain :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B : Term),
  der_eq Γ (snext s) (tsort s) A A' → der (Push A s Γ) B (tsort s') (snext s')
  → der_eq Γ (snext (smax s s')) (tsort (smax s s')) (tfun A B) (tfun A' B)
| der_eq_ctx_prod_codomain :
  Π(Γ : Context), Π(s s' : Sort), Π(A B B' : Term),
  der Γ A (tsort s) (snext s) → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der_eq Γ (snext (smax s s')) (tsort (smax s s')) (tfun A B) (tfun A B')
// tabs
| der_eq_ctx_tabs_domain :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B t : Term),
  der_eq Γ (snext s) (tsort s) A A' → der (Push A s Γ) B (tsort s') (snext s')
  → der (Push A s Γ) t B s'
  → der_eq Γ (smax s s') (tfun A B) (tabs A B t) (tabs A' B t)
| der_eq_ctx_tabs_codomain :
  Π(Γ : Context), Π(s s' : Sort), Π(A B B' t : Term),
  der Γ A (tsort s) (snext s') → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der (Push A s Γ) t B s'
  → der_eq Γ (smax s s') (tfun A B) (tabs A B t) (tabs A B' t)
| der_eq_ctx_tabs_body :
  Π(Γ : Context), Π(s s' : Sort), Π(A B t t' : Term),
  der Γ A (tsort s) (snext s') → der (Push A s Γ) B  (tsort s') (snext s')
  → der_eq (Push A s Γ) s' B t t'
  → der_eq Γ (smax s s') (tfun A B) (tabs A B t) (tabs A B t')
// App
| der_eq_ctx_app_domain :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B f u : Term),
  der_eq Γ (snext s) (tsort s) A A' → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ f (tfun A B) (smax s s') → der Γ u A s
  → der_eq Γ s' (apply1 B u) (tapp A B f u) (tapp A' B f u)
| der_eq_ctx_app_codomain :
  Π(Γ : Context), Π(s s' : Sort), Π(A B B' f u : Term),
  der Γ A (tsort s) (snext s) → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der Γ f (tfun A B) (smax s s') → der Γ u A s
  → der_eq Γ s' (apply1 B u) (tapp A B f u) (tapp A B' f u)
| der_eq_ctx_app_fun :
  Π(Γ : Context), Π(s s' : Sort), Π(A B f f' u : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der_eq Γ (smax s s') (tfun A B) f f' → der Γ u A s
  → der_eq Γ s' (apply1 B u) (tapp A B f u) (tapp A B f' u)
| der_eq_ctx_app_arg :
  Π(Γ : Context), Π(s s' : Sort), Π(A B f u u' : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ f (tfun A B) (smax s s') → der_eq Γ s A u u'
  → der_eq Γ s' (apply1 B u) (tapp A B f u) (tapp A B f u')
// Sum
| der_eq_ctx_sum1 :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B : Term),
  der_eq Γ (snext s) (tsort s) A A' → der (Push A s Γ) B (tsort s') (snext s')
  → der_eq Γ (snext (smax s s')) (tsort (smax s s')) (tsum A B) (tsum A' B)
| der_eq_ctx_sum2 :
  Π(Γ : Context), Π(s s' : Sort), Π(A B B' : Term),
  der Γ A (tsort s) (snext s) → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der_eq Γ (snext (smax s s')) (tsort (smax s s')) (tsum A B) (tsum A B')
// Pair
| der_eq_ctx_pair_t1 :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B u v : Term),
  der_eq Γ (snext s) (tsort s) A A' → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ u A s → der Γ v (apply1 B u) s'
  → der_eq Γ (smax s s') (tsum A B) (tpair A B u v) (tpair A' B u v)
| der_eq_ctx_pair_t2 :
  Π(Γ : Context), Π(s s' : Sort), Π(A B B' u v : Term),
  der Γ A (tsort s) (snext s) → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der Γ u A s → der Γ v (apply1 B u) s'
  → der_eq Γ (smax s s') (tsum A B) (tpair A B u v) (tpair A B' u v)
| der_eq_ctx_pair_π1 :
  Π(Γ : Context), Π(s s' : Sort), Π(A B u u' v : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der_eq Γ s A u u' → der Γ v (apply1 B u) s'
  → der_eq Γ (smax s s') (tsum A B) (tpair A B u v) (tpair A B u' v)
| der_eq_ctx_pair_π2 :
  Π(Γ : Context), Π(s s' : Sort), Π(A B u v v' : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ u A s → der_eq Γ s' (apply1 B u) v v'
  → der_eq Γ (smax s s') (tsum A B) (tpair A B u v) (tpair A B u v')
// Others
| der_eq_ctx_π1 :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B B' p p' : Term),
  der_eq Γ (snext s) (tsort s) A A' → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der_eq Γ (smax s s') (tsum A B) p p'
  → der_eq Γ s A (π1 A B p) (π1 A' B' p')
| der_eq_ctx_π2 :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B B' p p' : Term),
  der_eq Γ (snext s) (tsort s) A A' → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der_eq Γ (smax s s') (tsum A B) p p'
  → der_eq Γ s' (apply1 B (π1 A B p)) (π2 A B p) (π2 A' B' p')
| der_eq_ctx_refl :
  Π(Γ : Context), Π(s : Sort), Π(A A' u u' : Term),
  der_eq Γ (snext s) (tsort s) A A' → der_eq Γ s A u u'
  → der_eq Γ s (teq A u u) (trefl A u) (trefl A' u')
| der_eq_ctx_teq :
  Π(Γ : Context), Π(s : Sort), Π(A A' u u' v v' : Term),
  der_eq Γ (snext s) (tsort s) A A' → der_eq Γ s A u u' → der_eq Γ s A v v'
  → der_eq Γ (snext s) (tsort s) (teq A u v) (teq A' u' v')
| der_eq_ctx_funext :
  Π(Γ : Context), Π(s s' : Sort), Π(A A' B B' f f' g g' e e' : Term),
  der_eq Γ (snext s) (tsort s) A A' → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der_eq Γ (smax s s') (tfun A B) f f' → der_eq Γ (smax s s') (tfun A B) g g'
  → der_eq Γ (smax s s') (tfun A (teq B (tapp A B f (var db0)) (tapp A B g (var db0)))) e e'
  → der_eq Γ (smax s s') (teq (tfun A B) f g) (funext A B f g e) (funext A' B' f' g' e')
| der_eq_ctx_uip :
  Π(Γ : Context), Π(s : Sort), Π(A A' u u' v v' e1 e1' e2 e2' : Term),
  der_eq Γ (snext s) (tsort s) A A' → der_eq Γ s A u u' → der_eq Γ s A v v'
  → der_eq Γ s (teq A u v) e1 e1' → der_eq Γ s (teq A u v) e2 e2'
  → der_eq Γ s (teq (teq A u v) e1 e2) (uip A u v e1 e2) (uip A' u' v' e1' e2')
;




// Aliases
symbol tarrow : Term → Term → Term
 ≔ λ A B, tfun A (Shift B);

// Reification in ITT
symbol ider_context : Context → ITT.U ITT.s0;
symbol ider : Context → Term → Term → Sort → ITT.U ITT.s0;
symbol ider_eq : Context → Sort → Term → Term → Term → ITT.U ITT.s0;
rule ITT.ε ITT.s0 (ider_context $Γ) ↪ der_context $Γ
with ITT.ε ITT.s0 (ider $Γ $t $T $s) ↪ der $Γ $t $T $s
with ITT.ε ITT.s0 (ider_eq $Γ $s $T $t1 $t2) ↪ der_eq $Γ $s $T $t1 $t2;


// Lemmas
symbol der_shift1 (Γ : Context) (t T : Term) (s : Sort) (_ : der (getΓ Γ db0) t T s) : der Γ (Shift t) (Shift T) s;
symbol der_shift (id : DBId) (Γ : Context) (t T : Term) (s : Sort) (_ : der (getΓ Γ id) t T s) : der Γ (ShiftN id t) (ShiftN id T) s;
rule der_shift db0 $Γ $t $T $s $d ↪ der_shift1 $Γ $t $T $s $d
with der_shift (dbsucc $id) $Γ $t $T $s $d ↪ der_shift1 $Γ _ _ _ (der_shift $id _ $t $T $s $d);

symbol der_eq_ctx (Γ : Context) (s s' : Sort) (c C t1 t2 T : Term)
                  (_ : der_eq Γ s T t1 t2) (_ : der (Push T s Γ) c C s')
                  : der_eq Γ s' (apply1 C t1) (apply1 c t1) (apply1 c t2);

symbol der_conv_in_ctx (Γ : Context) (s s' : Sort) (A A' t B : Term)
                       (_ : der_eq Γ (snext s) (tsort s) A A') (_ : der (Push A s Γ) t B s')
                       : der (Push A' s Γ) t B s';
