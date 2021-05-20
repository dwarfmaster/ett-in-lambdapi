
require open ETT.XAst;
require open ETT.DeBruijn;

// Typing context
constant symbol Context : TYPE;
constant symbol Push : Term → Sort → Context → Context;
constant symbol Empty : Context;

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
  der Γ A (tsort s) (snext s) → der_eq (Push A s Γ) (snext s') (tsort s') B B'
  → der (Push A s Γ) t B s'
  → der_eq Γ (smax s s') (tfun A B) (tabs A B t) (tabs A B' t)
| der_eq_ctx_tabs_body :
  Π(Γ : Context), Π(s s' : Sort), Π(A B t t' : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B  (tsort s') (snext s')
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
