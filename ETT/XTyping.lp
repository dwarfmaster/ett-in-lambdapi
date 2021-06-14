
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

with der_eq : Context → Sort → Term → Term → Term → TYPE ≔

// Computation
| der_eq_beta :
  Π(Γ : Context), Π(s s' : Sort), Π(u A t B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der (Push A s Γ) t B s' → der Γ u A s
  → der_eq Γ s' (apply1 B u) (tapp A B (tabs A B t) u) (apply1 t u)
| der_eq_eta :
  Π(Γ : Context), Π(s s' : Sort), Π(A f B : Term),
  der Γ A (tsort s) (snext s) → der (Push A s Γ) B (tsort s') (snext s')
  → der Γ f (tfun A B) (smax s s')
  → der_eq Γ (smax s s') (tfun A B) (tabs A B (tapp (Shift A) (Shift1 B) (Shift f) (var db0))) f
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

// Structure
| der_eq_refl :
  Π(Γ : Context), Π(s : Sort), Π(u A : Term), der Γ u A s → der_eq Γ s A u u
| der_eq_trans :
  Π(Γ : Context), Π(s : Sort), Π(u v w A : Term),
  der_eq Γ s A u v → der_eq Γ s A v w → der_eq Γ s A u w
| der_eq_symm :
  Π(Γ : Context), Π(s : Sort), Π(u v A : Term),
  der_eq Γ s A u v → der_eq Γ s A v u

// Congruence
// Lambda calculus
| der_eq_cong_tfun :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der_eq Γ (snext (smax s s')) (tsort (smax s s')) (tfun A1 B1) (tfun A2 B2)
| der_eq_cong_tabs :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 t1 t2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der_eq (Push A1 s Γ) s' B1 t1 t2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der (Push A1 s Γ) t1 B1 s' → der (Push A2 s Γ) t2 B2 s'
  → der_eq Γ (smax s s') (tfun A1 B1) (tabs A1 B1 t1) (tabs A2 B2 t2)
| der_eq_cong_tapp :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 f1 f2 a1 a2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der_eq Γ (smax s s') (tfun A1 B1) f1 f2 → der_eq Γ s A1 a1 a2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der Γ f1 (tfun A1 B1) (smax s s') → der Γ f2 (tfun A2 B2) (smax s s')
  → der Γ a1 A1 s → der Γ a2 A2 s
  → der_eq Γ s' (apply1 B1 a1) (tapp A1 B1 f1 a1) (tapp A2 B2 f2 a2)
// Pairs
| der_eq_cong_tsum :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der_eq Γ (snext (smax s s')) (tsort (smax s s')) (tsum A1 B1) (tsum A2 B2)
| der_eq_cong_tpair :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 a1 a2 b1 b2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der_eq Γ s A1 a1 a2 → der_eq Γ s' (apply1 B1 a1) b1 b2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der Γ a1 A1 s → der Γ a2 A2 s
  → der Γ b1 (apply1 B1 a1) s' → der Γ b2 (apply1 B2 a2) s'
  → der_eq Γ (smax s s') (tsum A1 B1) (tpair A1 B1 a1 b1) (tpair A2 B2 a2 b2)
| der_eq_cong_π1 :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 p1 p2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der_eq Γ (smax s s') (tsum A1 B1) p1 p2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der Γ p1 (tsum A1 B1) (smax s s') → der Γ p2 (tsum A2 B2) (smax s s')
  → der_eq Γ s A1 (π1 A1 B1 p1) (π1 A2 B2 p2)
| der_eq_cong_π2 :
  Π(Γ : Context), Π(s s' : Sort), Π(A1 A2 B1 B2 p1 p2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2
  → der_eq Γ (smax s s') (tsum A1 B1) p1 p2
  → der (Push A1 s Γ) B1 (tsort s') (snext s') → der (Push A2 s Γ) B2 (tsort s') (snext s')
  → der Γ p1 (tsum A1 B1) (smax s s') → der Γ p2 (tsum A2 B2) (smax s s')
  → der_eq Γ s' (apply1 B1 (π1 A1 B1 p1)) (π2 A1 B1 p1) (π2 A2 B2 p2)
// Equality
| der_eq_cong_teq :
  Π(Γ : Context), Π(s : Sort), Π(A1 A2 a1 a2 b1 b2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq Γ s A1 a1 a2 → der_eq Γ s A1 b1 b2
  → der Γ a1 A1 s → der Γ a2 A2 s
  → der Γ b1 A1 s → der Γ b2 A2 s
  → der_eq Γ (snext s) (tsort s) (teq A1 a1 b1) (teq A2 a2 b2)
| der_eq_cong_trefl :
  Π(Γ : Context), Π(s : Sort), Π(A1 A2 a1 a2 : Term),
  der_eq Γ (snext s) (tsort s) A1 A2 → der_eq Γ s A1 a1 a2
  → der Γ a1 A1 s → der Γ a2 A2 s
  → der_eq Γ s (teq A1 a1 a1) (trefl A1 a1) (trefl A2 a2)
;
