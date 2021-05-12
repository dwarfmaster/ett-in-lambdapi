
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.ETT;
require open ETT.ITT;
require ETT.Inversions as I;
require open ETT.HEq;

// Translation of sorts
symbol τ_s : ETT.Sort → Sort;
rule τ_s ETT.s0 ↪ s0
with τ_s (ETT.snext $s) ↪ snext (τ_s $s)
with τ_s (ETT.smax $s $s') ↪ smax (τ_s $s) (τ_s $s');

// Translation declarations
constant symbol TContext : TYPE;
symbol tgetΓ : ETT.DBId → TContext → TContext;
symbol τ_Γ : TContext → Context;
rule τ_Γ (tgetΓ $id $Γ) ↪ getΓ (τ_Γ $Γ) $id;
symbol τ_T (Γ : TContext) {T : ETT.Term} {s : ETT.Sort} :
  der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s) → U (τ_s s);
symbol τ (Γ : TContext) {s : ETT.Sort} {t T : ETT.Term} (d : der (τ_Γ Γ) t T s) :
  let sort ≔ I.inv_sort d in
  ε (τ_s s) (τ_T Γ sort);
symbol τ_eq_type (Γ : TContext) {s : ETT.Sort} {T t1 t2 : ETT.Term} (d : der_eq (τ_Γ Γ) s T t1 t2) : U _ ≔
  let d1 ≔ I.inv_eq_t1 d in
  let d2 ≔ I.inv_eq_t2 d in
  let ds1 ≔ I.inv_sort d1 in
  let ds2 ≔ I.inv_sort d2 in
  HEq' (τ_s s) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);
symbol τ_eq (Γ : TContext) {s : ETT.Sort} {T t1 t2 : ETT.Term} (d : der_eq (τ_Γ Γ) s T t1 t2) : ε _ (τ_eq_type Γ d);
symbol convert_T (Γ : TContext) {T : ETT.Term} {s : ETT.Sort} (d1 d2 : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s)) :
  let S ≔ τ_s s in ε (snext S) (eq (snext S) (u S) (τ_T Γ d1) (τ_T Γ d2));
symbol convert (Γ : TContext) {s : ETT.Sort} {t T : ETT.Term} (d1 d2 : der (τ_Γ Γ) t T s) :
  let ds1 ≔ I.inv_sort d1 in
  let ds2 ≔ I.inv_sort d2 in
  HEq (τ_s s) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);

// For things to type, we need to make sure that the translation of a sort is a universe
rule @τ_T _ (ETT.tsort $s) (ETT.snext $s) _ ↪ u (τ_s $s);
rule @τ _ (ETT.snext (ETT.snext $s)) (ETT.tsort $s) (ETT.tsort (ETT.snext $s)) _ ↪ u (τ_s $s);

// Translation context
constant symbol TEmpty : TContext;
constant symbol TPush
  (Γ : TContext) (s : ETT.Sort) (A : ETT.Term) (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
  : ε (τ_s s) (τ_T Γ dA) → TContext;
symbol Extend : TContext → TContext → TContext;

// Translation of context
rule τ_Γ TEmpty ↪ Empty
with τ_Γ (TPush $t $s $A _ _) ↪ Push $A $s (τ_Γ $t)
with τ_Γ (Extend $Γ1 $Γ2) ↪ Append (τ_Γ $Γ2) (τ_Γ $Γ1);

// Translation context invariant
symbol well_formed_tcontext (Γ : TContext) : der_context (τ_Γ Γ);
rule well_formed_tcontext TEmpty ↪ der_context_empty
with well_formed_tcontext (TPush $Γ $s $A $dA _)
  ↪ der_context_push (τ_Γ $Γ) $s $A $dA (well_formed_tcontext $Γ);
