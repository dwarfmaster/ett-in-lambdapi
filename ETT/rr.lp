
require ETT.main as ETT;
require ETT.itt as ITT;
require ETT.inversions as I;

// Helper definitions
symbol ε ≔ ITT.ε;
symbol univ ≔ ITT.U;
symbol transport (s : ITT.Sort) (T U : univ s) (e : ε _ (ITT.eq (ITT.snext s) (ITT.u s) T U)) : ε s T → ε s U ≔
  λ t, ITT.J (ITT.snext s) s (ITT.u s) T (λ (X : univ s) (_ : ε (ITT.snext s) (ITT.eq (ITT.snext s) _ T X)), X) t U e;

symbol heterogeneous_eq' (s : ITT.Sort) (T U : univ s) (t : ε s T) (u : ε s U) : ITT.U _ ≔
  ITT.S _ _ (ITT.eq _ (ITT.u s) T U) (λ p, ITT.eq s U (transport s T U p t) u);
symbol heterogeneous_eq (s : ITT.Sort) (T U : univ s) (t : ε s T) (u : ε s U) : TYPE ≔
  ε _ (heterogeneous_eq' s T U t u);
symbol Pack' (s : ITT.Sort) (A1 A2 : univ s) : ITT.U _ ≔
  ITT.S _ _ A1 (λ x, ITT.S _ _ A2 (λ y, heterogeneous_eq' s A1 A2 x y));

symbol Pack (s : ITT.Sort) (A1 A2 : univ s) : TYPE ≔ ε _ (Pack' s A1 A2);
symbol Proj1 {s : ITT.Sort} {A1 A2 : univ s} (p : Pack s A1 A2) : ε s A1 ≔
  ITT.proj1 _ _ _ _ p;
symbol Proj2 {s : ITT.Sort} {A1 A2 : univ s} (p : Pack s A1 A2) : ε s A2 ≔
  ITT.proj1 _ _ _ _ (ITT.proj2 _ _ _ _ p);
symbol Proje {s : ITT.Sort} {A1 A2 : univ s} (p : Pack s A1 A2) : heterogeneous_eq s A1 A2 (Proj1 p) (Proj2 p) ≔
  ITT.proj2 _ _ _ _ (ITT.proj2 _ _ _ _ p);

// Translation of sorts
symbol τ_s : ETT.Sort → ITT.Sort;
rule τ_s ETT.s0 ↪ ITT.s0
with τ_s (ETT.snext $s) ↪ ITT.snext (τ_s $s)
with τ_s (ETT.smax $s $s') ↪ ITT.smax (τ_s $s) (τ_s $s');

// Translation declarations
constant symbol TContext : TYPE;
symbol tgetΓ : ETT.DBId → TContext → TContext;
symbol τ_Γ : TContext → ETT.Context;
rule τ_Γ (tgetΓ $id $Γ) ↪ ETT.getΓ (τ_Γ $Γ) $id;
symbol τ_T (Γ : TContext) (T : ETT.Term) (s : ETT.Sort) : ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s) → univ (τ_s s);
symbol τ (Γ : TContext) (s : ETT.Sort) (t T : ETT.Term) (d : ETT.der (τ_Γ Γ) t T s) :
  let sort ≔ I.inv_sort (τ_Γ Γ) s t T d in
  ε (τ_s s) (τ_T (tgetΓ (I.subId sort) Γ) T s (I.subP sort));
symbol τ_eq (Γ : TContext) (s : ETT.Sort) (T t1 t2 : ETT.Term) (d : ETT.der_eq (τ_Γ Γ) s T t1 t2) :
  let d1 ≔ I.inv_eq_t1 (τ_Γ Γ) s T t1 t2 d in
  let d2 ≔ I.inv_eq_t2 (τ_Γ Γ) s T t1 t2 d in
  let s1 ≔ I.inv_sort (τ_Γ Γ) s t1 T d1 in
  let s2 ≔ I.inv_sort (τ_Γ Γ) s t2 T d2 in
  heterogeneous_eq (τ_s s)
    (τ_T (tgetΓ (I.subId s1) Γ) T s (I.subP s1))
    (τ_T (tgetΓ (I.subId s2) Γ) T s (I.subP s2))
    (τ Γ s t1 T d1) (τ Γ s t2 T d2);
symbol convert_T (Γ : TContext) (T : ETT.Term) (s : ETT.Sort) (d1 d2 : ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s)) :
  let S ≔ τ_s s in ε (ITT.snext S) (ITT.eq (ITT.snext S) (ITT.u S) (τ_T Γ _ _ d1) (τ_T Γ _ _ d2));
symbol convert (Γ : TContext) (s : ETT.Sort) (t T : ETT.Term) (d1 d2 : ETT.der (τ_Γ Γ) t T s) :
  let s1 ≔ I.inv_sort (τ_Γ Γ) s t T d1 in
  let s2 ≔ I.inv_sort (τ_Γ Γ) s t T d2 in
  heterogeneous_eq (τ_s s)
    (τ_T (tgetΓ (I.subId s1) Γ) T s (I.subP s1))
    (τ_T (tgetΓ (I.subId s2) Γ) T s (I.subP s2))
    (τ Γ s t T d1) (τ Γ s t T d2);


// Translation context
constant symbol TEmpty : TContext;
constant symbol TPush
  (Γ : TContext) (s : ETT.Sort) (A : ETT.Term) (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
  : ITT.ε (τ_s s) (τ_T Γ A s dA) → TContext;

rule τ_Γ TEmpty ↪ ETT.Empty
with τ_Γ (TPush $t $s $A _ _) ↪ ETT.Push $A $s (τ_Γ $t);

symbol tgetS (id : ETT.DBId) (Γ : TContext) : ETT.Sort ≔ ETT.getS (τ_Γ Γ) id;
symbol tgetA (id : ETT.DBId) (Γ : TContext) : ETT.Term ≔ ETT.get (τ_Γ Γ) id;

rule tgetΓ ETT.db0 (TPush $t _ _ _ _) ↪ $t
with tgetΓ (ETT.dbsucc $id) (TPush $t _ _ _ _) ↪ tgetΓ $id $t;
symbol tgetD (id : ETT.DBId) (Γ : TContext) : ETT.der (τ_Γ (tgetΓ id Γ)) (tgetA id Γ) (ETT.tsort (tgetS id Γ)) (ETT.snext (tgetS id Γ));
rule tgetD ETT.db0 (TPush _ _ _ $d _) ↪ $d
with tgetD (ETT.dbsucc $id) (TPush $t _ _ _ _) ↪ tgetD $id $t;

symbol tgetT (id : ETT.DBId) (Γ : TContext) : ITT.U (τ_s (tgetS id Γ)) ≔
  τ_T (tgetΓ id Γ) (tgetA id Γ) (tgetS id Γ) (tgetD id Γ);
symbol tget (id : ETT.DBId) (Γ : TContext) : ITT.ε (τ_s (tgetS id Γ)) (tgetT id Γ);
rule tget ETT.db0 (TPush _ _ _ _ $a) ↪ $a
with tget (ETT.dbsucc $id) (TPush $t _ _ _ _) ↪ tget $id $t;

// // Translation of type
rule τ_T _ _ _ (ETT.der_sort _ $s _) ↪ ITT.u (τ_s $s);
rule τ_T $Γ _ _ (ETT.der_prod _ $s $s' $A _ $dA $dB)
   ↪ ITT.P (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA)
            (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB);

rule τ $Γ _ _ _ (ETT.der_var _ $id $dΓ)
   ↪ let p ≔ convert_T (tgetΓ $id $Γ) _ _ (tgetD $id $Γ) (I.der_subΓ (τ_Γ $Γ) $id $dΓ) in
      transport _ _ _ p (tget $id $Γ);
