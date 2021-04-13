
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

// Proved using uip
symbol heq_to_eq (s : ITT.Sort) (T : univ s) (t u : ε s T) : heterogeneous_eq s T T t u → ε s (ITT.eq s T t u);

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
  ε (τ_s s) (τ_T Γ T s sort);
symbol τ_eq (Γ : TContext) (s : ETT.Sort) (T t1 t2 : ETT.Term) (d : ETT.der_eq (τ_Γ Γ) s T t1 t2) :
  let d1 ≔ I.inv_eq_t1 (τ_Γ Γ) s T t1 t2 d in
  let d2 ≔ I.inv_eq_t2 (τ_Γ Γ) s T t1 t2 d in
  let ds1 ≔ I.inv_sort (τ_Γ Γ) s t1 T d1 in
  let ds2 ≔ I.inv_sort (τ_Γ Γ) s t2 T d2 in
  heterogeneous_eq (τ_s s)
    (τ_T Γ T s ds1)
    (τ_T Γ T s ds2)
    (τ Γ s t1 T d1) (τ Γ s t2 T d2);
symbol convert_T (Γ : TContext) (T : ETT.Term) (s : ETT.Sort) (d1 d2 : ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s)) :
  let S ≔ τ_s s in ε (ITT.snext S) (ITT.eq (ITT.snext S) (ITT.u S) (τ_T Γ _ _ d1) (τ_T Γ _ _ d2));
symbol convert (Γ : TContext) (s : ETT.Sort) (t T : ETT.Term) (d1 d2 : ETT.der (τ_Γ Γ) t T s) :
  let ds1 ≔ I.inv_sort (τ_Γ Γ) s t T d1 in
  let ds2 ≔ I.inv_sort (τ_Γ Γ) s t T d2 in
  heterogeneous_eq (τ_s s)
    (τ_T Γ T s ds1)
    (τ_T Γ T s ds2)
    (τ Γ s t T d1) (τ Γ s t T d2);


// Translation context
constant symbol TEmpty : TContext;
constant symbol TPush
  (Γ : TContext) (s : ETT.Sort) (A : ETT.Term) (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
  : ITT.ε (τ_s s) (τ_T Γ A s dA) → TContext;

rule τ_Γ TEmpty ↪ ETT.Empty
with τ_Γ (TPush $t $s $A _ _) ↪ ETT.Push $A $s (τ_Γ $t);

rule τ_T (TPush $Γ _ _ _ _) _ _ (ETT.der_shift1 _ _ (ETT.tsort _) _ $d) ↪ τ_T $Γ _ _ $d;

symbol tgetS (id : ETT.DBId) (Γ : TContext) : ETT.Sort ≔ ETT.getS (τ_Γ Γ) id;
symbol tgetA (id : ETT.DBId) (Γ : TContext) : ETT.Term ≔ ETT.get (τ_Γ Γ) id;

rule tgetΓ ETT.db0 (TPush $t _ _ _ _) ↪ $t
with tgetΓ (ETT.dbsucc $id) (TPush $t _ _ _ _) ↪ tgetΓ $id $t;
symbol tgetD (id : ETT.DBId) (Γ : TContext) : ETT.der (τ_Γ (tgetΓ id Γ)) (tgetA id Γ) (ETT.tsort (tgetS id Γ)) (ETT.snext (tgetS id Γ));
rule tgetD ETT.db0 (TPush _ _ _ $d _) ↪ $d
with tgetD (ETT.dbsucc $id) (TPush $t _ _ _ _) ↪ tgetD $id $t;

symbol tgetT (id : ETT.DBId) (Γ : TContext) : ITT.U (τ_s (tgetS id Γ)) ≔
  τ_T (tgetΓ id Γ) (tgetA id Γ) (tgetS id Γ) (tgetD id Γ);
symbol tgetTShift (id : ETT.DBId) (Γ : TContext) : ITT.U (τ_s (tgetS id Γ)) ≔
  τ_T Γ (ETT.ShiftN id (tgetA id Γ)) (tgetS id Γ) (ETT.der_shift id (τ_Γ Γ) _ _ _ (tgetD id Γ));

symbol tget (id : ETT.DBId) (Γ : TContext) : ITT.ε (τ_s (tgetS id Γ)) (tgetT id Γ);
rule tget ETT.db0 (TPush _ _ _ _ $a) ↪ $a
with tget (ETT.dbsucc $id) (TPush $t _ _ _ _) ↪ tget $id $t;
symbol tgetShift (id : ETT.DBId) (Γ : TContext) : ITT.ε (τ_s (tgetS id Γ)) (tgetTShift id Γ);
rule tgetShift ETT.db0 (TPush _ _ _ _ $a) ↪ $a
with tgetShift (ETT.dbsucc $id) (TPush $Γ _ _ _ _) ↪ tgetShift $id $Γ;

// Translation of type
rule τ_T _ (ETT.tsort $s) (ETT.snext $s) _ ↪ ITT.u (τ_s $s);
rule τ $Γ (ETT.snext $s) $T (ETT.tsort $s) $d ↪ τ_T $Γ $T $s $d;

rule τ_T $Γ _ _ (ETT.der_prod _ $s $s' $A _ $dA $dB)
  ↪ ITT.P (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA)
           (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB)
with τ_T $Γ _ _ (ETT.der_sigma _ $s $s' $A _ $dA $dB)
  ↪ ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA)
           (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB)
with τ_T $Γ _ _ (ETT.der_prop_type_eq _ $s _ _ _ $dA $du $dv)
  ↪ let pu ≔ convert_T $Γ _ _ (I.inv_sort (τ_Γ $Γ) _ _ _ $du) $dA in
     let pv ≔ convert_T $Γ _ _ (I.inv_sort (τ_Γ $Γ) _ _ _ $dv) $dA in
     ITT.eq (τ_s $s) (τ_T $Γ _ _ $dA) (transport _ _ _ pu (τ $Γ _ _ _ $du)) (transport _ _ _ pv (τ $Γ _ _ _ $dv))
// der_var and der_conv are hard
// with τ_T $Γ _ _ (ETT.der_var _ $id $dΓ)
//   ↪ tgetShift $id $Γ
// der_type_conv is useless for types, since equality of universe means meta-equality of universes
;

rule τ $Γ _ _ _ (ETT.der_var _ $id $dΓ)
  ↪ let shift ≔ ETT.der_shift $id (τ_Γ $Γ) (tgetA $id $Γ) (ETT.tsort (tgetS $id $Γ)) (ETT.snext (tgetS $id $Γ)) in
     let p ≔ convert_T $Γ _ _ (shift (tgetD $id $Γ)) (shift (I.der_subΓ (τ_Γ $Γ) $id $dΓ)) in
     transport _ _ _ p (tgetShift $id $Γ)

with τ $Γ _ _ _ (ETT.der_abs _ $s _ $A _ _ $dA $dB $dt)
  ↪ λ a, let p ≔ convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort (ETT.Push $A $s (τ_Γ $Γ)) _ _ _ $dt) $dB in
          transport _ _ _ p (τ (TPush $Γ $s $A $dA a) _ _ _ $dt)
;
