
require ETT.main as ETT;
require ETT.itt as ITT;
require ETT.inversions as I;

// Cheater
symbol magic (s : ITT.Sort) (A : ITT.U s) : ITT.ε s A;

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
symbol τ_T (Γ : TContext) (T : ETT.Term) (s : ETT.Sort) :
  ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s) → univ (τ_s s);
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

// Translation of shifting
symbol τ_shift_eq (Γ : TContext) (s s' : ETT.Sort) (T A : ETT.Term)
                  (dT : ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                  (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                  (a : ε _ (τ_T Γ _ _ dA)) :
  ε _ (ITT.eq _ (ITT.u (τ_s s))
      (τ_T Γ T s dT)
      (τ_T (TPush Γ s' A dA a) (ETT.Shift T) s (ETT.der_shift1 (ETT.Push A s' (τ_Γ Γ)) T (ETT.tsort s) (ETT.snext s) dT)));
symbol τ_shift (Γ : TContext) (s s' : ETT.Sort) (T A : ETT.Term)
               (dT : ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
               (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
               (a : ε _ (τ_T Γ _ _ dA)) ≔
  transport _ _ _ (τ_shift_eq Γ s s' T A dT dA a);
symbol τ_shift' (Γ : TContext) (s s' : ETT.Sort) (T A : ETT.Term)
                (dT : ETT.der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                (a : ε _ (τ_T Γ _ _ dA)) ≔
  transport _ _ _ (ITT.inv_eq (τ_shift_eq Γ s s' T A dT dA a));

// Accessing the context
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
rule tgetShift ETT.db0 (TPush $Γ $s $A $dA $a)
     ↪ τ_shift $Γ $s $s $A $A
          $dA $dA $a $a
with tgetShift (ETT.dbsucc $id) (TPush $Γ $s $A $dA $a)
  ↪ τ_shift $Γ (tgetS $id $Γ) $s (ETT.ShiftN $id (tgetA $id $Γ)) $A
        (ETT.der_shift $id (τ_Γ $Γ) _ _ _ (tgetD $id $Γ))
        $dA $a (tgetShift $id $Γ);

// Converting in the context
symbol convert_Γ (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term) (d1 d2 : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                 (a1 : ε _ (τ_T Γ _ _ d1)) (a2 : ε _ (τ_T Γ _ _ d2))
                 (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) :
  ε _ (ITT.eq _ (ITT.u (τ_s s')) (τ_T (TPush Γ s A d1 a1) _ _ dB) (τ_T (TPush Γ s A d2 a2) _ _ dB));

// Translation of product
symbol τ_fun_eq (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
             (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (df : ETT.der (τ_Γ Γ) (ETT.tfun A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) :
  ε _ (ITT.eq _ (ITT.u (τ_s (ETT.smax s s')))
    (τ_T Γ _ _ df)
    (ITT.P (τ_s s) (τ_s s') (τ_T Γ _ _ dA) (λ a, τ_T (TPush Γ s A dA a) _ _ dB)));
symbol τ_fun (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
             (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (df : ETT.der (τ_Γ Γ) (ETT.tfun A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport _ _ _ (τ_fun_eq Γ s s' A B dA dB df);
symbol τ_fun' (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
             (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (df : ETT.der (τ_Γ Γ) (ETT.tfun A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport _ _ _ (ITT.inv_eq (τ_fun_eq Γ s s' A B dA dB df));

// Translation of substitution
symbol τ_subst_eq (Γ : TContext) (s s' : ETT.Sort) (A B u : ETT.Term)
               (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (du : ETT.der (τ_Γ Γ) u A s) :
  ITT.ε _ (ITT.eq _ (ITT.u (τ_s s'))
    (τ_T (TPush Γ s A (I.inv_sort _ _ _ _ du) (τ Γ s u A du)) B s' dB)
    (τ_T Γ (ETT.apply1 B u) s' (I.substitution (τ_Γ Γ) s (ETT.snext s') A (ETT.tsort s') B dB u du)));
symbol τ_subst (Γ : TContext) (s s' : ETT.Sort) (A B u : ETT.Term)
               (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (du : ETT.der (τ_Γ Γ) u A s) ≔
  transport _ _ _ (τ_subst_eq Γ s s' A B u dB du);
symbol τ_subst' (Γ : TContext) (s s' : ETT.Sort) (A B u : ETT.Term)
               (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (du : ETT.der (τ_Γ Γ) u A s) ≔
  transport _ _ _ (ITT.inv_eq (τ_subst_eq Γ s s' A B u dB du));

// Translation of pairs
symbol τ_sum_eq (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
             (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (dp : ETT.der (τ_Γ Γ) (ETT.tsum A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) :
  ε _ (ITT.eq _ (ITT.u (τ_s (ETT.smax s s')))
      (τ_T Γ _ _ dp)
      (ITT.S (τ_s s) (τ_s s') (τ_T Γ _ _ dA) (λ a, τ_T (TPush Γ s A dA a) _ _ dB)));
symbol τ_sum (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
             (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (dp : ETT.der (τ_Γ Γ) (ETT.tsum A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport _ _ _ (τ_sum_eq Γ s s' A B dA dB dp);
symbol τ_sum' (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
             (dA : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (dp : ETT.der (τ_Γ Γ) (ETT.tsum A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport _ _ _ (ITT.inv_eq (τ_sum_eq Γ s s' A B dA dB dp));

// Recovering well sortedness
symbol der_recover_sort (Γ : ETT.Context) (s s' : ETT.Sort) (A : ETT.Term) :
  ETT.der Γ A (ETT.tsort s) s' → ETT.der Γ A (ETT.tsort s) (ETT.snext s);
rule der_recover_sort _ _ _ _ (ETT.der_sort $Γ $s $dΓ)
  ↪ ETT.der_sort $Γ $s $dΓ
with der_recover_sort _ _ _ _ (ETT.der_prod $Γ $s $s' $A $B $dA $dB)
  ↪ ETT.der_prod $Γ $s $s' $A $B $dA $dB
with der_recover_sort _ _ _ _ (ETT.der_sigma $Γ $s $s' $A $B $dA $dB)
  ↪ ETT.der_sigma $Γ $s $s' $A $B $dA $dB
with der_recover_sort _ _ _ _ (ETT.der_prop_type_eq $Γ $s $A $u $v $dA $du $dv)
  ↪ ETT.der_prop_type_eq $Γ $s $A $u $v $dA $du $dv
;

// Equalities
symbol eq_pair (s s' : ITT.Sort) (A A' : ITT.U s) (B : ITT.ε s A → ITT.U s') (B' : ITT.ε s A' → ITT.U s')
               (eqA : ε _ (ITT.eq (ITT.snext s) (ITT.u s) A A'))
               (eqB : Π(a : ε s A), ITT.ε _ (ITT.eq (ITT.snext s') (ITT.u s') (B a) (B' (transport _ _ _ eqA a)))) :
               ITT.ε _ (ITT.eq (ITT.snext (ITT.smax s s')) (ITT.u (ITT.smax s s')) (ITT.S s s' A B) (ITT.S s s' A' B'));

// For things to type, we need to make sure that the translation of a sort is a universe
rule τ_T _ (ETT.tsort $s) (ETT.snext $s) _ ↪ ITT.u (τ_s $s);
rule τ _ (ETT.snext (ETT.snext $s)) (ETT.tsort $s) (ETT.tsort (ETT.snext $s)) _ ↪ ITT.u (τ_s $s);

// Translation of type
// This is done simply by invoking a term translation of the type
// We know the der_eq is always an instance of der_eq_refl, so we don't bother
// defining it for other proofs of equality.
rule τ_T $Γ $T $s $d
  ↪ τ $Γ (ETT.snext $s) $T (ETT.tsort $s) $d;

rule τ _ _ _ _ (ETT.der_sort _ $s _)
  ↪ ITT.u (τ_s $s)
with τ $Γ _ _ _ (ETT.der_prod _ $s $s' $A _ $dA $dB)
  ↪ ITT.P (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA)
           (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB)
with τ $Γ _ _ (ETT.tsort (ETT.smax $s $s')) (ETT.der_sigma _ $s $s' $A _ $dA $dB)
  ↪ ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA)
           (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB)
with τ $Γ _ _ (ETT.tsort $s) (ETT.der_prop_type_eq _ $s _ _ _ $dA $du $dv)
  ↪ let pu ≔ convert_T $Γ _ _ (I.inv_sort (τ_Γ $Γ) _ _ _ $du) $dA in
     let pv ≔ convert_T $Γ _ _ (I.inv_sort (τ_Γ $Γ) _ _ _ $dv) $dA in
     ITT.eq (τ_s $s) (τ_T $Γ _ _ $dA) (transport _ _ _ pu (τ $Γ _ _ _ $du)) (transport _ _ _ pv (τ $Γ _ _ _ $dv))
;

// Translation of type equality
symbol τ_eqT (Γ : TContext) (s : ETT.Sort) (T1 T2 : ETT.Term) (d : ETT.der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) T1 T2) :
  let d1 ≔ I.inv_eq_t1 (τ_Γ Γ) _ _ _ _ d in
  let d2 ≔ I.inv_eq_t2 (τ_Γ Γ) _ _ _ _ d in
  ε _ (ITT.eq _ (ITT.u (τ_s s)) (τ_T Γ T1 s d1) (τ_T Γ T2 s d2));
//   let d1 ≔ I.inv_eq_t1 (τ_Γ Γ) _ _ _ _ d in
//   let d2 ≔ I.inv_eq_t2 (τ_Γ Γ) _ _ _ _ d in
//   let heq ≔ τ_eq Γ (ETT.snext s) (ETT.tsort s) T1 T2 d in
//   heq_to_eq (ITT.snext (τ_s s)) (ITT.u (τ_s s)) (τ_T Γ T1 s d1) (τ_T Γ T2 s d2) heq;

// Translation of terms
rule τ $Γ _ _ _ (ETT.der_var _ $id $dΓ)
  ↪ let shift ≔ ETT.der_shift $id (τ_Γ $Γ) (tgetA $id $Γ) (ETT.tsort (tgetS $id $Γ)) (ETT.snext (tgetS $id $Γ)) in
     let p ≔ convert_T $Γ _ _ (shift (tgetD $id $Γ)) (shift (I.der_subΓ (τ_Γ $Γ) $id $dΓ)) in
     transport _ _ _ p (tgetShift $id $Γ)
with τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ $du $deq)
  ↪ let pAB ≔ τ_eqT $Γ _ _ _ $deq in
     let p ≔ convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) (I.inv_eq_t1 _ _ _ _ _ $deq) in
     transport _ _ _ pAB (transport _ _ _ p (τ $Γ _ _ _ $du))

with τ $Γ _ _ _ (ETT.der_abs _ $s _ $A _ _ $dA $dB $dt)
  ↪ λ a, let p ≔ convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort (ETT.Push $A $s (τ_Γ $Γ)) _ _ _ $dt) $dB in
          transport _ _ _ p (τ (TPush $Γ $s $A $dA a) _ _ _ $dt)
with τ $Γ _ _ _ (ETT.der_app _ $s $s' $A _ $u $B _ $dB $dt $du)
  ↪ let f ≔ τ_fun $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB (I.inv_sort (τ_Γ $Γ) _ _ _ $dt) (τ $Γ _ _ _ $dt) in
     τ_subst $Γ $s $s' $A $B $u $dB $du (f (τ $Γ _ _ _ $du))

with τ $Γ _ _ _ (ETT.der_pair _ $s $s' $u $A _ $B $dA $du $dB $dv)
  ↪ let pv ≔ convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du) in
     let p ≔ eq_pair (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (τ_T $Γ _ _ $dA)
                     (λ (a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
                     (λ (a : ε _ (τ_T $Γ _ _ $dA)), τ_T (TPush $Γ $s $A $dA a) _ _ $dB)
                     (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) $dA)
                     (λ (a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), convert_Γ $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dA a
                                                                                   (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) $dA) a) $dB) in
     transport _ (ITT.S _ _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
                 (ITT.S _ _ (τ_T $Γ _ _ $dA) (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB))
                 p
       (ITT.mkS (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
            (τ $Γ _ _ _ $du) (τ_subst' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ pv (τ $Γ _ _ _ $dv))))
with τ $Γ _ _ _ (ETT.der_π1 _ $s $s' _ $A $B $dA $dB $dp)
  ↪ let pr ≔ τ_sum $Γ $s $s' $A $B $dA $dB (I.inv_sort (τ_Γ $Γ) _ _ _ $dp) (τ $Γ _ _ _ $dp) in
     ITT.proj1 (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA) (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB) pr
with τ $Γ _ _ _ (ETT.der_refl _ $s _ _ $dA $du)
  ↪ let p ≔ convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) $dA in
     ITT.refl (τ_s $s) (τ_T $Γ _ _ $dA) (transport _ _ _ p (τ $Γ _ _ _ $du))
;


// der_π2 needs τ ... (der_π1 ...) to be defined to type
rule τ $Γ _ _ _ (ETT.der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ let pr ≔ τ_sum $Γ $s $s' $A $B $dA $dB (I.inv_sort (τ_Γ $Γ) _ _ _ $dp) (τ $Γ _ _ _ $dp) in
     τ_subst $Γ $s $s' $A $B (ETT.π1 $A $B $p) $dB
       (ETT.der_π1 (τ_Γ $Γ) $s $s' $p $A $B $dA $dB $dp)
       (ITT.proj2 (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA) (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB) pr)
;

// Translation of equality
