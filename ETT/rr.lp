
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
with τ_s (ETT.snext $s) ↪ ITT.snext (τ_s $s);

// Translation declaration
symbol τ_T (T : ETT.Term) (s : ETT.Sort) : ETT.der T (ETT.tsort s) (ETT.snext s) → univ (τ_s s);
symbol τ (s : ETT.Sort) (t T : ETT.Term) (d : ETT.der t T s) :
  ε (τ_s s) (τ_T T s (I.inv_sort s t T d));
symbol τ_eq (s : ETT.Sort) (T t1 t2 : ETT.Term) (d : ETT.der_eq s T t1 t2) :
  let d1 ≔ I.inv_eq_t1 s T t1 t2 d in
  let d2 ≔ I.inv_eq_t2 s T t1 t2 d in
  heterogeneous_eq (τ_s s)
    (τ_T T s (I.inv_sort s t1 T d1))
    (τ_T T s (I.inv_sort s t2 T d2))
    (τ s t1 T d1) (τ s t2 T d2);

// Translation of type
rule τ_T _ _ (ETT.der_sort $s) ↪ ITT.u (τ_s $s);
rule τ_T _ _ (ETT.der_prod $s $s' $A $B $dA $dB) ↪ ITT.P (τ_s $s) (τ_s $s') (τ_T _ _ $dA)
                                                         (λ a, ?);
