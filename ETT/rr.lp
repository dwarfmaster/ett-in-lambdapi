
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
symbol path_comp (s : ITT.Sort) (T U V : univ s) (p1 : ε _ (ITT.eq _ (ITT.u s) T U)) (p2 : ε _ (ITT.eq _ (ITT.u s) U V)) (t : ε _ T) :
  ε _ (ITT.eq s V
              (transport s T V (ITT.trans_eq p1 p2) t)
              (transport s U V p2 (transport s T U p1 t))) ≔
  ITT.J (ITT.snext s) s (ITT.u s) U
        (λ (V : univ s) p, ITT.eq s V (transport s T V (ITT.trans_eq p1 p) t) (transport s U V p (transport s T U p1 t)))
        (ITT.refl s U (transport s T U p1 t)) V p2;
symbol homotopy (s : ITT.Sort) (T U : univ s) (p1 p2 : ε _ (ITT.eq _ (ITT.u s) T U)) (p : ε _ (ITT.eq _ (ITT.eq _ (ITT.u s) T U) p1 p2)) (t : ε _ T) :
  ε _ (ITT.eq s U (transport _ _ _ p1 t) (transport _ _ _ p2 t)) ≔
  ITT.lift_eq (λ (p : ε _ (ITT.eq _ (ITT.u s) T U)), transport s T U p t) p1 p2 p;

symbol heterogeneous_eq' (s : ITT.Sort) (T U : univ s) (t : ε s T) (u : ε s U) : ITT.U _ ≔
  ITT.S _ _ (ITT.eq _ (ITT.u s) T U) (λ p, ITT.eq s U (transport s T U p t) u);
symbol heterogeneous_eq (s : ITT.Sort) (T U : univ s) (t : ε s T) (u : ε s U) : TYPE ≔
  ε _ (heterogeneous_eq' s T U t u);
symbol Pack' (s : ITT.Sort) (A1 A2 : univ s) : ITT.U _ ≔
  ITT.S _ _ A1 (λ x, ITT.S _ _ A2 (λ y, heterogeneous_eq' s A1 A2 x y));

symbol mkHeq {s : ITT.Sort} (T U : univ s) (t : ε s T) (u : ε s U) (p : ε _ (ITT.eq _ (ITT.u s) T U)) :
  (ε _ (ITT.eq s U (transport _ _ _ p t) u)) → heterogeneous_eq s T U t u ≔
  λ eq, ITT.mkS _ _ (ITT.eq _ (ITT.u s) T U) (λ p, ITT.eq s U (transport _ _ _ p t) u) p eq;
symbol getTeq {s : ITT.Sort} (T U : univ s) (t : ε s T) (u : ε s U) (heq : heterogeneous_eq s T U t u) : ε _ (ITT.eq _ (ITT.u s) T U) ≔
  ITT.proj1 _ _ (ITT.eq (ITT.snext s) (ITT.u s) T U) (λ p, ITT.eq s U (transport _ _ _ p t) u) heq;
symbol getEq {s : ITT.Sort} (T U : univ s) (t : ε s T) (u : ε s U) (heq : heterogeneous_eq s T U t u) :
  ε _ (ITT.eq s U (transport _ _ _ (getTeq T U t u heq) t) u) ≔
  ITT.proj2 _ _ (ITT.eq (ITT.snext s) (ITT.u s) T U) (λ p, ITT.eq s U (transport _ _ _ p t) u) heq;

symbol eq_to_heq {s : ITT.Sort} (T : univ s) (t u : ε s T) (p : ε _ (ITT.eq s T t u)) : heterogeneous_eq s T T t u ≔
  mkHeq T T t u (ITT.refl (ITT.snext s) (ITT.u s) T) p;
symbol heq_refl {s : ITT.Sort} (T : univ s) (t : ε s T) : heterogeneous_eq s T T t t ≔
  eq_to_heq T t t (ITT.refl s T t);
symbol heq_trans {s : ITT.Sort} (T U V : univ s) (t : ε s T) (u : ε s U) (v : ε s V)
                 (htu : heterogeneous_eq s T U t u) (huv : heterogeneous_eq s U V u v) : heterogeneous_eq s T V t v ≔
  mkHeq T V t v (ITT.trans_eq (getTeq T U t u htu) (getTeq U V u v huv))
        (ITT.trans_eq
          (path_comp s T U V (getTeq T U t u htu) (getTeq U V u v huv) t)
          (ITT.trans_eq (ITT.lift_eq (transport _ _ _ (getTeq U V u v huv)) (transport _ _ _ (getTeq T U t u htu) t) u (getEq T U t u htu)) (getEq U V u v huv)));
symbol heq_symm {s : ITT.Sort} (T U : univ s) (t : ε s T) (u : ε s U)
                (h : heterogeneous_eq s T U t u) : heterogeneous_eq s U T u t ≔
  mkHeq U T u t (ITT.inv_eq (getTeq T U t u h))
        (ITT.trans_eq
          (ITT.inv_eq (ITT.trans_eq
            (path_comp s T U T (getTeq T U t u h) (ITT.inv_eq (getTeq T U t u h)) t)
            (ITT.lift_eq (transport _ _ _ (ITT.inv_eq (getTeq T U t u h))) (transport _ _ _ (getTeq T U t u h) t) u (getEq T U t u h))))
          (homotopy s T T (ITT.trans_eq (getTeq T U t u h) (ITT.inv_eq (getTeq T U t u h))) (ITT.refl _ (ITT.u s) T) (ITT.eq_inverse (getTeq T U t u h)) t));
symbol lift_to_heq {s s' : ITT.Sort} {A : ITT.U s} {B : ε s A → ITT.U s'}
                   (f : ε _ (ITT.P s s' A B)) (u v : ε s A) (p : ε _ (ITT.eq s A u v))
                   : heterogeneous_eq s' (B u) (B v) (f u) (f v) ≔
  ITT.J s _ A u (λ v _, heterogeneous_eq' s' (B u) (B v) (f u) (f v)) (heq_refl (B u) (f u)) v p;

// Proved using uip
symbol heq_to_eq (s : ITT.Sort) (T : univ s) (t u : ε s T) : heterogeneous_eq s T T t u → ε s (ITT.eq s T t u);

// Extend heterogeneous equality with transports to the left and to the right
symbol heq_extend_R (s : ITT.Sort) (T U V : univ s) (t : ε s T) (v : ε s V)
                    (p : ε _ (ITT.eq _ (ITT.u s) V U))
                    (_ : heterogeneous_eq s T U t (transport _ _ _ p v)) :
                    heterogeneous_eq s T V t v;
symbol heq_extend_L (s : ITT.Sort) (T U V : univ s) (u : ε s U) (v : ε s V)
                    (p : ε _ (ITT.eq _ (ITT.u s) U T))
                    (_ : heterogeneous_eq s U V u v) :
                    heterogeneous_eq s T V (transport _ _ _ p u) v;
symbol heq_of_transport (s : ITT.Sort) (T U : univ s) (t : ε s T)
                        (p : ε _ (ITT.eq _ (ITT.u s) T U)) :
                        heterogeneous_eq s T U t (transport _ _ _ p t) ≔
  mkHeq T U t (transport _ _ _ p t) p (ITT.refl s U (transport _ _ _ p t));
symbol eq_of_transport (s : ITT.Sort) (T : univ s) (t : ε s T)
                       (p : ε _ (ITT.eq _ (ITT.u s) T T)) :
                       ε _ (ITT.eq s T t (transport _ _ _ p t)) ≔
  heq_to_eq s T t (transport _ _ _ p t) (heq_of_transport s T T t p);
symbol heq_funext (s s' : ITT.Sort) (A : ITT.U s) (B B' : ε s A → ITT.U s')
                  (f : ε _ (ITT.P s s' A B)) (g : ε _ (ITT.P s s' A B'))
                  (heq : Π a, heterogeneous_eq s' (B a) (B' a) (f a) (g a))
                  : heterogeneous_eq (ITT.smax s s') (ITT.P s s' A B) (ITT.P s s' A B') f g ≔
  ITT.J (ITT.smax s (ITT.snext s')) _ (ITT.P s (ITT.snext s') A (λ _, ITT.u s')) B
        (λ B' p, ITT.P (ITT.smax s s') _ (ITT.P s s' A B')
                       (λ g, ITT.P _ _ (ITT.P s _ A (λ a, ITT.eq s' (B' a) (transport _ _ _ (ITT.apply_eq p a) (f a)) (g a)))
                                   (λ _, heterogeneous_eq' (ITT.smax s s') (ITT.P s s' A B) (ITT.P s s' A B') f g)))
        (λ g eq, eq_to_heq (ITT.P s s' A B) f g (ITT.funext s s' A B f g eq))
        B'
        (ITT.funext s (ITT.snext s') A (λ _, ITT.u s') B B' (λ a, getTeq (B a) (B' a) (f a) (g a) (heq a))) // Equality of B and B'
        g
        (λ a, magic _ (ITT.eq s' (B' a) (transport _ _ _ (ITT.apply_eq (ITT.funext s (ITT.snext s') A (λ _, ITT.u s') B B' (λ a, getTeq (B a) (B' a) (f a) (g a) (heq a))) a) (f a)) (g a)));
        // (λ a, getEq (B a) (B' a) (f a) (g a) (heq a));

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
symbol τ_eq_type (Γ : TContext) (s : ETT.Sort) (T t1 t2 : ETT.Term) (d : ETT.der_eq (τ_Γ Γ) s T t1 t2) : ITT.U _ ≔
  let d1 ≔ I.inv_eq_t1 (τ_Γ Γ) s T t1 t2 d in
  let d2 ≔ I.inv_eq_t2 (τ_Γ Γ) s T t1 t2 d in
  let ds1 ≔ I.inv_sort (τ_Γ Γ) s t1 T d1 in
  let ds2 ≔ I.inv_sort (τ_Γ Γ) s t2 T d2 in
  heterogeneous_eq' (τ_s s)
    (τ_T Γ T s ds1)
    (τ_T Γ T s ds2)
    (τ Γ s t1 T d1) (τ Γ s t2 T d2);
symbol τ_eq (Γ : TContext) (s : ETT.Sort) (T t1 t2 : ETT.Term) (d : ETT.der_eq (τ_Γ Γ) s T t1 t2) : ε _ (τ_eq_type Γ s T t1 t2 d);
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
symbol τ_substT_eq (Γ : TContext) (s s' : ETT.Sort) (A B u : ETT.Term)
               (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (du : ETT.der (τ_Γ Γ) u A s) :
  ITT.ε _ (ITT.eq _ (ITT.u (τ_s s'))
    (τ_T (TPush Γ s A (I.inv_sort _ _ _ _ du) (τ Γ s u A du)) B s' dB)
    (τ_T Γ (ETT.apply1 B u) s' (I.substitution (τ_Γ Γ) s (ETT.snext s') A (ETT.tsort s') B dB u du)));
symbol τ_substT (Γ : TContext) (s s' : ETT.Sort) (A B u : ETT.Term)
               (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (du : ETT.der (τ_Γ Γ) u A s) ≔
  transport _ _ _ (τ_substT_eq Γ s s' A B u dB du);
symbol τ_substT' (Γ : TContext) (s s' : ETT.Sort) (A B u : ETT.Term)
               (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (du : ETT.der (τ_Γ Γ) u A s) ≔
  transport _ _ _ (ITT.inv_eq (τ_substT_eq Γ s s' A B u dB du));


symbol τ_subst_eq (Γ : TContext) (s s' : ETT.Sort) (A B t u : ETT.Term)
                  (dt : ETT.der (ETT.Push A s (τ_Γ Γ)) t B s')
                  (du : ETT.der (τ_Γ Γ) u A s) :
  heterogeneous_eq (τ_s s')
    (τ_T (TPush Γ s A (I.inv_sort _ _ _ _ du) (τ Γ s u A du)) _ _ (I.inv_sort _ _ _ _ dt))
    (τ_T Γ _ _ (I.inv_sort _ _ _ _ (I.substitution (τ_Γ Γ) s s' A B t dt u du)))
    (τ (TPush Γ s A (I.inv_sort _ _ _ _ du) (τ Γ s u A du)) s' t B dt)
    (τ Γ s' (ETT.apply1 t u) (ETT.apply1 B u) (I.substitution (τ_Γ Γ) s s' A B t dt u du));

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

// Translation of equality
symbol τ_equality_eq (Γ : TContext) (s : ETT.Sort) (A u v e : ETT.Term)
                     (de : ETT.der (τ_Γ Γ) e (ETT.teq A u v) s) :
  ε _ (ITT.eq _ (ITT.u (τ_s s))
                (τ_T Γ _ _ (I.inv_sort _ _ _ _ de))
                (ITT.eq (τ_s s) (τ_T Γ _ _ (I.inv_teq_sort _ _ _ _ _ _ de))
                    (transport _ _ _ (convert_T Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ de)) (I.inv_teq_sort _ _ _ _ _ _ de)) (τ Γ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ de)))
                    (transport _ _ _ (convert_T Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ de)) (I.inv_teq_sort _ _ _ _ _ _ de)) (τ Γ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ de)))));
symbol τ_equality (Γ : TContext) {s : ETT.Sort} {A u v e : ETT.Term}
                  (de : ETT.der (τ_Γ Γ) e (ETT.teq A u v) s) ≔
  transport _ _ _ (τ_equality_eq Γ s A u v e de);
symbol τ_equality' (Γ : TContext) {s : ETT.Sort} {A u v e : ETT.Term}
                   (de : ETT.der (τ_Γ Γ) e (ETT.teq A u v) s) ≔
  transport _ _ _ (ITT.inv_eq (τ_equality_eq Γ s A u v e de));

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
symbol eq_prod (s s' : ITT.Sort) (A A' : ITT.U s) (B : ε s A → ITT.U s') (B' : ε s A' → ITT.U s')
               (eqA : ε _ (ITT.eq (ITT.snext s) (ITT.u s) A A'))
               (eqB : Π(a : ε s A), ITT.ε _ (ITT.eq (ITT.snext s') (ITT.u s') (B a) (B' (transport _ _ _ eqA a))))
               : ε _ (ITT.eq (ITT.snext (ITT.smax s s')) (ITT.u (ITT.smax s s')) (ITT.P s s' A B) (ITT.P s s' A' B'));

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
  ε _ (ITT.eq _ (ITT.u (τ_s s)) (τ_T Γ T1 s d1) (τ_T Γ T2 s d2)) ≔
  let d1 ≔ I.inv_eq_t1 (τ_Γ Γ) _ _ _ _ d in
  let d2 ≔ I.inv_eq_t2 (τ_Γ Γ) _ _ _ _ d in
  let heq ≔ τ_eq Γ (ETT.snext s) (ETT.tsort s) T1 T2 d in
  heq_to_eq (ITT.snext (τ_s s)) (ITT.u (τ_s s)) (τ_T Γ T1 s d1) (τ_T Γ T2 s d2) heq;

// Translation of context conversion
symbol τ_conv_in_ctx (Γ : TContext) (s s' : ETT.Sort) (A A' t B : ETT.Term)
                     (deqA : ETT.der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A A')
                     (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) t B s')
                     (a : ε _ (τ Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ deqA)))
                     : heterogeneous_eq (τ_s s')
                        (τ_T (TPush Γ s A (I.inv_eq_t1 _ _ _ _ _ deqA) a) _ _ (I.inv_sort _ _ _ _ dB))
                        (τ_T (TPush Γ s A' (I.inv_eq_t2 _ _ _ _ _ deqA) (transport _ _ _ (τ_eqT Γ _ _ _ deqA) a)) _ _
                             (I.inv_sort _ _ _ _ (ETT.der_conv_in_ctx (τ_Γ Γ) s s' A A' t B deqA dB)))
                        (τ (TPush Γ s A (I.inv_eq_t1 _ _ _ _ _ deqA) a) _ _ _ dB)
                        (τ (TPush Γ s A' (I.inv_eq_t2 _ _ _ _ _ deqA) (transport _ _ _ (τ_eqT Γ _ _ _ deqA) a)) _ _ _
                           (ETT.der_conv_in_ctx (τ_Γ Γ) s s' A A' t B deqA dB));
symbol τ_convT_in_ctx (Γ : TContext) (s s' : ETT.Sort) (A A' B : ETT.Term)
                      (deqA : ETT.der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A A')
                      (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                      (a : ε _ (τ Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ deqA)))
                      : ε _ (ITT.eq (τ_s (ETT.snext s')) (ITT.u (τ_s s'))
                               (τ_T (TPush Γ s A (I.inv_eq_t1 _ _ _ _ _ deqA) a) _ _ dB)
                               (τ_T (TPush Γ s A' (I.inv_eq_t2 _ _ _ _ _ deqA) (transport _ _ _ (τ_eqT Γ _ _ _ deqA) a)) _ _
                                  (ETT.der_conv_in_ctx (τ_Γ Γ) s (ETT.snext s') A A' B (ETT.tsort s') deqA dB))) ≔
  heq_to_eq _ _ _ _ (τ_conv_in_ctx Γ s (ETT.snext s') A A' B (ETT.tsort s') deqA dB a);


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
     τ_substT $Γ $s $s' $A $B $u $dB $du (f (τ $Γ _ _ _ $du))

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
            (τ $Γ _ _ _ $du) (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ pv (τ $Γ _ _ _ $dv))))
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
     τ_substT $Γ $s $s' $A $B (ETT.π1 $A $B $p) $dB
       (ETT.der_π1 (τ_Γ $Γ) $s $s' $p $A $B $dA $dB $dp)
       (ITT.proj2 (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA) (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ $dB) pr)
;

// Translation of equality
// Computation
rule τ_eq $Γ _ _ _ _ (ETT.der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du)
  ↪ let IA : ITT.U (τ_s $s) ≔ τ_T $Γ $A $s (I.inv_sort _ _ _ _ $du) in
     heq_symm _ _ _ _ (heq_trans
       (τ_T $Γ (ETT.apply1 $B $u) $s' (I.inv_sort _ _ _ _ (I.substitution (τ_Γ $Γ) $s $s' $A $B $t $dt $u $du)))
       (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) $B $s' (I.inv_sort _ _ _ _ $dt))
       (τ_T $Γ (ETT.apply1 $B $u) $s' (I.substitution (τ_Γ $Γ) $s (ETT.snext $s') $A (ETT.tsort $s') $B (I.inv_sort _ _ _ _ $dt) $u $du))
       (τ $Γ _ _ _ (I.inv_eq_t2 _ _ _ _ _ (ETT.der_eq_beta (τ_Γ $Γ) $s $s' $u $A $t $B $dA $dB $dt $du)))
       (τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) _ _ _ $dt)
       (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_beta (τ_Γ $Γ) $s $s' $u $A $t $B $dA $dB $dt $du)))

       (heq_symm _ _ _ _ (τ_subst_eq $Γ $s $s' $A $B $t $u $dt $du))

       (heq_trans
         (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) $B $s' (I.inv_sort _ _ _ _ $dt))
         (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) $B $s' (I.inv_sort _ _ _ _ $dt))
         (τ_T $Γ (ETT.apply1 $B $u) $s' (I.substitution (τ_Γ $Γ) $s (ETT.snext $s') $A (ETT.tsort $s') $B (I.inv_sort _ _ _ _ $dt) $u $du))
         (τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) _ _ _ $dt)
         (τ_fun $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt))
                (τ $Γ _ _ _ (ETT.der_abs (τ_Γ $Γ) $s $s' $A $t $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) $dt))
                (τ $Γ _ _ _ $du))
         (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_beta (τ_Γ $Γ) $s $s' $u $A $t $B $dA $dB $dt $du)))

         (eq_to_heq _ _ _ (@ITT.lift_eq (ITT.smax (τ_s $s) (τ_s $s')) (τ_s $s')
           (ITT.P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ (I.inv_sort _ _ _ _ $dt)))
           (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) _ _ (I.inv_sort _ _ _ _ $dt))
           (λ(f : ε _ (ITT.P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ (I.inv_sort _ _ _ _ $dt)))), f (τ $Γ $s $u $A $du))
           (λ(a : ε _ IA), τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt)
           (τ_fun $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt))
             (τ $Γ _ _ _ (ETT.der_abs (τ_Γ $Γ) $s $s' $A $t $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) $dt)))
           (@ITT.trans_eq
             (ITT.smax (τ_s $s) (τ_s $s'))
             (ITT.P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ (I.inv_sort _ _ _ _ $dt)))
             (λ(a : ε _ IA), τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt)
             (λ(a : ε _ IA), transport _ _ _ (convert_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) $B $s' (I.inv_sort _ _ _ _ $dt) (I.inv_sort _ _ _ _ $dt))
                                             (τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt))
             (τ_fun $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt))
               (τ $Γ _ _ _ (ETT.der_abs (τ_Γ $Γ) $s $s' $A $t $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) $dt)))
             (ITT.funext (τ_s $s) (τ_s $s') IA
               (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ (I.inv_sort _ _ _ _ $dt))
               (λ(a : ε _ IA), τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt)
               (λ(a : ε _ IA), transport _ _ _ (convert_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) $B $s' (I.inv_sort _ _ _ _ $dt) (I.inv_sort _ _ _ _ $dt))
                                               (τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt))
               (λ(a : ε _ IA), eq_of_transport (τ_s $s') (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ (I.inv_sort _ _ _ _ $dt))
                                               (τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt)
                                               (convert_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) $B $s' (I.inv_sort _ _ _ _ $dt) (I.inv_sort _ _ _ _ $dt))))
             (eq_of_transport (ITT.smax (τ_s $s) (τ_s $s'))
              (ITT.P (τ_s $s) (τ_s $s') IA (λ(a : ε _ IA), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ (I.inv_sort _ _ _ _ $dt)))
              (λ(a : ε _ IA), transport _ _ _ (convert_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) $B $s' (I.inv_sort _ _ _ _ $dt) (I.inv_sort _ _ _ _ $dt))
                                              (τ (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ _ $dt))
              (τ_fun_eq $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt)))))))

         (heq_of_transport (τ_s $s')
           (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ $s $u $A $du)) $B $s' (I.inv_sort _ _ _ _ $dt))
           (τ_T $Γ (ETT.apply1 $B $u) $s' (I.substitution (τ_Γ $Γ) $s (ETT.snext $s') $A (ETT.tsort $s') $B (I.inv_sort _ _ _ _ $dt) $u $du))
           (τ_fun $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt))
                  (τ $Γ _ _ _ (ETT.der_abs (τ_Γ $Γ) $s $s' $A $t $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $dt) $dt))
                  (τ $Γ _ _ _ $du))
           (τ_substT_eq $Γ $s $s' $A $B $u (I.inv_sort _ _ _ _ $dt) $du))))

with τ_eq $Γ _ _ _ _ (ETT.der_eq_π1 _ $s $s' $u $A $v $B _ $du $dB $dv)
  ↪ eq_to_heq _ _ _
      (ITT.inv_eq
        (@ITT.lift_eq (ITT.smax (τ_s $s) (τ_s $s')) (τ_s $s)
          (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
          (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
          (λ(s : ε _ (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))), ITT.proj1 _ _ _ _ s)
          // u
          (ITT.mkS (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
              (λ(a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
              (τ $Γ _ _ _ $du)
              (τ_substT' $Γ $s $s' $A $B $u $dB $du
                (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))))
          // v
          (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
            (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
          // u = v
          (ITT.trans_eq
           (eq_of_transport (ITT.smax (τ_s $s) (τ_s $s'))
             (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
                    (λ(a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
             (ITT.mkS (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
              (λ(a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
              (τ $Γ _ _ _ $du)
              (τ_substT' $Γ $s $s' $A $B $u $dB $du
                (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))))
             (eq_pair (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
               (λ (a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
               (λ (a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
               (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $du))
               (λ (a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))),
                  convert_Γ $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $du) a
                            (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $du)) a) $dB)))
           (eq_of_transport (ITT.smax (τ_s $s) (τ_s $s'))
             (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
                    (λ(a : ε _ (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))), τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
             (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))
             (τ_sum_eq $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB))))))

with τ_eq $Γ _ _ _ _ (ETT.der_eq_π2 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ heq_symm
       (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $dv))
       (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv))))
       (τ $Γ _ _ _ $dv)
       (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv)))
       (heq_trans
         (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $dv))
         (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ _ _ _ $du)) _ _ $dB)
         (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv))))
         (τ $Γ _ _ _ $dv)
         (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv)))
         (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv)))

         // Equality from the translation of $v to the second projection of the untransported pair
         (heq_trans
           (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $dv))
           (τ_T $Γ _ _ (I.substitution _ _ _ _ _ _ $dB _ $du))
           (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ _ _ _ $du)) _ _ $dB)
           (τ $Γ _ _ _ $dv)
           (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))
           (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv)))
           (heq_of_transport _ _ _
             (τ $Γ _ _ _ $dv)
             (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)))
           (heq_of_transport _ _ _
             (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))
             (ITT.inv_eq (τ_substT_eq $Γ $s $s' $A $B $u $dB $du))))

         (heq_trans
           (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (τ $Γ _ _ _ $du)) _ _ $dB)
           (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du)
                       (ITT.proj1 _ _ _ _ (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                 (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                                                 (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))))
                _ _ $dB)
           (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv))))
           (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv)))
           (ITT.proj2 _ _ _ _ (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                                     (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                                     (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
           (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv)))

           // Equality between the projection of the pair and the transported pair
           (@lift_to_heq
             (ITT.smax (τ_s $s) (τ_s $s')) (τ_s $s')
             (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
             (λ p, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) (ITT.proj1 _ _ _ _ p)) _ _ $dB)
             (λ p, ITT.proj2 _ _ _ _ p)
             (ITT.mkS (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
                      (τ $Γ _ _ _ $du)
                      (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))))
             (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                    (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                    (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
             (heq_to_eq _ _ _ _
               (heq_trans
                 (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
                 (τ_T $Γ _ _ (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB))
                 (ITT.S (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB))
                 (ITT.mkS (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
                          (τ $Γ _ _ _ $du)
                          (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))))
                 (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))
                 (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                        (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                        (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
                 (heq_of_transport _ _ _
                   (ITT.mkS (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
                            (τ $Γ _ _ _ $du)
                            (τ_substT' $Γ $s $s' $A $B $u $dB $du (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $dv) (I.substitution _ _ _ _ _ _ $dB _ $du)) (τ $Γ _ _ _ $dv))))
                   (eq_pair (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du))
                     (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
                     (λ a, τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du) a) _ _ $dB)
                     (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $du))
                     (λ a, convert_Γ $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $du) a
                                     (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ $du) (I.inv_sort _ _ _ _ $du)) a) $dB)))
                 (heq_of_transport _ _ _
                   (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))
                   (τ_sum_eq $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                     (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB))))))

           // Equality between the projection of the transported pair and the converted second element
           (heq_trans
             (τ_T (TPush $Γ $s $A (I.inv_sort _ _ _ _ $du)
                         (ITT.proj1 _ _ _ _ (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                   (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                                                   (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))))
                  _ _ $dB)
             (τ_T $Γ _ _ (I.substitution _ _ _ _ _ _ $dB _ (ETT.der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                              (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
             (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv))))
             (ITT.proj2 _ _ _ _ (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                                       (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                                       (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
             (τ $Γ _ _ _ (ETT.der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                     (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
             (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv)))
             // Substitution
             (heq_of_transport _ _ _
               (ITT.proj2 _ _ _ _ (τ_sum $Γ $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB
                                         (ETT.der_sigma (τ_Γ $Γ) $s $s' $A $B (I.inv_sort _ _ _ _ $du) $dB)
                                         (τ $Γ _ _ _ (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
               (τ_substT_eq $Γ $s $s' $A $B (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $dB
                 (ETT.der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                             (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
             // Type conversion
             (heq_trans
               (τ_T $Γ _ _ (I.substitution _ _ _ _ _ _ $dB _ (ETT.der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                                (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
               (τ_T $Γ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                                    (ETT.der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv) $dB)))
               (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv))))
               (τ $Γ _ _ _ (ETT.der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                       (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
               (transport _ _ _
                 (convert_T $Γ _ _
                   (I.substitution _ _ _ _ _ _ $dB _ (ETT.der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                       (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
                   (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                             (ETT.der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv) $dB)))
                 (τ $Γ _ _ _ (ETT.der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                         (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
               (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_π2 (τ_Γ $Γ) $s $s' $u $A $v $B $dA $du $dB $dv)))

               (heq_of_transport _ _ _
                 (τ $Γ _ _ _ (ETT.der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
                 (convert_T $Γ _ _
                   (I.substitution _ _ _ _ _ _ $dB _ (ETT.der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                       (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
                   (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                             (ETT.der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv) $dB))))
               (heq_of_transport _ _ _
                 (transport _ _ _
                   (convert_T $Γ _ _
                     (I.substitution _ _ _ _ _ _ $dB _ (ETT.der_π1 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                                         (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv)))
                     (I.inv_eq_t1 _ _ _ _ _ (ETT.der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                               (ETT.der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv) $dB)))
                   (τ $Γ _ _ _ (ETT.der_π2 (τ_Γ $Γ) $s $s' (ETT.tpair $A $B $u $v) $A $B (I.inv_sort _ _ _ _ $du) $dB
                                           (ETT.der_pair (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv))))
                 (τ_eqT $Γ _ _ _
                        (ETT.der_eq_ctx (τ_Γ $Γ) $s (ETT.snext $s') $B (ETT.tsort $s') (ETT.π1 $A $B (ETT.tpair $A $B $u $v)) $u $A
                                    (ETT.der_eq_π1 (τ_Γ $Γ) $s $s' $u $A $v $B (I.inv_sort _ _ _ _ $du) $du $dB $dv) $dB)))))))

// Conversion
// rule τ_eq $Γ _ _ _ _ (ETT.der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deq $deqT)
//   ↪ mkHeq
//        (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqT))
//        (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqT))
//        (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq) $deqT))
//        (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq) $deqT))
//        (ITT.trans_eq (ITT.trans_eq (ITT.inv_eq (τ_eqT $Γ _ _ _ $deqT)) (ITT.inv_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT))))
//                      (ITT.trans_eq (getTeq _ _ _ _ (τ_eq $Γ _ _ _ _ $deq))
//                                    (ITT.trans_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT)) (τ_eqT $Γ _ _ _ $deqT))))
//        (magic _
//          (ITT.eq _ (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqT))
//            (transport _ _ _ (ITT.trans_eq (ITT.trans_eq (ITT.inv_eq (τ_eqT $Γ _ _ _ $deqT)) (ITT.inv_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT))))
//                                           (ITT.trans_eq (getTeq _ _ _ _ (τ_eq $Γ _ _ _ _ $deq))
//                                                         (ITT.trans_eq (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq)) (I.inv_eq_t1 _ _ _ _ _ $deqT)) (τ_eqT $Γ _ _ _ $deqT))))
//               (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $deq) $deqT)))
//            (τ $Γ _ _ _ (ETT.der_type_conv _ _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $deq) $deqT))))

with τ_eq $Γ _ _ _ _ (ETT.der_eq_lift _ $s _ _ _ _ $de)
  ↪ let heq ≔ mkHeq (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ $de))) (τ_T $Γ _ _ (I.inv_teq_sort _ _ _ _ _ _ $de))
                     (τ $Γ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ $de))
                     (transport _ _ _ (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ $de)) (I.inv_teq_sort _ _ _ _ _ _ $de)) (τ $Γ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ $de)))
                     (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ $de)) (I.inv_teq_sort _ _ _ _ _ _ $de))
                     (τ_equality $Γ $de (τ $Γ _ _ _ $de)) in
     heq_extend_R (τ_s $s)
       (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ $de)))
       (τ_T $Γ _ _ (I.inv_teq_sort _ _ _ _ _ _ $de))
       (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ $de)))
       (τ $Γ _ _ _ (I.inv_teq_t1 _ _ _ _ _ _ $de))
       (τ $Γ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ $de))
       (convert_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_teq_t2 _ _ _ _ _ _ $de)) (I.inv_teq_sort _ _ _ _ _ _ $de)) heq

// Congruence
with τ_eq $Γ _ _ _ _ (ETT.der_eq_refl _ _ _ _ $du)
  ↪ heq_refl (τ_T $Γ _ _ (I.inv_sort _ _ _ _ $du)) (τ $Γ _ _ _ $du)
with τ_eq $Γ _ _ _ _ (ETT.der_eq_trans _ $s _ $v _ $A $duv $dvw)
  ↪ heq_trans
         (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $duv)))
         (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $dvw)))
         (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $dvw)))
         (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $duv))
         (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $dvw))
         (τ $Γ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $dvw))
       (heq_trans
            (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $duv)))
            (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $duv)))
            (τ_T $Γ _ _ (I.inv_sort _ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $dvw)))
            (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $duv))
            (τ $Γ _ _ _ (I.inv_eq_t2 _ _ _ _ _ $duv))
            (τ $Γ _ _ _ (I.inv_eq_t1 _ _ _ _ _ $dvw))
          (τ_eq $Γ _ _ _ _ $duv)
          (convert $Γ $s $v $A (I.inv_eq_t2 _ _ _ _ _ $duv) (I.inv_eq_t1 _ _ _ _ _ $dvw)))
       (τ_eq $Γ _ _ _ _ $dvw)
with τ_eq $Γ _ _ _ _ (ETT.der_eq_symm _ _ _ _ _ $duv)
  ↪ heq_symm _ _ _ _ (τ_eq $Γ _ _ _ _ $duv)

// Context
// prod
with τ_eq $Γ _ _ _ _ (ETT.der_eq_ctx_prod_domain _ $s $s' $A $A' $B $deqA $dB)
  ↪ eq_to_heq _ _ _ (eq_prod (τ_s $s) (τ_s $s') (τ_T $Γ _ _ (I.inv_eq_t1 _ _ _ _ _ $deqA)) (τ_T $Γ _ _ (I.inv_eq_t2 _ _ _ _ _ $deqA))
            (λ a, τ_T (TPush $Γ $s $A (I.inv_eq_t1 _ _ _ _ _ $deqA) a) _ _ $dB)
            (λ a, τ_T (TPush $Γ $s $A' (I.inv_eq_t2 _ _ _ _ _ $deqA) a) _ _ (ETT.der_conv_in_ctx (τ_Γ $Γ) $s (ETT.snext $s') $A $A' $B (ETT.tsort $s') $deqA $dB))
            (τ_eqT $Γ _ _ _ $deqA)
            (λ a, τ_convT_in_ctx $Γ $s $s' $A $A' $B $deqA $dB a))
with τ_eq $Γ _ _ _ _ (ETT.der_eq_ctx_prod_codomain _ $s $s' $A _ _ $dA $deqB)
  ↪ eq_to_heq _ _ _ (eq_prod (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA) (τ_T $Γ _ _ $dA)
            (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t1 _ _ _ _ _ $deqB))
            (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB))
            (ITT.refl (ITT.snext (τ_s $s)) (ITT.u (τ_s $s)) (τ_T $Γ _ _ $dA))
            (λ a, τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB))
// tabs
with τ_eq $Γ _ _ _ _ (ETT.der_eq_ctx_tabs_domain _ $s $s' $A $A' $B $t $deqA $dB $dt)
  ↪ magic _ (τ_eq_type $Γ _ _ _ _ (ETT.der_eq_ctx_tabs_domain (τ_Γ $Γ) $s $s' $A $A' $B $t $deqA $dB $dt))
with τ_eq $Γ _ _ _ _ (ETT.der_eq_ctx_tabs_codomain _ $s $s' $A $B $B' $t $dA $deqB $dt)
  ↪ heq_trans
       (τ_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B  $dA (I.inv_eq_t1 _ _ _ _ _ $deqB)))
       (τ_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)))
       (τ_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B  $dA (I.inv_eq_t1 _ _ _ _ _ $deqB)))
       (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB)) (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))
       (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                                     (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                                     (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                                     (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))))
       (τ $Γ _ _ _ (I.inv_eq_t2 _ _ _ _ _ (ETT.der_eq_ctx_tabs_codomain (τ_Γ $Γ) $s $s' $A $B $B' $t $dA $deqB $dt)))
       (heq_funext (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA)
         (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t1 _ _ _ _ _ $deqB))
         (λ a, τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB))
         (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB)) (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))
         (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                                       (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                                       (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                                       (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))))
         (λ a, heq_trans
           (τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t1 _ _ _ _ _ $deqB))
           (τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB))
           (τ_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB))
           (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB)) (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))
           (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                            (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                            (τ (TPush $Γ $s $A $dA a) _ _ _ $dt)))
           (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                            (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                            (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                            (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))))
           (heq_of_transport _ _ _
             (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB)) (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))
             (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB))
           (heq_of_transport _ _ _
             (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                              (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                              (τ (TPush $Γ $s $A $dA a) _ _ _ $dt)))
             (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB)))))
       (heq_trans
         (τ_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)))
         (τ_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)))
         (τ_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B  $dA (I.inv_eq_t1 _ _ _ _ _ $deqB)))
         (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                                       (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                                       (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                                       (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))))
         (transport _ _ _ (convert_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)))
           (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                                         (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                                         (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                                         (τ (TPush $Γ $s $A $dA a) _ _ _ $dt)))))
         (τ $Γ _ _ _ (I.inv_eq_t2 _ _ _ _ _ (ETT.der_eq_ctx_tabs_codomain (τ_Γ $Γ) $s $s' $A $B $B' $t $dA $deqB $dt)))
         (heq_of_transport _ _ _
           (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                                         (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                                         (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                                         (τ (TPush $Γ $s $A $dA a) _ _ _ $dt))))
           (convert_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB))))
         (heq_of_transport _ _ _
           (transport _ _ _ (convert_T $Γ _ _ (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)) (ETT.der_prod (τ_Γ $Γ) $s $s' $A $B' $dA (I.inv_eq_t2 _ _ _ _ _ $deqB)))
             (λ(a : ε _ (τ_T $Γ _ _ $dA)), transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_eq_t2 _ _ _ _ _ $deqB) (I.inv_eq_t2 _ _ _ _ _ $deqB))
                                           (transport _ _ _ (τ_eqT (TPush $Γ $s $A $dA a) _ _ _ $deqB)
                                           (transport _ _ _ (convert_T (TPush $Γ $s $A $dA a) _ _ (I.inv_sort _ _ _ _ $dt) (I.inv_eq_t1 _ _ _ _ _ $deqB))
                                           (τ (TPush $Γ $s $A $dA a) _ _ _ $dt)))))
           (τ_eqT $Γ _ _ _ (ETT.der_eq_symm (τ_Γ $Γ) (ETT.snext (ETT.smax $s $s')) (ETT.tfun $A $B) (ETT.tfun $A $B') (ETT.tsort (ETT.smax $s $s'))
                             (ETT.der_eq_ctx_prod_codomain (τ_Γ $Γ) $s $s' $A $B $B' $dA $deqB)))))
;

// convert_T
rule convert_T $Γ $T $s $d1 $d2
  ↪ heq_to_eq _ _ _ _ (convert $Γ (ETT.snext $s) $T (ETT.tsort $s) $d1 $d2);

// convert
rule convert _ _ _ _ (ETT.der_sort _ $s _) (ETT.der_sort _ _ _)
  ↪ heq_refl (ITT.u (ITT.snext (τ_s $s))) (ITT.u (τ_s $s))
;
