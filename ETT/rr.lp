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
// TODO this is false ! It is only true if a1 d1~d2 a2
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

// Equalities
symbol eq_pair (s s' : ITT.Sort) (A A' : ITT.U s) (B : ITT.ε s A → ITT.U s') (B' : ITT.ε s A' → ITT.U s')
               (eqA : ε _ (ITT.eq (ITT.snext s) (ITT.u s) A A'))
               (eqB : Π(a : ε s A), ITT.ε _ (ITT.eq (ITT.snext s') (ITT.u s') (B a) (B' (transport _ _ _ eqA a)))) :
               ITT.ε _ (ITT.eq (ITT.snext (ITT.smax s s')) (ITT.u (ITT.smax s s')) (ITT.S s s' A B) (ITT.S s s' A' B'));
symbol eq_prod (s s' : ITT.Sort) (A A' : ITT.U s) (B : ε s A → ITT.U s') (B' : ε s A' → ITT.U s')
               (eqA : ε _ (ITT.eq (ITT.snext s) (ITT.u s) A A'))
               (eqB : Π(a : ε s A), ITT.ε _ (ITT.eq (ITT.snext s') (ITT.u s') (B a) (B' (transport _ _ _ eqA a))))
               : ε _ (ITT.eq (ITT.snext (ITT.smax s s')) (ITT.u (ITT.smax s s')) (ITT.P s s' A B) (ITT.P s s' A' B'));

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

symbol τ_transport_in_ctx (Γ : TContext) (s s' : ETT.Sort) (A B t : ETT.Term)
                          (dA dA' : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                          (dt : ETT.der (ETT.Push A s (τ_Γ Γ)) t B s')
                          (p : ε _ (ITT.eq _ (ITT.u (τ_s s)) (τ_T Γ _ _ dA) (τ_T Γ _ _ dA')))
                          (a : ε _ (τ_T Γ _ _ dA))
                          : heterogeneous_eq (τ_s s')
                              (τ_T (TPush Γ s A dA a) _ _ (I.inv_sort _ _ _ _ dt))
                              (τ_T (TPush Γ s A dA' (transport _ _ _ p a)) _ _ (I.inv_sort _ _ _ _ dt))
                              (τ (TPush Γ s A dA a) _ _ _ dt)
                              (τ (TPush Γ s A dA' (transport _ _ _ p a)) _ _ _ dt);
symbol τ_T_transport_in_ctx (Γ : TContext) (s s' : ETT.Sort) (A B : ETT.Term)
                            (dA dA' : ETT.der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                            (dB : ETT.der (ETT.Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                            (p : ε _ (ITT.eq _ (ITT.u (τ_s s)) (τ_T Γ _ _ dA) (τ_T Γ _ _ dA')))
                            (a : ε _ (τ_T Γ _ _ dA))
                            : ε _ (ITT.eq _ (ITT.u (τ_s s'))
                                (τ_T (TPush Γ s A dA a) _ _ dB)
                                (τ_T (TPush Γ s A dA' (transport _ _ _ p a)) _ _ dB)) ≔
  heq_to_eq _ _ _ _ (τ_transport_in_ctx Γ s (ETT.snext s') A (ETT.tsort s') B dA dA' dB p a);


// Invariance of translation by extension
symbol τ_extend_context (Γ1 Γ2 : TContext) (s : ETT.Sort) (t T : ETT.Term)
                        (dt : ETT.der (τ_Γ Γ2) t T s)
                        : heterogeneous_eq (τ_s s)
                            (τ_T Γ2 _ _ (I.inv_sort _ _ _ _ dt))
                            (τ_T (Extend Γ1 Γ2) _ _ (I.inv_sort _ _ _ _ (ETT.der_extend_context _ _ s t T (well_formed_tcontext Γ1) dt)))
                            (τ Γ2 _ _ _ dt)
                            (τ (Extend Γ1 Γ2) _ _ _ (ETT.der_extend_context _ _ s t T (well_formed_tcontext Γ1) dt));
symbol τ_T_extend_context (Γ1 Γ2 : TContext) (s : ETT.Sort) (T : ETT.Term)
                          (dT : ETT.der (τ_Γ Γ2) T (ETT.tsort s) (ETT.snext s))
                          : ε _ (ITT.eq _ (ITT.u (τ_s s))
                                (τ_T Γ2 _ _ dT)
                                (τ_T (Extend Γ1 Γ2) _ _ (ETT.der_extend_context _ _ (ETT.snext s) T (ETT.tsort s) (well_formed_tcontext Γ1) dT))) ≔
  heq_to_eq _ _ _ _ (τ_extend_context Γ1 Γ2 (ETT.snext s) T (ETT.tsort s) dT);

// Implementation of extension
rule Extend $Γ1 (TPush $Γ2 $s $A $dA $a)
  ↪ TPush (Extend $Γ1 $Γ2) $s $A
           (ETT.der_extend_context _ _ (ETT.snext $s) $A (ETT.tsort $s) (well_formed_tcontext $Γ1) $dA)
           (transport _ _ _ (τ_T_extend_context $Γ1 $Γ2 $s $A $dA) $a)
with Extend $Γ1 TEmpty ↪ $Γ1;

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
with convert $Γ _ _ _ (ETT.der_prod _ $s $s' $A $B $dA $dB) (ETT.der_prod _ $s $s' $A $B $dA' $dB')
  ↪ eq_to_heq _ _ _ (eq_prod (τ_s $s) (τ_s $s') (τ_T $Γ _ _ $dA) (τ_T $Γ _ _ $dA')
       (λ a, τ_T (TPush $Γ $s $A $dA  a) _ _ $dB)
       (λ a, τ_T (TPush $Γ $s $A $dA' a) _ _ $dB')
       (convert_T $Γ $A $s $dA $dA')
       (λ a, (@ITT.trans_eq _
         (ITT.u (τ_s $s'))
         (τ_T (TPush $Γ $s $A $dA a) _ _ $dB)
         (τ_T (TPush $Γ $s $A $dA' (transport _ _ _ (convert_T $Γ $A $s $dA $dA') a)) _ _ $dB)
         (τ_T (TPush $Γ $s $A $dA' (transport _ _ _ (convert_T $Γ $A $s $dA $dA') a)) _ _ $dB')
         (τ_T_transport_in_ctx $Γ $s $s' $A $B $dA $dA' $dB (convert_T $Γ $A $s $dA $dA') a)
         (convert_T (TPush $Γ $s $A $dA' (transport _ _ _ (convert_T $Γ $A $s $dA $dA') a)) $B $s' $dB $dB'))))
// with convert $Γ _ _ _ (ETT.der_abs _ $s $s' $A $t $B $dA $dB $dt) (ETT.der_abs _ $s $s' $A $t $B $dA' $dB' $dt')
//   ↪
;
