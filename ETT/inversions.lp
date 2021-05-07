
require open ETT.main;
require ETT.itt as ITT;
symbol U : TYPE ≔ ITT.U ITT.s0;

// Lemmas
symbol substitution (Γ : Context) (s s' : Sort) (A B : Term) (C : Term) :
  der (Push A s Γ) C B s' → Π(u : Term), der Γ u A s → der Γ (apply1 C u) (apply1 B u) s';
symbol inv_context : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(_ : der Γ t T s), der_context Γ;
symbol inv_eq_context : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(_ : der_eq Γ s T t1 t2), der_context Γ;
symbol inv_sort : Π(Γ : Context), Π(s : Sort), Π(t T : Term), Π(_ : der Γ t T s), der Γ T (tsort s) (snext s);
symbol inv_eq_sort : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), Π(_ : der_eq Γ s T t1 t2), der Γ T (tsort s) (snext s);
symbol inv_eq_t2 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t2 T s;
symbol inv_eq_t1 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 : Term), der_eq Γ s T t1 t2 → der Γ t1 T s;

symbol inv_teq_sort : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 e : Term), Π(_ : der Γ e (teq T t1 t2) s), der Γ T (tsort s) (snext s);
symbol inv_teq_t1 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 e : Term), Π(_ : der Γ e (teq T t1 t2) s), der Γ t1 T s;
symbol inv_teq_t2 : Π(Γ : Context), Π(s : Sort), Π(T t1 t2 e : Term), Π(_ : der Γ e (teq T t1 t2) s), der Γ t2 T s;

symbol inv_type : Π(Γ : Context), Π(s s' : Sort), Π(A : Term), der Γ A (tsort s) s' → der Γ A (tsort s) (snext s);
symbol inv_eq_type : Π(Γ : Context), Π(s s' : Sort), Π(s1 s2 : Sort), der_eq Γ s' (tsort s) (tsort s1) (tsort s2) →
  der_eq Γ (snext (snext s1)) (tsort (snext s1)) (tsort s1) (tsort s1);

// Helpers
symbol der_subΓ (Γ : Context) (id : DBId) (_ : der_context Γ): der (getΓ Γ id) (get Γ id) (tsort (getS Γ id)) (snext (getS Γ id));
rule der_subΓ _ db0 (der_context_push _ _ _ $dA _) ↪ $dA
with der_subΓ _ (dbsucc $id) (der_context_push _ _ _ _ $dt) ↪ der_subΓ _ $id $dt;

symbol pushΓ {Γ : Context} {s : Sort} {T : Term} (d : der Γ T (tsort s) (snext s)) : der_context (Push T s Γ) ≔
  der_context_push Γ s T d (inv_context _ _ _ _ d);


// Definition of inv_sort
rule inv_sort _ _ _ _ (der_var $Γ $id $dΓ) ↪ der_shift $id $Γ _ _ _ (der_subΓ _ $id $dΓ)
with inv_sort _ _ _ _ (der_type_conv _ _ _ _ _ _ $deq) ↪ inv_eq_t2 _ _ _ _ _ $deq
with inv_sort _ _ _ _ (der_abs $Γ $s $s' $A _ $B $dA $dB _) ↪ der_prod $Γ $s $s' $A $B $dA $dB
with inv_sort _ _ _ _ (der_app $Γ $s $s' $A _ $u $B _ $dB _ $du) ↪ substitution $Γ $s (snext $s') $A (tsort $s') $B $dB $u $du
with inv_sort _ _ _ _ (der_pair $Γ $s $s' _ $A _ $B $dA _ $dB _) ↪ der_sigma $Γ $s $s' $A $B $dA $dB
with inv_sort _ _ _ _ (der_π1 _ _ _ _ _ _ $dA _ _) ↪ $dA
with inv_sort _ _ _ _ (der_π2 $Γ $s $s' $p $A $B $dA $dB $dp) ↪ substitution $Γ $s (snext $s') $A (tsort $s') $B $dB (π1 $A $B $p)
                                                                              (der_π1 $Γ $s $s' $p $A $B $dA $dB $dp)
with inv_sort _ _ _ _ (der_refl $Γ $s $u $A $dA $du) ↪ der_prop_type_eq $Γ $s $A $u $u $dA $du $du
with inv_sort _ _ _ _ (der_uip $Γ $s $e1 $e2 $u $v $A $de1 $de2) ↪ der_prop_type_eq $Γ $s (teq $A $u $v) $e1 $e2
                                                                                     (inv_sort _ _ _ _ $de1) $de1 $de2
with inv_sort _ _ _ _ (der_funext $Γ $s $s' $f $g $A _ $B $dA $dB $df $dg _)
  ↪ der_prop_type_eq $Γ (smax $s $s') (tfun $A $B) $f $g (der_prod $Γ $s $s' $A $B $dA $dB) $df $dg
;

// Definition of inv_eq*
// Computation
rule inv_eq_sort _ _ _ _ _ (der_eq_beta $Γ $s $s' $u $A _  $B _ _ $dt $du) ↪ substitution $Γ $s (snext $s') $A (tsort $s') $B (inv_sort _ _ _ _ $dt) $u $du
with inv_eq_t1   _ _ _ _ _ (der_eq_beta $Γ $s $s' $u $A $t $B _ _ $dt $du) ↪ der_app $Γ $s $s' $A (tabs $A $B $t) $u $B (inv_sort _ _ _ _ $du) (inv_sort _ _ _ _ $dt)
                                                                                      (der_abs $Γ $s $s' $A $t $B (inv_sort _ _ _ _ $du) (inv_sort _ _ _ _ $dt) $dt) $du
with inv_eq_t2   _ _ _ _ _ (der_eq_beta $Γ $s $s' $u $A $t $B _ _ $dt $du) ↪ substitution $Γ $s $s' $A $B $t $dt $u $du
with inv_eq_sort _ _ _ _ _ (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ inv_sort _ _ _ _ $du
with inv_eq_t1   _ _ _ _ _ (der_eq_π1 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_π1 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort _ _ _ _ $du) $dB
                                                                                     (der_pair $Γ $s $s' $u $A $v $B (inv_sort _ _ _ _ $du) $du $dB $dv)
with inv_eq_t2   _ _ _ _ _ (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ $du
with inv_eq_sort _ _ _ _ _ (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ inv_sort _ _ _ _ $dv
with inv_eq_t1   _ _ _ _ _ (der_eq_π2 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_type_conv $Γ (π2 $A $B (tpair $A $B $u $v)) (apply1 $B (π1 $A $B (tpair $A $B $u $v))) (apply1 $B $u) $s'
                                                                                  (der_π2 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort _ _ _ _ $du) $dB
                                                                                    (der_pair $Γ $s $s' $u $A $v $B (inv_sort _ _ _ _ $du) $du $dB $dv))
                                                                                  (der_eq_ctx $Γ $s (snext $s') $B (tsort $s') (π1 $A $B (tpair $A $B $u $v)) $u $A
                                                                                    (der_eq_π1 $Γ $s $s' $u $A $v $B (inv_sort _ _ _ _ $du) $du $dB $dv) $dB)
with inv_eq_t2   _ _ _ _ _ (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ $dv
// Conversion
with inv_eq_sort _ _ _ _ _ (der_eq_conversion _ _ _ _ _ _ _ $deqT) ↪ inv_eq_t2 _ _ _ _ _ $deqT
with inv_eq_t1   _ _ _ _ _ (der_eq_conversion $Γ $s $t1 _ $T1 $T2 $deq $deqT) ↪ der_type_conv $Γ $t1 $T1 $T2 $s (inv_eq_t1 _ _ _ _ _ $deq) $deqT
with inv_eq_t2   _ _ _ _ _ (der_eq_conversion $Γ $s _ $t2 $T1 $T2 $deq $deqT) ↪ der_type_conv $Γ $t2 $T1 $T2 $s (inv_eq_t2 _ _ _ _ _ $deq) $deqT
with inv_eq_sort _ _ _ _ _ (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_sort _ _ _ _ _ _ $de
with inv_eq_t1   _ _ _ _ _ (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_t1   _ _ _ _ _ _ $de
with inv_eq_t2   _ _ _ _ _ (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_t2   _ _ _ _ _ _ $de
// Congruence
with inv_eq_sort _ _ _ _ _ (der_eq_refl _ _ _ _ $du) ↪ inv_sort _ _ _ _ $du
with inv_eq_t1   _ _ _ _ _ (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_t2   _ _ _ _ _ (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_sort _ _ _ _ _ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_sort _ _ _ _ _ $duv
with inv_eq_t1   _ _ _ _ _ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_t1   _ _ _ _ _ $duv
with inv_eq_t2   _ _ _ _ _ (der_eq_trans _ _ _ _ _ _ _ $dvw) ↪ inv_eq_t2   _ _ _ _ _ $dvw
with inv_eq_sort _ _ _ _ _ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_sort _ _ _ _ _ $duv
with inv_eq_t1   _ _ _ _ _ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t2   _ _ _ _ _ $duv
with inv_eq_t2   _ _ _ _ _ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t1  _ _ _ _ _ $duv
// Context
// prod
with inv_eq_sort _ _ _ _ _ (der_eq_ctx_prod_domain $Γ $s $s' _  _   _  $deqA _  )
  ↪ der_sort $Γ (smax $s $s') (inv_eq_context $Γ _ _ _ _ $deqA)
with inv_eq_t1   _ _ _ _ _ (der_eq_ctx_prod_domain $Γ $s $s' $A _   $B $deqA $dB)
  ↪ der_prod $Γ $s $s' $A $B (inv_eq_t1 _ _ _ _ _ $deqA) $dB
with inv_eq_t2   _ _ _ _ _ (der_eq_ctx_prod_domain $Γ $s $s' $A $A' $B $deqA $dB)
  ↪ der_prod $Γ $s $s' $A' $B (inv_eq_t2 _ _ _ _ _ $deqA)
              (der_conv_in_ctx $Γ $s (snext $s') $A $A' $B (tsort $s') $deqA $dB)
with inv_eq_sort _ _ _ _ _ (der_eq_ctx_prod_codomain $Γ $s $s' _  _  _   $dA _    )
  ↪ der_sort $Γ (smax $s $s') (inv_context $Γ _ _ _ $dA)
with inv_eq_t1   _ _ _ _ _ (der_eq_ctx_prod_codomain $Γ $s $s' $A $B _   $dA $deqB)
  ↪ der_prod $Γ $s $s' $A $B  $dA (inv_eq_t1 _ _ _ _ _ $deqB)
with inv_eq_t2   _ _ _ _ _ (der_eq_ctx_prod_codomain $Γ $s $s' $A _  $B' $dA $deqB)
  ↪ der_prod $Γ $s $s' $A $B' $dA (inv_eq_t2 _ _ _ _ _ $deqB)
// abs
with inv_eq_sort _ _ _ _ _ (der_eq_ctx_tabs_domain $Γ $s $s' $A _   $B _  $deqA $dB _  )
  ↪ der_prod $Γ $s $s' $A $B (inv_eq_t1 _ _ _ _ _ $deqA) $dB
with inv_eq_t1   _ _ _ _ _ (der_eq_ctx_tabs_domain $Γ $s $s' $A _   $B $t $deqA $dB $dt)
  ↪ der_abs $Γ $s $s' $A $t $B (inv_eq_t1 _ _ _ _ _ $deqA) $dB $dt
with inv_eq_t2   _ _ _ _ _ (der_eq_ctx_tabs_domain $Γ $s $s' $A $A' $B $t $deqA $dB $dt)
  ↪ der_type_conv $Γ (tabs $A' $B $t) (tfun $A' $B) (tfun $A $B) (smax $s $s')
      (der_abs $Γ $s $s' $A' $t $B (inv_eq_t2 _ _ _ _ _ $deqA)
             (der_conv_in_ctx $Γ $s (snext $s') $A $A' $B (tsort $s') $deqA $dB)
             (der_conv_in_ctx $Γ $s $s' $A $A' $t $B $deqA $dt))
      (der_eq_symm $Γ (snext (smax $s $s')) (tfun $A $B) (tfun $A' $B) (tsort (smax $s $s'))
                   (der_eq_ctx_prod_domain $Γ $s $s' $A $A' $B $deqA $dB))
with inv_eq_sort _ _ _ _ _ (der_eq_ctx_tabs_codomain $Γ $s $s' $A $B _   _  $dA $deqB _  )
  ↪ der_prod $Γ $s $s' $A $B $dA (inv_eq_t1 _ _ _ _ _ $deqB)
with inv_eq_t1   _ _ _ _ _ (der_eq_ctx_tabs_codomain $Γ $s $s' $A $B _   $t $dA $deqB $dt)
  ↪ der_abs $Γ $s $s' $A $t $B $dA (inv_eq_t1 _ _ _ _ _ $deqB) $dt
with inv_eq_t2   _ _ _ _ _ (der_eq_ctx_tabs_codomain $Γ $s $s' $A $B $B' $t $dA $deqB $dt)
  ↪ der_type_conv $Γ (tabs $A $B' $t) (tfun $A $B') (tfun $A $B) (smax $s $s')
      (der_abs $Γ $s $s' $A $t $B' $dA (inv_eq_t2 _ _ _ _ _ $deqB)
        (der_type_conv (Push $A $s $Γ) $t $B $B' $s' $dt $deqB))
      (der_eq_symm $Γ (snext (smax $s $s')) (tfun $A $B) (tfun $A $B') (tsort (smax $s $s'))
                   (der_eq_ctx_prod_codomain $Γ $s $s' $A $B $B' $dA $deqB))
;
