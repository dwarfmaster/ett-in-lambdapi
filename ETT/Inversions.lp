
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require ETT.ITT as ITT;

// Lemmas
symbol substitution {Γ : Context} {s s' : Sort} {A B C : Term} :
  der (Push A s Γ) C B s' → Π{u : Term}, der Γ u A s → der Γ (apply1 C u) (apply1 B u) s';
symbol inv_context {Γ : Context} {s : Sort} {t T : Term} : der Γ t T s → der_context Γ;
symbol inv_eq_context {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_eq Γ s T t1 t2 → der_context Γ;
symbol inv_sort {Γ : Context} {s : Sort} {t T : Term} : der Γ t T s → der Γ T (tsort s) (snext s);
symbol inv_eq_sort {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_eq Γ s T t1 t2 → der Γ T (tsort s) (snext s);
symbol inv_eq_t2   {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_eq Γ s T t1 t2 → der Γ t2 T s;
symbol inv_eq_t1   {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_eq Γ s T t1 t2 → der Γ t1 T s;

symbol inv_teq_sort {Γ : Context} {s : Sort} {T t1 t2 e : Term} : der Γ e (teq T t1 t2) s → der Γ T (tsort s) (snext s);
symbol inv_teq_t1   {Γ : Context} {s : Sort} {T t1 t2 e : Term} : der Γ e (teq T t1 t2) s → der Γ t1 T s;
symbol inv_teq_t2   {Γ : Context} {s : Sort} {T t1 t2 e : Term} : der Γ e (teq T t1 t2) s → der Γ t2 T s;

// Helpers
symbol der_subΓ (Γ : Context) (id : DBId) (_ : der_context Γ): der (getΓ Γ id) (get Γ id) (tsort (getS Γ id)) (snext (getS Γ id));
rule der_subΓ _ db0 (der_context_push _ _ _ $dA _) ↪ $dA
with der_subΓ _ (dbsucc $id) (der_context_push _ _ _ _ $dt) ↪ der_subΓ _ $id $dt;

symbol pushΓ {Γ : Context} {s : Sort} {T : Term} (d : der Γ T (tsort s) (snext s)) : der_context (Push T s Γ) ≔
  der_context_push Γ s T d (inv_context d);


// Definition of inv_sort
rule inv_sort (der_var $Γ $id $dΓ) ↪ der_shift $id $Γ _ _ _ (der_subΓ _ $id $dΓ)
with inv_sort (der_type_conv _ _ _ _ _ _ $deq) ↪ inv_eq_t2 $deq
with inv_sort (der_abs $Γ $s $s' $A _ $B $dA $dB _) ↪ der_prod $Γ $s $s' $A $B $dA $dB
with inv_sort (der_app _ _ _ _ _ _ _ _ $dB _ $du) ↪ substitution $dB $du
with inv_sort (der_pair $Γ $s $s' _ $A _ $B $dA _ $dB _) ↪ der_sigma $Γ $s $s' $A $B $dA $dB
with inv_sort (der_π1 _ _ _ _ _ _ $dA _ _) ↪ $dA
with inv_sort (der_π2 $Γ $s $s' $p $A $B $dA $dB $dp) ↪ substitution $dB (der_π1 $Γ $s $s' $p $A $B $dA $dB $dp)
with inv_sort (der_refl $Γ $s $u $A $dA $du) ↪ der_prop_type_eq $Γ $s $A $u $u $dA $du $du
with inv_sort (der_uip $Γ $s $e1 $e2 $u $v $A $de1 $de2) ↪ der_prop_type_eq $Γ $s (teq $A $u $v) $e1 $e2
                                                                             (inv_sort $de1) $de1 $de2
with inv_sort (der_funext $Γ $s $s' $f $g $A _ $B $dA $dB $df $dg _)
  ↪ der_prop_type_eq $Γ (smax $s $s') (tfun $A $B) $f $g (der_prod $Γ $s $s' $A $B $dA $dB) $df $dg
;

// Definition of inv_eq*
// Computation
rule inv_eq_sort (der_eq_beta _  _  _   _  _  _  _  _ _ $dt $du) ↪ substitution (inv_sort $dt) $du
with inv_eq_t1   (der_eq_beta $Γ $s $s' $u $A $t $B _ _ $dt $du) ↪ der_app $Γ $s $s' $A (tabs $A $B $t) $u $B (inv_sort $du) (inv_sort $dt)
                                                                            (der_abs $Γ $s $s' $A $t $B (inv_sort $du) (inv_sort $dt) $dt) $du
with inv_eq_t2   (der_eq_beta _  _  _   _  _  _  _  _ _ $dt $du) ↪ substitution $dt $du
with inv_eq_sort (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ inv_sort $du
with inv_eq_t1   (der_eq_π1 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_π1 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                                                                           (der_pair $Γ $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv)
with inv_eq_t2   (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ $du
with inv_eq_sort (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ inv_sort $dv
with inv_eq_t1   (der_eq_π2 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_type_conv $Γ (π2 $A $B (tpair $A $B $u $v)) (apply1 $B (π1 $A $B (tpair $A $B $u $v))) (apply1 $B $u) $s'
                                                                        (der_π2 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $du) $dB
                                                                          (der_pair $Γ $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv))
                                                                        (der_eq_ctx $Γ $s (snext $s') $B (tsort $s') (π1 $A $B (tpair $A $B $u $v)) $u $A
                                                                          (der_eq_π1 $Γ $s $s' $u $A $v $B (inv_sort $du) $du $dB $dv) $dB)
with inv_eq_t2   (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ $dv
// Conversion
with inv_eq_sort (der_eq_conversion _ _ _ _ _ _ _ $deqT) ↪ inv_eq_t2 $deqT
with inv_eq_t1   (der_eq_conversion $Γ $s $t1 _ $T1 $T2 $deq $deqT) ↪ der_type_conv $Γ $t1 $T1 $T2 $s (inv_eq_t1 $deq) $deqT
with inv_eq_t2   (der_eq_conversion $Γ $s _ $t2 $T1 $T2 $deq $deqT) ↪ der_type_conv $Γ $t2 $T1 $T2 $s (inv_eq_t2 $deq) $deqT
with inv_eq_sort (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_sort $de
with inv_eq_t1   (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_t1   $de
with inv_eq_t2   (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_t2   $de
// Congruence
with inv_eq_sort (der_eq_refl _ _ _ _ $du) ↪ inv_sort $du
with inv_eq_t1   (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_t2   (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_sort (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_sort $duv
with inv_eq_t1   (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_t1 $duv
with inv_eq_t2   (der_eq_trans _ _ _ _ _ _ _ $dvw) ↪ inv_eq_t2 $dvw
with inv_eq_sort (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_sort $duv
with inv_eq_t1   (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t2 $duv
with inv_eq_t2   (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t1 $duv
// Context
// prod
with inv_eq_sort (der_eq_ctx_prod_domain $Γ $s $s' _  _   _  $deqA _  )
  ↪ der_sort $Γ (smax $s $s') (inv_eq_context $deqA)
with inv_eq_t1   (der_eq_ctx_prod_domain $Γ $s $s' $A _   $B $deqA $dB)
  ↪ der_prod $Γ $s $s' $A $B (inv_eq_t1 $deqA) $dB
with inv_eq_t2   (der_eq_ctx_prod_domain $Γ $s $s' $A $A' $B $deqA $dB)
  ↪ der_prod $Γ $s $s' $A' $B (inv_eq_t2 $deqA)
              (der_conv_in_ctx $Γ $s (snext $s') $A $A' $B (tsort $s') $deqA $dB)
with inv_eq_sort (der_eq_ctx_prod_codomain $Γ $s $s' _  _  _   $dA _    )
  ↪ der_sort $Γ (smax $s $s') (inv_context $dA)
with inv_eq_t1   (der_eq_ctx_prod_codomain $Γ $s $s' $A $B _   $dA $deqB)
  ↪ der_prod $Γ $s $s' $A $B  $dA (inv_eq_t1 $deqB)
with inv_eq_t2   (der_eq_ctx_prod_codomain $Γ $s $s' $A _  $B' $dA $deqB)
  ↪ der_prod $Γ $s $s' $A $B' $dA (inv_eq_t2 $deqB)
// abs
with inv_eq_sort (der_eq_ctx_tabs_domain $Γ $s $s' $A _   $B _  $deqA $dB _  )
  ↪ der_prod $Γ $s $s' $A $B (inv_eq_t1 $deqA) $dB
with inv_eq_t1   (der_eq_ctx_tabs_domain $Γ $s $s' $A _   $B $t $deqA $dB $dt)
  ↪ der_abs $Γ $s $s' $A $t $B (inv_eq_t1 $deqA) $dB $dt
with inv_eq_t2   (der_eq_ctx_tabs_domain $Γ $s $s' $A $A' $B $t $deqA $dB $dt)
  ↪ der_type_conv $Γ (tabs $A' $B $t) (tfun $A' $B) (tfun $A $B) (smax $s $s')
      (der_abs $Γ $s $s' $A' $t $B (inv_eq_t2 $deqA)
             (der_conv_in_ctx $Γ $s (snext $s') $A $A' $B (tsort $s') $deqA $dB)
             (der_conv_in_ctx $Γ $s $s' $A $A' $t $B $deqA $dt))
      (der_eq_symm $Γ (snext (smax $s $s')) (tfun $A $B) (tfun $A' $B) (tsort (smax $s $s'))
                   (der_eq_ctx_prod_domain $Γ $s $s' $A $A' $B $deqA $dB))
with inv_eq_sort (der_eq_ctx_tabs_codomain $Γ $s $s' $A $B _   _  $dA $deqB _  )
  ↪ der_prod $Γ $s $s' $A $B $dA (inv_eq_t1 $deqB)
with inv_eq_t1   (der_eq_ctx_tabs_codomain $Γ $s $s' $A $B _   $t $dA $deqB $dt)
  ↪ der_abs $Γ $s $s' $A $t $B $dA (inv_eq_t1 $deqB) $dt
with inv_eq_t2   (der_eq_ctx_tabs_codomain $Γ $s $s' $A $B $B' $t $dA $deqB $dt)
  ↪ der_type_conv $Γ (tabs $A $B' $t) (tfun $A $B') (tfun $A $B) (smax $s $s')
      (der_abs $Γ $s $s' $A $t $B' $dA (inv_eq_t2 $deqB)
        (der_type_conv (Push $A $s $Γ) $t $B $B' $s' $dt $deqB))
      (der_eq_symm $Γ (snext (smax $s $s')) (tfun $A $B) (tfun $A $B') (tsort (smax $s $s'))
                   (der_eq_ctx_prod_codomain $Γ $s $s' $A $B $B' $dA $deqB))
;
