
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require ETT.ITT as ITT;

// Lemmas
symbol inv_sort {Γ : Context} {s : Sort} {t T : Term} : der_context Γ → der Γ t T s → der Γ T (tsort s) (snext s);
symbol inv_eq_sort {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_context Γ → der_eq Γ s T t1 t2 → der Γ T (tsort s) (snext s);
symbol inv_eq_t2   {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_context Γ → der_eq Γ s T t1 t2 → der Γ t2 T s;
symbol inv_eq_t1   {Γ : Context} {s : Sort} {T t1 t2 : Term} : der_context Γ → der_eq Γ s T t1 t2 → der Γ t1 T s;

symbol inv_teq_sort {Γ : Context} {s : Sort} {T S t1 t2 : Term} : der_context Γ → der Γ (teq T t1 t2) S (snext s) → der Γ T (tsort s) (snext s);
symbol inv_teq_t1   {Γ : Context} {s : Sort} {T S t1 t2 : Term} : der_context Γ → der Γ (teq T t1 t2) S (snext s) → der Γ t1 T s;
symbol inv_teq_t2   {Γ : Context} {s : Sort} {T S t1 t2 : Term} : der_context Γ → der Γ (teq T t1 t2) S (snext s) → der Γ t2 T s;

// Helpers
symbol pushIΓ {Γ : Context} {s : Sort} {t T : Term} (dΓ : der_context Γ) (d: der Γ t T s)
              : der_context (Push T s Γ) ≔
  pushΓ (inv_sort dΓ d) dΓ;
symbol pushEΓ {Γ : Context} {s : Sort} {t1 t2 T : Term} (dΓ : der_context Γ) (deq: der_eq Γ s T t1 t2)
              : der_context (Push T s Γ) ≔
  pushΓ (inv_eq_sort dΓ deq) dΓ;
symbol push1Γ {Γ : Context} {s : Sort} {T1 T2 : Term} (dΓ : der_context Γ) (deq: der_eq Γ (snext s) (tsort s) T1 T2)
              : der_context (Push T1 s Γ) ≔
  pushΓ (inv_eq_t1 dΓ deq) dΓ;
symbol push2Γ {Γ : Context} {s : Sort} {T1 T2 : Term} (dΓ : der_context Γ) (deq: der_eq Γ (snext s) (tsort s) T1 T2)
              : der_context (Push T2 s Γ) ≔
  pushΓ (inv_eq_t2 dΓ deq) dΓ;

// Definition of inv_sort
rule inv_sort _ (der_sort $Γ $s) ↪ der_sort $Γ (snext $s)
with inv_sort _ (der_prod $Γ $s $s' _ _ _ _) ↪ der_sort $Γ (smax $s $s')
with inv_sort _ (der_sigma $Γ $s $s' _ _ _ _) ↪ der_sort $Γ (smax $s $s')
with inv_sort _ (der_prop_type_eq $Γ $s _ _ _ _ _ _) ↪ der_sort $Γ $s
with inv_sort $dΓ (der_var _ $id) ↪ der_shift $id $dΓ (der_getΓ $id $dΓ)
with inv_sort $dΓ (der_type_conv _ _ _ _ _ _ $deq) ↪ inv_eq_t2 $dΓ $deq
with inv_sort $dΓ (der_abs $Γ $s $s' $A _ $B $dA _ $dt) ↪ der_prod $Γ $s $s' $A $B $dA (inv_sort (pushΓ $dA $dΓ) $dt)
with inv_sort $dΓ (der_app _ _ _ _ _ _ _ _ $dB _ $du) ↪ substitution $dΓ $dB $du
with inv_sort $dΓ (der_pair $Γ $s $s' _ $A _ $B _ $du $dB _) ↪ der_sigma $Γ $s $s' $A $B (inv_sort $dΓ $du) $dB
with inv_sort _ (der_π1 _ _ _ _ _ _ $dA _ _) ↪ $dA
with inv_sort $dΓ (der_π2 $Γ $s $s' $p $A $B $dA $dB $dp) ↪ substitution $dΓ $dB (der_π1 $Γ $s $s' $p $A $B $dA $dB $dp)
with inv_sort _ (der_refl $Γ $s $u $A $dA $du) ↪ der_prop_type_eq $Γ $s $A $u $u $dA $du $du
with inv_sort _ (der_K $Γ $s $A $a $p $dA $da $dp) ↪ der_prop_type_eq $Γ $s (teq $A $a $a) $p (trefl $A $a)
                                                                       (der_prop_type_eq $Γ $s $A $a $a $dA $da $da)
                                                                       $dp (der_refl $Γ $s $a $A $dA $da)
;

// Definition of inv_eq*
// Computation
rule inv_eq_sort $dΓ (der_eq_beta _  _  _   _  _  _  _  _ _ $dt $du) ↪ substitution $dΓ (inv_sort (pushΓ (inv_sort $dΓ $du) $dΓ) $dt) $du
with inv_eq_t1   $dΓ (der_eq_beta $Γ $s $s' $u $A $t $B _ _ $dt $du) ↪ der_app $Γ $s $s' $A (tabs $A $B $t) $u $B (inv_sort $dΓ $du) (inv_sort (pushΓ (inv_sort $dΓ $du) $dΓ) $dt)
                                                                            (der_abs $Γ $s $s' $A $t $B (inv_sort $dΓ $du) (inv_sort (pushΓ (inv_sort $dΓ $du) $dΓ) $dt) $dt) $du
with inv_eq_t2   $dΓ (der_eq_beta _  _  _   _  _  _  _  _ _ $dt $du) ↪ substitution $dΓ $dt $du
with inv_eq_sort _   (der_eq_eta  $Γ $s $s' $A _  $B $dA $dB _  ) ↪ der_prod $Γ $s $s' $A $B $dA $dB
with inv_eq_t1   $dΓ (der_eq_eta  $Γ $s $s' $A $f $B $dA $dB $df) ↪ der_abs $Γ $s $s' $A (tapp (Shift $A) (Shift1 $B) (Shift $f) (var db0)) $B $dA $dB
                                                                      (der_app (Push $A $s $Γ) $s $s' (Shift $A) (Shift $f) (var db0) (Shift1 $B)
                                                                        (der_shift0 $dA $dΓ $dA)
                                                                        (der_shift1 $dA $dA $dΓ $dB)
                                                                        (der_shift0 $dA $dΓ $df)
                                                                        (der_var (Push $A $s $Γ) db0))
with inv_eq_t2   _   (der_eq_eta  _  _  _   _  _  _  _   _   $df) ↪ $df
with inv_eq_sort $dΓ (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ inv_sort $dΓ $du
with inv_eq_t1   $dΓ (der_eq_π1 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_π1 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $dΓ $du) $dB
                                                                               (der_pair $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv)
with inv_eq_t2   _   (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ $du
with inv_eq_sort $dΓ (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ inv_sort $dΓ $dv
with inv_eq_t1   $dΓ (der_eq_π2 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_type_conv $Γ (π2 $A $B (tpair $A $B $u $v)) (apply1 $B (π1 $A $B (tpair $A $B $u $v))) (apply1 $B $u) $s'
                                                                            (der_π2 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $dΓ $du) $dB
                                                                              (der_pair $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv))
                                                                            (der_eq_cong_apply $dΓ
                                                                              (der_eq_refl $Γ (snext $s) $A (tsort $s) (inv_sort $dΓ $du))
                                                                              (der_eq_refl (Push $A $s $Γ) (snext $s') $B (tsort $s') $dB)
                                                                              (der_eq_π1 $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv)
                                                                              $dB $dB
                                                                              (der_π1 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $dΓ $du) $dB
                                                                                (der_pair $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv)) $du)
with inv_eq_t2   _   (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ $dv
// Conversion
with inv_eq_sort $dΓ (der_eq_conversion _ _ _ _ _ _ _ $deqT) ↪ inv_eq_t2 $dΓ $deqT
with inv_eq_t1   $dΓ (der_eq_conversion $Γ $s $t1 _ $T1 $T2 $deq $deqT) ↪ der_type_conv $Γ $t1 $T1 $T2 $s (inv_eq_t1 $dΓ $deq) $deqT
with inv_eq_t2   $dΓ (der_eq_conversion $Γ $s _ $t2 $T1 $T2 $deq $deqT) ↪ der_type_conv $Γ $t2 $T1 $T2 $s (inv_eq_t2 $dΓ $deq) $deqT
with inv_eq_sort $dΓ (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_sort $dΓ (inv_sort $dΓ $de)
with inv_eq_t1   $dΓ (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_t1   $dΓ (inv_sort $dΓ $de)
with inv_eq_t2   $dΓ (der_eq_lift _ _ _ _ _ _ $de) ↪ inv_teq_t2   $dΓ (inv_sort $dΓ $de)
// Structure
with inv_eq_sort $dΓ (der_eq_refl _ _ _ _ $du) ↪ inv_sort $dΓ $du
with inv_eq_t1   _   (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_t2   _   (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_sort $dΓ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_sort $dΓ $duv
with inv_eq_t1   $dΓ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_t1 $dΓ $duv
with inv_eq_t2   $dΓ (der_eq_trans _ _ _ _ _ _ _ $dvw) ↪ inv_eq_t2 $dΓ $dvw
with inv_eq_sort $dΓ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_sort $dΓ $duv
with inv_eq_t1   $dΓ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t2 $dΓ $duv
with inv_eq_t2   $dΓ (der_eq_symm _ _ _ _ _ $duv) ↪ inv_eq_t1 $dΓ $duv
// Congruence
// Lambda-calculus
with inv_eq_sort _   (der_eq_cong_tfun $Γ $s $s' _   _   _   _   _     _ _    _   ) ↪ der_sort $Γ (smax $s $s')
with inv_eq_t1   $dΓ (der_eq_cong_tfun $Γ $s $s' $A1 _   $B1 _   $deqA _ $dB1 _   ) ↪ der_prod $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t2   $dΓ (der_eq_cong_tfun $Γ $s $s' _   $A2 _   $B2 $deqA _ _    $dB2) ↪ der_prod $Γ $s $s' $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2
with inv_eq_sort $dΓ (der_eq_cong_tabs $Γ $s $s' $A1 _   $B1 _   _   _   $deqA _     _ $dB1 _    _    _   ) ↪ der_prod $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t1   $dΓ (der_eq_cong_tabs $Γ $s $s' $A1 _   $B1 _   $t1 _   $deqA _     _ $dB1 _    $dt1 _   ) ↪ der_abs $Γ $s $s' $A1 $t1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dt1
with inv_eq_t2   $dΓ (der_eq_cong_tabs $Γ $s $s' $A1 $A2 $B1 $B2 _   $t2 $deqA $deqB _ $dB1 $dB2 _    $dt2)
   ↪ der_type_conv $Γ (tabs $A2 $B2 $t2) (tfun $A2 $B2) (tfun $A1 $B1) (smax $s $s')
                    (der_abs $Γ $s $s' $A2 $t2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dt2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_tfun $Γ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2))
with inv_eq_sort $dΓ (der_eq_cong_tapp _  _  _   _   _   _   _   _   _   _   _   _     _     _ _     $dB1 _    _    _    $da1 _   ) ↪ substitution $dΓ $dB1 $da1
with inv_eq_t1   $dΓ (der_eq_cong_tapp $Γ $s $s' $A1 _   $B1 _   $f1 _   $a1 _   $deqA _     _ _     $dB1 _    $df1 _    $da1 _   ) ↪ der_app $Γ $s $s' $A1 $f1 $a1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $df1 $da1
with inv_eq_t2   $dΓ (der_eq_cong_tapp $Γ $s $s' _   $A2 $B1 $B2 _   $f2 $a1 $a2 $deqA $deqB _ $deqa $dB1 $dB2 _    $df2 $da1 $da2)
   ↪ der_type_conv $Γ (tapp $A2 $B2 $f2 $a2) (apply1 $B2 $a2) (apply1 $B1 $a1) $s'
                    (der_app $Γ $s $s' $A2 $f2 $a2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $df2 $da2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_apply $dΓ $deqA $deqB $deqa $dB1 $dB2 $da1 $da2))
// Pairs
with inv_eq_sort _   (der_eq_cong_tsum $Γ $s $s' _   _   _   _   _     _ _    _   ) ↪ der_sort $Γ (smax $s $s')
with inv_eq_t1   $dΓ (der_eq_cong_tsum $Γ $s $s' $A1 _   $B1 _   $deqA _ $dB1 _   ) ↪ der_sigma $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t2   $dΓ (der_eq_cong_tsum $Γ $s $s' _   $A2 _   $B2 $deqA _ _    $dB2) ↪ der_sigma $Γ $s $s' $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2
with inv_eq_sort $dΓ (der_eq_cong_tpair $Γ $s $s' $A1 _   $B1 _   _   _   _   _   $deqA _     _ _ $dB1 _    _    _    _    _   ) ↪ der_sigma $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t1   $dΓ (der_eq_cong_tpair $Γ $s $s' $A1 _   $B1 _   $a1 _   $b1 _   $deqA _     _ _ $dB1 _    $da1 _    $db1 _   ) ↪ der_pair $Γ $s $s' $a1 $A1 $b1 $B1 (inv_eq_t1 $dΓ $deqA) $da1 $dB1 $db1
with inv_eq_t2   $dΓ (der_eq_cong_tpair $Γ $s $s' $A1 $A2 $B1 $B2 _   $a2 _   $b2 $deqA $deqB _ _ $dB1 $dB2 _    $da2 _    $db2)
   ↪ der_type_conv $Γ (tpair $A2 $B2 $a2 $b2) (tsum $A2 $B2) (tsum $A1 $B1) (smax $s $s')
                    (der_pair $Γ $s $s' $a2 $A2 $b2 $B2 (inv_eq_t2 $dΓ $deqA) $da2 $dB2 $db2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_tsum $Γ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2))
with inv_eq_sort $dΓ (der_eq_cong_π1 _  _  _   _   _   _   _   _   _   $deqA _ _ _    _    _    _   ) ↪ inv_eq_t1 $dΓ $deqA
with inv_eq_t1   $dΓ (der_eq_cong_π1 $Γ $s $s' $A1 _   $B1 _   $p1 _   $deqA _ _ $dB1 _    $dp1 _   ) ↪ der_π1 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1
with inv_eq_t2   $dΓ (der_eq_cong_π1 $Γ $s $s' $A1 $A2 _   $B2 _   $p2 $deqA _ _ _    $dB2 _    $dp2)
   ↪ der_type_conv $Γ (π1 $A2 $B2 $p2) $A2 $A1 $s
                    (der_π1 $Γ $s $s' $p2 $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dp2)
                    (der_eq_symm _ _ _ _ _ $deqA)
with inv_eq_sort $dΓ (der_eq_cong_π2 $Γ $s $s' $A1 _   $B1 _   $p1 _   $deqA _     _     $dB1 _    $dp1 _   ) ↪ substitution $dΓ $dB1 (der_π1 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1)
with inv_eq_t1   $dΓ (der_eq_cong_π2 $Γ $s $s' $A1 _   $B1 _   $p1 _   $deqA _     _     $dB1 _    $dp1 _   ) ↪ der_π2 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1
with inv_eq_t2   $dΓ (der_eq_cong_π2 $Γ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
   ↪ der_type_conv $Γ (π2 $A2 $B2 $p2) (apply1 $B2 (π1 $A2 $B2 $p2)) (apply1 $B1 (π1 $A1 $B1 $p1)) $s'
                    (der_π2 $Γ $s $s' $p2 $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dp2)
                    (der_eq_symm _ _ _ _ _
                     (der_eq_cong_apply $dΓ $deqA $deqB
                      (der_eq_cong_π1 $Γ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
                      $dB1 $dB2
                      (der_π1 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1)
                      (der_π1 $Γ $s $s' $p2 $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dp2)))
// Equalities
with inv_eq_sort _   (der_eq_cong_teq $Γ $s _   _   _   _   _   _   _     _ _ _    _    _    _   ) ↪ der_sort $Γ $s
with inv_eq_t1   $dΓ (der_eq_cong_teq $Γ $s $A1 _   $a1 _   $b1 _   $deqA _ _ $da1 _    $db1 _   ) ↪ der_prop_type_eq $Γ $s $A1 $a1 $b1 (inv_eq_t1 $dΓ $deqA) $da1 $db1
with inv_eq_t2   $dΓ (der_eq_cong_teq $Γ $s _   $A2 _   $a2 _   $b2 $deqA _ _ _    $da2 _    $db2) ↪ der_prop_type_eq $Γ $s $A2 $a2 $b2 (inv_eq_t2 $dΓ $deqA) $da2 $db2
with inv_eq_sort $dΓ (der_eq_cong_trefl $Γ $s $A1 _   $a1 _   $deqA _     $da1 _   ) ↪ der_prop_type_eq $Γ $s $A1 $a1 $a1 (inv_eq_t1 $dΓ $deqA) $da1 $da1
with inv_eq_t1   $dΓ (der_eq_cong_trefl $Γ $s $A1 _   $a1 _   $deqA _     $da1 _   ) ↪ der_refl $Γ $s $a1 $A1 (inv_eq_t1 $dΓ $deqA) $da1
with inv_eq_t2   $dΓ (der_eq_cong_trefl $Γ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
   ↪ der_type_conv $Γ (trefl $A2 $a2) (teq $A2 $a2 $a2) (teq $A1 $a1 $a1) $s
                    (der_refl $Γ $s $a2 $A2 (inv_eq_t2 $dΓ $deqA) $da2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_teq $Γ $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2))
with inv_eq_sort $dΓ (der_eq_cong_tK $Γ $s $A1 _   $a1 _   $p1 _   $deqA _     _     $da1 _    $dp1 _   )
   ↪ der_prop_type_eq $Γ $s (teq $A1 $a1 $a1) $p1 (trefl $A1 $a1)
                       (der_prop_type_eq $Γ $s $A1 $a1 $a1 (inv_eq_t1 $dΓ $deqA) $da1 $da1)
                       $dp1 (der_refl $Γ $s $a1 $A1 (inv_eq_t1 $dΓ $deqA) $da1)
with inv_eq_t1   $dΓ (der_eq_cong_tK $Γ $s $A1 _   $a1 _   $p1 _   $deqA _     _     $da1 _    $dp1 _   )
   ↪ der_K $Γ $s $A1 $a1 $p1 (inv_eq_t1 $dΓ $deqA) $da1 $dp1
with inv_eq_t2   $dΓ (der_eq_cong_tK $Γ $s $A1 $A2 $a1 $a2 $p1 $p2 $deqA $deqa $deqp $da1 $da2 $dp1 $dp2)
   ↪ der_type_conv $Γ (tK $A2 $a2 $p2) (teq (teq $A2 $a2 $a2) $p2 (trefl $A2 $a2)) (teq (teq $A1 $a1 $a1) $p1 (trefl $A1 $a1)) $s
                    (der_K $Γ $s $A2 $a2 $p2 (inv_eq_t2 $dΓ $deqA) $da2 $dp2)
                    (der_eq_symm _ _ _ _ _
                      (der_eq_cong_teq $Γ $s (teq $A1 $a1 $a1) (teq $A2 $a2 $a2) $p1 $p2 (trefl $A1 $a1) (trefl $A2 $a2)
                        (der_eq_cong_teq $Γ $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2)
                        $deqp (der_eq_cong_trefl $Γ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
                        $dp1 $dp2 (der_refl $Γ $s $a1 $A1 (inv_eq_t1 $dΓ $deqA) $da1) (der_refl $Γ $s $a2 $A2 (inv_eq_t2 $dΓ $deqA) $da2)))
;

// Propositional equality inversion
rule inv_teq_sort _   (der_prop_type_eq _ _ _ _ _ $dA _    _   ) ↪ $dA
with inv_teq_t1   _   (der_prop_type_eq _ _ _ _ _ _   $da1 _   ) ↪ $da1
with inv_teq_t2   _   (der_prop_type_eq _ _ _ _ _ _   _    $da2) ↪ $da2
with inv_teq_sort $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_sort $dΓ $du
with inv_teq_t1   $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_t1   $dΓ $du
with inv_teq_t2   $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_t2   $dΓ $du
;
