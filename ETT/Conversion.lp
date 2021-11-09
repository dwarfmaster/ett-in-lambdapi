
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.DeBruijn;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.Packing;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.Congruences;
require open ETT.TContext;
require open ETT.Translation;

// convert wrapper for types
rule convert_T $Γ $d1 $d2
  ↪ heq_to_eq (convert $Γ $d1 $d2);

// convert wrapper
rule convert $Γ $d1 $d2
  ↪ convertR $Γ (PCEmpty $Γ) $d1 $d2;

// Helper for the non-diagonal cases
symbol convertTypeConversion (Γ : TContext) (HC : PContext Γ) {t T1 T2 T3 : ETT.Term} {s : ETT.Sort}
                             (d1 : der (τ_Γ (projΓ1 HC)) t T1 s)
                             (d2 : der (τ_Γ (projΓ2 HC)) t T2 s)
                             (deq : der_eq (τ_Γ (projΓ2 HC)) (ETT.snext s) (ETT.tsort s) T2 T3)
                             : H (τ (projΓ1 HC) d1) (τ (projΓ2 HC)
                                                       (der_type_conv (τ_Γ (projΓ2 HC)) t T2 T3 s d2 deq)) ≔
  heq_trans
    (convertR Γ HC d1 d2)
    (heq_trans
      (heq_of_transport
        (τ (projΓ2 HC) d2)
        (convert_T (projΓ2 HC) (inv_sort (τ_dΓ (projΓ2 HC)) d2) (inv_eq_t1 (τ_dΓ (projΓ2 HC)) deq)))
      (heq_of_transport
        (transport (convert_T (projΓ2 HC) (inv_sort (τ_dΓ (projΓ2 HC)) d2) (inv_eq_t1 (τ_dΓ (projΓ2 HC)) deq)) (τ (projΓ2 HC) d2))
        (τ_eqT (projΓ2 HC) deq)));
symbol convertTypeConversion' (Γ : TContext) (HC : PContext Γ) {t T1 T2 T3 : ETT.Term} {s : ETT.Sort}
                              (d1 : der (τ_Γ (projΓ1 HC)) t T1 s)
                              (d2 : der (τ_Γ (projΓ2 HC)) t T3 s)
                              (deq : der_eq (τ_Γ (projΓ1 HC)) (ETT.snext s) (ETT.tsort s) T1 T2)
                              : H (τ (projΓ1 HC) (der_type_conv (τ_Γ (projΓ1 HC)) t T1 T2 s d1 deq))
                                  (τ (projΓ2 HC) d2) ≔
  heq_trans
    (heq_symm (heq_trans
      (heq_of_transport
        (τ (projΓ1 HC) d1)
        (convert_T (projΓ1 HC) (inv_sort (τ_dΓ (projΓ1 HC)) d1) (inv_eq_t1 (τ_dΓ (projΓ1 HC)) deq)))
      (heq_of_transport
        (transport (convert_T (projΓ1 HC) (inv_sort (τ_dΓ (projΓ1 HC)) d1) (inv_eq_t1 (τ_dΓ (projΓ1 HC)) deq)) (τ (projΓ1 HC) d1))
        (τ_eqT (projΓ1 HC) deq))))
    (convertR Γ HC d1 d2);

// convert recursive
// Types
rule convertR _ _ (der_sort _ $s) (der_sort _ _)
  ↪ heq_refl (u (snext (τ_s $s))) (u (τ_s $s))
with convertR $Γ $H (der_prod _ $s $s' $A $B $dA1 $dB1) (der_prod _ $s $s' $A $B $dA2 $dB2)
  ↪ cong_prod
       (λ a, τ_T (TPush (projΓ1 $H) $s $A $dA1 a) $dB1)
       (λ a, τ_T (TPush (projΓ2 $H) $s $A $dA2 a) $dB2)
       (convertR $Γ $H $dA1 $dA2)
       (λ p, convertR $Γ (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
with convertR $Γ $H (der_sigma _ $s $s' $A $B $dA1 $dB1) (der_sigma _ $s $s' $A $B $dA2 $dB2)
  ↪ cong_sum
       (λ a, τ_T (TPush (projΓ1 $H) $s $A $dA1 a) $dB1)
       (λ a, τ_T (TPush (projΓ2 $H) $s $A $dA2 a) $dB2)
       (convertR $Γ $H $dA1 $dA2)
       (λ p, convertR $Γ (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
with convertR $Γ $H (der_prop_type_eq _ $s $A $u $v $dA1 $du1 $dv1) (der_prop_type_eq _ $s $A $u $v $dA2 $du2 $dv2)
  ↪ cong_eq
       (convertR $Γ $H $dA1 $dA2)
       (heq_conj (convertR $Γ $H $du1 $du2)
         (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $du1) $dA1)
         (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $du2) $dA2))
       (heq_conj (convertR $Γ $H $dv1 $dv2)
         (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $dv1) $dA1)
         (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $dv2) $dA2))

// Structural rules
with convertR _ $H (der_var _ $id) (der_var _ $id)
  ↪ heq_conj (pgetHShift $id $H)
       (convert_T (projΓ1 $H) (der_shift $id (τ_dΓ (projΓ1 $H)) (pgetD1 $id $H)) (der_shift $id (τ_dΓ (projΓ1 $H)) (der_getΓ $id (τ_dΓ (projΓ1 $H)))))
       (convert_T (projΓ2 $H) (der_shift $id (τ_dΓ (projΓ2 $H)) (pgetD2 $id $H)) (der_shift $id (τ_dΓ (projΓ2 $H)) (der_getΓ $id (τ_dΓ (projΓ2 $H)))))
with convertR $Γ $H (der_type_conv _ $u $A $B $s $du1 $deq1) (der_type_conv _ $u $A $B $s $du2 $deq2)
  ↪ convertTypeConversion $Γ $H (der_type_conv _ $u $A $B $s $du1 $deq1) $du2 $deq2

// λ-calculus
with convertR $Γ $H (der_abs _ $s $s' $A $t $B $dA1 _ $dt1) (der_abs _ $s $s' $A $t $B $dA2 _ $dt2)
  ↪ cong_lambda
       (λ a, τ_T (TPush (projΓ1 $H) $s $A $dA1 a) (inv_sort (pushΓ $dA1 (τ_dΓ (projΓ1 $H))) $dt1))
       (λ a, τ_T (TPush (projΓ2 $H) $s $A $dA2 a) (inv_sort (pushΓ $dA2 (τ_dΓ (projΓ2 $H))) $dt2))
       (λ a, τ (TPush (projΓ1 $H) $s $A $dA1 a) $dt1)
       (λ a, τ (TPush (projΓ2 $H) $s $A $dA2 a) $dt2)
       (convertR $Γ $H $dA1 $dA2)
       (λ p, convertR $Γ (PCPush $H $dA1 $dA2 (projHEq p)) (inv_sort (pushΓ $dA1 (τ_dΓ (projΓ1 $H))) $dt1) (inv_sort (pushΓ $dA2 (τ_dΓ (projΓ2 $H))) $dt2))
       (λ p, convertR $Γ (PCPush $H $dA1 $dA2 (projHEq p)) $dt1 $dt2)
with convertR $Γ $H (der_app _ $s $s' $A $t $u $B _ $dB1 $dt1 $du1) (der_app _ $s $s' $A $t $u $B _ $dB2 $dt2 $du2)
  ↪ heq_conj
       (cong_app
         (λ a, τ_T (TPush (projΓ1 $H) $s $A (inv_sort (τ_dΓ (projΓ1 $H)) $du1) a) $dB1)
         (λ a, τ_T (TPush (projΓ2 $H) $s $A (inv_sort (τ_dΓ (projΓ2 $H)) $du2) a) $dB2)
         (convertR $Γ $H (inv_sort (τ_dΓ (projΓ1 $H)) $du1) (inv_sort (τ_dΓ (projΓ2 $H)) $du2))
         (λ p, convertR $Γ (PCPush $H (inv_sort (τ_dΓ (projΓ1 $H)) $du1) (inv_sort (τ_dΓ (projΓ2 $H)) $du2) (projHEq p)) $dB1 $dB2)
         (heq_conj (convertR $Γ $H $dt1 $dt2)
           (τ_fun_eq (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $du1) $dB1 (inv_sort (τ_dΓ (projΓ1 $H)) $dt1))
           (τ_fun_eq (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $du2) $dB2 (inv_sort (τ_dΓ (projΓ2 $H)) $dt2)))
         (convertR $Γ $H $du1 $du2))
       (τ_substT_eq (projΓ1 $H) $dB1 $du1)
       (τ_substT_eq (projΓ2 $H) $dB2 $du2)
with convertR $Γ $H (der_pair _ $s $s' $u $A $v $B _ $du1 $dB1 $dv1) (der_pair _ $s $s' $u $A $v $B _ $du2 $dB2 $dv2)
  ↪ cong_pair
       (λ a, τ_T (TPush (projΓ1 $H) $s $A (inv_sort (τ_dΓ (projΓ1 $H)) $du1) a) $dB1)
       (λ a, τ_T (TPush (projΓ2 $H) $s $A (inv_sort (τ_dΓ (projΓ2 $H)) $du2) a) $dB2)
       (convertR $Γ $H (inv_sort (τ_dΓ (projΓ1 $H)) $du1) (inv_sort (τ_dΓ (projΓ2 $H)) $du2))
       (λ p, convertR $Γ (PCPush $H (inv_sort (τ_dΓ (projΓ1 $H)) $du1) (inv_sort (τ_dΓ (projΓ2 $H)) $du2) (projHEq p)) $dB1 $dB2)
       (convertR $Γ $H $du1 $du2)
       (heq_conj'
         (heq_conj (convertR $Γ $H $dv1 $dv2)
           (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $dv1) (substitution (τ_dΓ (projΓ1 $H)) $dB1 $du1))
           (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $dv2) (substitution (τ_dΓ (projΓ2 $H)) $dB2 $du2)))
         (τ_substT_eq (projΓ1 $H) $dB1 $du1)
         (τ_substT_eq (projΓ2 $H) $dB2 $du2))
with convertR $Γ $H (der_π1 _ $s $s' $p $A $B $dA1 $dB1 $dp1) (der_π1 _ $s $s' $p $A $B $dA2 $dB2 $dp2)
  ↪ cong_proj1
       (λ a, τ_T (TPush (projΓ1 $H) $s $A $dA1 a) $dB1)
       (λ a, τ_T (TPush (projΓ2 $H) $s $A $dA2 a) $dB2)
       (convertR $Γ $H $dA1 $dA2)
       (λ p, convertR $Γ (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
       (heq_conj (convertR $Γ $H $dp1 $dp2)
         (τ_sum_eq (projΓ1 $H) $dA1 $dB1 (inv_sort (τ_dΓ (projΓ1 $H)) $dp1))
         (τ_sum_eq (projΓ2 $H) $dA2 $dB2 (inv_sort (τ_dΓ (projΓ2 $H)) $dp2)))
with convertR $Γ $H (der_π2 _ $s $s' $p $A $B $dA1 $dB1 $dp1) (der_π2 _ $s $s' $p $A $B $dA2 $dB2 $dp2)
  ↪ heq_conj
       (cong_proj2
         (λ a, τ_T (TPush (projΓ1 $H) $s $A $dA1 a) $dB1)
         (λ a, τ_T (TPush (projΓ2 $H) $s $A $dA2 a) $dB2)
         (convertR $Γ $H $dA1 $dA2)
         (λ p, convertR $Γ (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
         (heq_conj (convertR $Γ $H $dp1 $dp2)
           (τ_sum_eq (projΓ1 $H) $dA1 $dB1 (inv_sort (τ_dΓ (projΓ1 $H)) $dp1))
           (τ_sum_eq (projΓ2 $H) $dA2 $dB2 (inv_sort (τ_dΓ (projΓ2 $H)) $dp2))))
       (τ_substT_eq (projΓ1 $H) $dB1 (der_π1 (τ_Γ (projΓ1 $H)) $s $s' $p $A $B $dA1 $dB1 $dp1))
       (τ_substT_eq (projΓ2 $H) $dB2 (der_π1 (τ_Γ (projΓ2 $H)) $s $s' $p $A $B $dA2 $dB2 $dp2))

// Equality
with convertR $Γ $H (der_refl _ $s $u $A $dA1 $du1) (der_refl _ $s $u $A $dA2 $du2)
  ↪ cong_refl
       (convertR $Γ $H $dA1 $dA2)
       (heq_conj (convertR $Γ $H $du1 $du2)
         (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $du1) $dA1)
         (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $du2) $dA2))
with convertR $Γ $H (der_uip _ $s $A $a $p $dA1 $da1 $dp1) (der_uip _ $s $A $a $p $dA2 $da2 $dp2)
  ↪ let dT1 ≔ der_prop_type_eq (τ_Γ (projΓ1 $H)) $s $A $a $a $dA1 $da1 $da1 in
     let dT2 ≔ der_prop_type_eq (τ_Γ (projΓ2 $H)) $s $A $a $a $dA2 $da2 $da2 in
     heq_conj
       (cong_K
           (convertR $Γ $H $dA1 $dA2)
           (heq_conj
             (convertR $Γ $H $da1 $da2)
             (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $da1) $dA1)
             (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $da2) $dA2))
           (heq_conj
             (convertR $Γ $H $dp1 $dp2)
             (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $dp1) dT1)
             (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $dp2) dT2)))
       (trans_eq_as_eq
         (transport (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $dp1) dT1) (τ (projΓ1 $H) $dp1))
         (eq_of_transport
           (refl (τ_s $s) (τ_T (projΓ1 $H) $dA1) (transport (convert_T (projΓ1 $H) (inv_sort (τ_dΓ (projΓ1 $H)) $da1) $dA1) (τ (projΓ1 $H) $da1)))
           (convert_T (projΓ1 $H) dT1 dT1)))
       (trans_eq_as_eq
         (transport (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $dp2) dT2) (τ (projΓ2 $H) $dp2))
         (eq_of_transport
           (refl (τ_s $s) (τ_T (projΓ2 $H) $dA2) (transport (convert_T (projΓ2 $H) (inv_sort (τ_dΓ (projΓ2 $H)) $da2) $dA2) (τ (projΓ2 $H) $da2)))
           (convert_T (projΓ2 $H) dT2 dT2)))

// Type conversion
with convertR $Γ $H (der_sort _ $s) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_sort _ $s) $dX $deq
with convertR $Γ $H (der_prod _ $s $s' $A $B $dA $dB) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_prod _ $s $s' $A $B $dA $dB) $dX $deq
with convertR $Γ $H (der_sigma _ $s $s' $A $B $dA $dB) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_sigma _ $s $s' $A $B $dA $dB) $dX $deq
with convertR $Γ $H (der_prop_type_eq _ $s $A $u $v $dA $du $dv) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_prop_type_eq _ $s $A $u $v $dA $du $dv) $dX $deq
with convertR $Γ $H (der_var _ $id) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_var _ $id) $dX $deq
with convertR $Γ $H (der_abs _ $s $s' $A $t $B $dA $dB $dt) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_abs _ $s $s' $A $t $B $dA $dB $dt) $dX $deq
with convertR $Γ $H (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du) $dX $deq
with convertR $Γ $H (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv) $dX $deq
with convertR $Γ $H (der_π1 _ $s $s' $p $A $B $dA $dB $dp) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_π1 _ $s $s' $p $A $B $dA $dB $dp) $dX $deq
with convertR $Γ $H (der_π2 _ $s $s' $p $A $B $dA $dB $dp) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_π2 _ $s $s' $p $A $B $dA $dB $dp) $dX $deq
with convertR $Γ $H (der_refl _ $s $u $A $dA $du) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_refl _ $s $u $A $dA $du) $dX $deq
with convertR $Γ $H (der_uip _ $s $A $a $p $dA $da $dp) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $H (der_uip _ $s $A $a $p $dA $da $dp) $dX $deq
// Symmetric cases
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_sort _ $s)
  ↪ convertTypeConversion' $Γ $H $dX (der_sort _ $s) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_prod _ $s $s' $A $B $dA $dB)
  ↪ convertTypeConversion' $Γ $H $dX (der_prod _ $s $s' $A $B $dA $dB) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_sigma _ $s $s' $A $B $dA $dB)
  ↪ convertTypeConversion' $Γ $H $dX (der_sigma _ $s $s' $A $B $dA $dB) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_prop_type_eq _ $s $A $u $v $dA $du $dv)
  ↪ convertTypeConversion' $Γ $H $dX (der_prop_type_eq _ $s $A $u $v $dA $du $dv) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_var _ $id)
  ↪ convertTypeConversion' $Γ $H $dX (der_var _ $id) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_abs _ $s $s' $A $t $B $dA $dB $dt)
  ↪ convertTypeConversion' $Γ $H $dX (der_abs _ $s $s' $A $t $B $dA $dB $dt) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du)
  ↪ convertTypeConversion' $Γ $H $dX (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ convertTypeConversion' $Γ $H $dX (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_π1 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ convertTypeConversion' $Γ $H $dX (der_π1 _ $s $s' $p $A $B $dA $dB $dp) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ convertTypeConversion' $Γ $H $dX (der_π2 _ $s $s' $p $A $B $dA $dB $dp) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_refl _ $s $u $A $dA $du)
  ↪ convertTypeConversion' $Γ $H $dX (der_refl _ $s $u $A $dA $du) $deq
with convertR $Γ $H (der_type_conv _ _ _ _ _ $dX $deq) (der_uip _ $s $A $a $p $dA $da $dp)
  ↪ convertTypeConversion' $Γ $H $dX (der_uip _ $s $A $a $p $dA $da $dp) $deq
;
