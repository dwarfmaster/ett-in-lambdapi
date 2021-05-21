
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.XLemmas;
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

symbol magic {s : Sort} (A : U s) : ε s A;

// convert wrapper for types
rule convert_T $Γ $d1 $d2
  ↪ heq_to_eq (convert $Γ $d1 $d2);

// convert wrapper
rule convert $Γ $d1 $d2
  ↪ convertR $Γ (COTail $Γ) (COTail $Γ) (PCEmpty $Γ) $d1 $d2;

// Helper for the non-diagonal cases
symbol convertTypeConversion (Γ : TContext) (Γ1 Γ2 : ContextOver Γ) (HC : PContext Γ Γ1 Γ2) {t T1 T2 T3 : ETT.Term} {s : ETT.Sort}
                             (d1 : der (τ_Γ (Concat Γ Γ1)) t T1 s)
                             (d2 : der (τ_Γ (Concat Γ Γ2)) t T2 s)
                             (deq : der_eq (τ_Γ (Concat Γ Γ2)) (ETT.snext s) (ETT.tsort s) T2 T3)
                             : H (τ (Concat Γ Γ1) d1) (τ (Concat Γ Γ2)
                                                         (der_type_conv (τ_Γ (Concat Γ Γ2)) t T2 T3 s d2 deq)) ≔
  heq_trans
    (convertR Γ Γ1 Γ2 HC d1 d2)
    (heq_trans
      (heq_of_transport
        (τ (Concat Γ Γ2) d2)
        (convert_T (Concat Γ Γ2) (inv_sort d2) (inv_eq_t1 deq)))
      (heq_of_transport
        (transport (convert_T (Concat Γ Γ2) (inv_sort d2) (inv_eq_t1 deq)) (τ (Concat Γ Γ2) d2))
        (τ_eqT (Concat Γ Γ2) deq)));

// convert recursive
// Types
rule convertR _ _ _ _ (der_sort _ $s _) (der_sort _ _ _)
  ↪ heq_refl (u (snext (τ_s $s))) (u (τ_s $s))
with convertR $Γ $T1 $T2 $H (der_prod _ $s $s' $A $B $dA1 $dB1) (der_prod _ $s $s' $A $B $dA2 $dB2)
  ↪ cong_prod
       (λ a, τ_T (TPush (Concat $Γ $T1) $s $A $dA1 a) $dB1)
       (λ a, τ_T (TPush (Concat $Γ $T2) $s $A $dA2 a) $dB2)
       (convertR $Γ $T1 $T2 $H $dA1 $dA2)
       (λ p, convertR $Γ (COPush $T1 $dA1 (projT1 p)) (COPush $T2 $dA2 (projT2 p))
                      (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
with convertR $Γ $T1 $T2 $H (der_sigma _ $s $s' $A $B $dA1 $dB1) (der_sigma _ $s $s' $A $B $dA2 $dB2)
  ↪ cong_sum
       (λ a, τ_T (TPush (Concat $Γ $T1) $s $A $dA1 a) $dB1)
       (λ a, τ_T (TPush (Concat $Γ $T2) $s $A $dA2 a) $dB2)
       (convertR $Γ $T1 $T2 $H $dA1 $dA2)
       (λ p, convertR $Γ (COPush $T1 $dA1 (projT1 p)) (COPush $T2 $dA2 (projT2 p))
                      (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
with convertR $Γ $T1 $T2 $H (der_prop_type_eq _ $s $A $u $v $dA1 $du1 $dv1) (der_prop_type_eq _ $s $A $u $v $dA2 $du2 $dv2)
  ↪ cong_eq
       (convertR $Γ $T1 $T2 $H $dA1 $dA2)
       (heq_trans
         (heq_symm (heq_of_transport (τ (Concat $Γ $T1) $du1) (convert_T (Concat $Γ $T1) (inv_sort $du1) $dA1)))
         (heq_trans
           (convertR $Γ $T1 $T2 $H $du1 $du2)
           (heq_of_transport (τ (Concat $Γ $T2) $du2) (convert_T (Concat $Γ $T2) (inv_sort $du2) $dA2))))
       (heq_trans
         (heq_symm (heq_of_transport (τ (Concat $Γ $T1) $dv1) (convert_T (Concat $Γ $T1) (inv_sort $dv1) $dA1)))
         (heq_trans
           (convertR $Γ $T1 $T2 $H $dv1 $dv2)
           (heq_of_transport (τ (Concat $Γ $T2) $dv2) (convert_T (Concat $Γ $T2) (inv_sort $dv2) $dA2))))


// λ-calculus
with convertR $Γ $T1 $T2 $H (der_abs _ $s $s' $A $t $B $dA1 _ $dt1) (der_abs _ $s $s' $A $t $B $dA2 _ $dt2)
  ↪ cong_lambda
       (λ a, τ_T (TPush (Concat $Γ $T1) $s $A $dA1 a) (inv_sort $dt1))
       (λ a, τ_T (TPush (Concat $Γ $T2) $s $A $dA2 a) (inv_sort $dt2))
       (λ a, τ (TPush (Concat $Γ $T1) $s $A $dA1 a) $dt1)
       (λ a, τ (TPush (Concat $Γ $T2) $s $A $dA2 a) $dt2)
       (convertR $Γ $T1 $T2 $H $dA1 $dA2)
       (λ p, convertR $Γ (COPush $T1 $dA1 (projT1 p)) (COPush $T2 $dA2 (projT2 p))
                      (PCPush $H $dA1 $dA2 (projHEq p)) (inv_sort $dt1) (inv_sort $dt2))
       (λ p, convertR $Γ (COPush $T1 $dA1 (projT1 p)) (COPush $T2 $dA2 (projT2 p))
                      (PCPush $H $dA1 $dA2 (projHEq p)) $dt1 $dt2)

// Type conversion
with convertR $Γ $T1 $T2 $H (der_sort _ $s $dΓ) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_sort _ $s $dΓ) $dX $deq
with convertR $Γ $T1 $T2 $H (der_prod _ $s $s' $A $B $dA $dB) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_prod _ $s $s' $A $B $dA $dB) $dX $deq
with convertR $Γ $T1 $T2 $H (der_sigma _ $s $s' $A $B $dA $dB) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_sigma _ $s $s' $A $B $dA $dB) $dX $deq
with convertR $Γ $T1 $T2 $H (der_prop_type_eq _ $s $A $u $v $dA $du $dv) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_prop_type_eq _ $s $A $u $v $dA $du $dv) $dX $deq
with convertR $Γ $T1 $T2 $H (der_var _ $id $dΓ) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_var _ $id $dΓ) $dX $deq
with convertR $Γ $T1 $T2 $H (der_abs _ $s $s' $A $t $B $dA $dB $dt) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_abs _ $s $s' $A $t $B $dA $dB $dt) $dX $deq
with convertR $Γ $T1 $T2 $H (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du) $dX $deq
with convertR $Γ $T1 $T2 $H (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv) $dX $deq
with convertR $Γ $T1 $T2 $H (der_π1 _ $s $s' $p $A $B $dA $dB $dp) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_π1 _ $s $s' $p $A $B $dA $dB $dp) $dX $deq
with convertR $Γ $T1 $T2 $H (der_π2 _ $s $s' $p $A $B $dA $dB $dp) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_π2 _ $s $s' $p $A $B $dA $dB $dp) $dX $deq
with convertR $Γ $T1 $T2 $H (der_refl _ $s $u $A $dA $du) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_refl _ $s $u $A $dA $du) $dX $deq
with convertR $Γ $T1 $T2 $H (der_uip _ $s $e1 $e2 $u $v $A $de1 $de2) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_uip _ $s $e1 $e2 $u $v $A $de1 $de2) $dX $deq
with convertR $Γ $T1 $T2 $H (der_funext _ $s $s' $f $g $A $e $B $dA $dB $df $dg $de) (der_type_conv _ _ _ _ _ $dX $deq)
  ↪ convertTypeConversion $Γ $T1 $T2 $H (der_funext _ $s $s' $f $g $A $e $B $dA $dB $df $dg $de) $dX $deq
// Symmetric cases
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_sort _ $s $dΓ)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_sort _ $s $dΓ) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_prod _ $s $s' $A $B $dA $dB)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_prod _ $s $s' $A $B $dA $dB) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_sigma _ $s $s' $A $B $dA $dB)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_sigma _ $s $s' $A $B $dA $dB) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_prop_type_eq _ $s $A $u $v $dA $du $dv)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_prop_type_eq _ $s $A $u $v $dA $du $dv) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_var _ $id $dΓ)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_var _ $id $dΓ) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_abs _ $s $s' $A $t $B $dA $dB $dt)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_abs _ $s $s' $A $t $B $dA $dB $dt) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_π1 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_π1 _ $s $s' $p $A $B $dA $dB $dp) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_π2 _ $s $s' $p $A $B $dA $dB $dp) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_refl _ $s $u $A $dA $du)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_refl _ $s $u $A $dA $du) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_uip _ $s $e1 $e2 $u $v $A $de1 $de2)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_uip _ $s $e1 $e2 $u $v $A $de1 $de2) $dX $deq)
with convertR $Γ $T1 $T2 $H (der_type_conv _ _ _ _ _ $dX $deq) (der_funext _ $s $s' $f $g $A $e $B $dA $dB $df $dg $de)
  ↪ heq_symm (convertTypeConversion $Γ $T2 $T1 (PCSymm $H) (der_funext _ $s $s' $f $g $A $e $B $dA $dB $df $dg $de) $dX $deq)
;
