
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

// convert_T
rule convert_T $Γ $d1 $d2
  ↪ heq_to_eq (convert $Γ $d1 $d2);

// convert
rule convert $Γ $d1 $d2
  ↪ convertR $Γ (COTail $Γ) (COTail $Γ) (PCEmpty $Γ) $d1 $d2;

// convert
rule convertR _ _ _ _ (der_sort _ $s _) (der_sort _ _ _)
  ↪ heq_refl (u (snext (τ_s $s))) (u (τ_s $s))
with convertR $Γ $T1 $T2 $H (der_prod _ $s $s' $A $B $dA1 $dB1) (der_prod _ $s $s' $A $B $dA2 $dB2)
  ↪ cong_prod
       (λ a, τ_T (TPush (Concat $Γ $T1) $s $A $dA1 a) $dB1)
       (λ a, τ_T (TPush (Concat $Γ $T2) $s $A $dA2 a) $dB2)
       (convertR $Γ $T1 $T2 $H $dA1 $dA2)
       (λ p, convertR $Γ (COPush $T1 $dA1 (projT1 p)) (COPush $T2 $dA2 (projT2 p))
                      (PCPush $H $dA1 $dA2 (projHEq p)) $dB1 $dB2)
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
;
