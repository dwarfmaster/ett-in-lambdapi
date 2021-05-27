
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

symbol magic {s : Sort} (A : U s) : ε s A;

// Helper
symbol heq_of_conversion (Γ : TContext) {s : ETT.Sort} {a A B : ETT.Term}
                         (da : der (τ_Γ Γ) a A s) (deq : der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A B)
                         : H (τ Γ da) (τ Γ (der_type_conv (τ_Γ Γ) a A B s da deq)) ≔
  heq_trans
   (heq_of_transport (τ Γ da) (convert_T Γ (inv_sort da) (inv_eq_t1 deq)))
   (heq_of_transport (transport (convert_T Γ (inv_sort da) (inv_eq_t1 deq)) (τ Γ da)) (τ_eqT Γ deq));

rule τ_eq $Γ (der_eq_cong_tfun _ $s _ $A1 $A2 _ _ $deqA $deqB $dB1 $dB2)
  ↪ cong_prod
       (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dB1)
       (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dB2)
       (τ_eq $Γ $deqA)
       (λ p, heq_trans
         (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dB1 (inv_eq_t1 $deqB))
         (heq_trans
           (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
           (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) $dB2)))
with τ_eq $Γ (der_eq_cong_tabs _ $s $s' $A1 $A2 $B1 $B2 _ $t2 $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ heq_trans
       (cong_lambda
         (λ a, τ_T (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) (inv_sort $dt1))
         (λ a, τ_T (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) (inv_sort $dt2))
         (λ a, τ (TPush $Γ $s $A1 (inv_eq_t1 $deqA) a) $dt1)
         (λ a, τ (TPush $Γ $s $A2 (inv_eq_t2 $deqA) a) $dt2)
         (τ_eq $Γ $deqA)
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) (inv_sort $dt1) (inv_eq_t1 $deqB))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqB)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqB) (inv_sort $dt2))))
         (λ p, heq_trans
           (convert (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $dt1 (inv_eq_t1 $deqt))
           (heq_trans
             (τ_eq (TPush $Γ $s $A1 (inv_eq_t1 $deqA) (projT1 p)) $deqt)
             (convertR $Γ (PCPush (PCEmpty $Γ) (inv_eq_t1 $deqA) (inv_eq_t2 $deqA) (projHEq p)) (inv_eq_t2 $deqt) $dt2))))
       (heq_of_conversion $Γ
         (der_abs (τ_Γ $Γ) $s $s' $A2 $t2 $B2 (inv_eq_t2 $deqA) $dB2 $dt2)
         (der_eq_symm _ _ _ _ _ (der_eq_cong_tfun (τ_Γ $Γ) $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)))
;
