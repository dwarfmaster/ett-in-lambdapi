
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
;
