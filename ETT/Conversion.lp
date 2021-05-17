
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.Congruences;
require open ETT.TContext;
require open ETT.Translation;

// convert_T
rule convert_T $Γ $d1 $d2
  ↪ heq_to_eq (convert $Γ $d1 $d2);

// convert
rule convert _ (der_sort _ $s _) (der_sort _ _ _)
  ↪ heq_refl (u (snext (τ_s $s))) (u (τ_s $s))
with convert $Γ (der_prod _ $s $s' $A $B $dA $dB) (der_prod _ $s $s' $A $B $dA' $dB')
  ↪ eq_to_heq (eq_prod
       (λ a, τ_T (TPush $Γ $s $A $dA  a) $dB)
       (λ a, τ_T (TPush $Γ $s $A $dA' a) $dB')
       (convert_T $Γ $dA $dA')
       (λ a, (@trans_eq _
         (u (τ_s $s'))
         (τ_T (TPush $Γ $s $A $dA a) $dB)
         (τ_T (TPush $Γ $s $A $dA' (transport (convert_T $Γ $dA $dA') a)) $dB)
         (τ_T (TPush $Γ $s $A $dA' (transport (convert_T $Γ $dA $dA') a)) $dB')
         (τ_T_transport_in_ctx $Γ $dA $dA' $dB (convert_T $Γ $dA $dA') a)
         (convert_T (TPush $Γ $s $A $dA' (transport (convert_T $Γ $dA $dA') a)) $dB $dB'))))
// with convert $Γ (der_abs _ $s $s' $A $t $B $dA $dB $dt) (der_abs _ $s $s' $A $t $B $dA' $dB' $dt')
//   ↪
;
