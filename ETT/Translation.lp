
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.Congruences;
require open ETT.TContext;

// Translation of types
rule τ _ (der_sort _ $s _)
  ↪ u (τ_s $s)
with τ $Γ (der_prod _ $s $s' $A _ $dA $dB)
  ↪ P (τ_s $s) (τ_s $s') (τ_T $Γ $dA)
       (λ a, τ_T (TPush $Γ $s $A $dA a) $dB)
with τ $Γ (der_sigma _ $s $s' $A _ $dA $dB)
  ↪ S (τ_s $s) (τ_s $s') (τ_T $Γ $dA)
       (λ a, τ_T (TPush $Γ $s $A $dA a) $dB)
with τ $Γ (der_prop_type_eq _ $s _ _ _ $dA $du $dv)
  ↪ let pu ≔ convert_T $Γ (inv_sort $du) $dA in
     let pv ≔ convert_T $Γ (inv_sort $dv) $dA in
     eq (τ_s $s) (τ_T $Γ $dA) (transport pu (τ $Γ $du)) (transport pv (τ $Γ $dv))
;

// Translation of terms
rule τ $Γ (der_var _ $id $dΓ)
  ↪ let p ≔ convert_T $Γ (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ)) (der_shift $id $dΓ (der_getΓ $id $dΓ)) in
     transport p (tgetShift $id $Γ)
with τ $Γ (der_type_conv _ _ _ _ _ $du $deq)
  ↪ let pAB ≔ τ_eqT $Γ $deq in
     let p ≔ convert_T $Γ (inv_sort $du) (inv_eq_t1 $deq) in
     transport pAB (transport p (τ $Γ $du))

with τ $Γ (der_abs _ $s _ $A _ _ $dA _ $dt)
  ↪ λ a, τ (TPush $Γ $s $A $dA a) $dt
with τ $Γ (der_app _ _ _ _ _ _ _ _ $dB $dt $du)
  ↪ let f ≔ τ_fun $Γ (inv_sort $du) $dB (inv_sort $dt) (τ $Γ $dt) in
     τ_substT $Γ $dB $du (f (τ $Γ $du))

with τ $Γ (der_pair _ $s $s' _ $A _ _ _ $du $dB $dv)
  ↪ let pv ≔ convert_T $Γ (inv_sort $dv) (substitution $dB $du) in
     mkS (τ_s $s) (τ_s $s') (τ_T $Γ (inv_sort $du)) (λ a, τ_T (TPush $Γ $s $A (inv_sort $du) a) $dB)
         (τ $Γ $du) (τ_substT' $Γ $dB $du (transport pv (τ $Γ $dv)))
with τ $Γ (der_π1 _ $s $s' _ $A _ $dA $dB $dp)
  ↪ let pr ≔ τ_sum $Γ $dA $dB (inv_sort $dp) (τ $Γ $dp) in
     proj1 (τ_s $s) (τ_s $s') (τ_T $Γ $dA) (λ a, τ_T (TPush $Γ $s $A $dA a) $dB) pr

// Equality
with τ $Γ (der_refl _ $s _ _ $dA $du)
  ↪ let p ≔ convert_T $Γ (inv_sort $du) $dA in
     refl (τ_s $s) (τ_T $Γ $dA) (transport p (τ $Γ $du))
;


// der_π2 needs τ ... (der_π1 ...) to be defined to type
rule τ $Γ (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ let pr ≔ τ_sum $Γ $dA $dB (inv_sort $dp) (τ $Γ $dp) in
     τ_substT $Γ $dB (der_π1 (τ_Γ $Γ) $s $s' $p $A $B $dA $dB $dp)
       (proj2 (τ_s $s) (τ_s $s') (τ_T $Γ $dA) (λ a, τ_T (TPush $Γ $s $A $dA a) $dB) pr)
;
