
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require ETT.Inversions as I;
require open ETT.HEq;
require open ETT.TranslationDefinition;

// Translation of shifting
symbol τ_shift_eq (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
                  (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                  (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                  (a : ε _ (τ_T Γ dA)) :
  ε _ (eq _ (u (τ_s s))
      (τ_T Γ dT)
      (τ_T (TPush Γ s' A dA a) (der_shift1 (Push A s' (τ_Γ Γ)) T (ETT.tsort s) (ETT.snext s) dT)));
symbol τ_shift (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
               (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
               (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
               (a : ε _ (τ_T Γ dA)) ≔
  transport (τ_shift_eq Γ dT dA a);
symbol τ_shift' (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
                (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                (a : ε _ (τ_T Γ dA)) ≔
  transport (inv_eq (τ_shift_eq Γ dT dA a));
