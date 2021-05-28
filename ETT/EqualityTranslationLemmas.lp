
require open ETT.ITT;
require open ETT.ILemmas;
require      ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.HEq;
require open ETT.Inversions;
require open ETT.TranslationDefinition;
require open ETT.Translation;

// Helper
symbol heq_of_conversion (Γ : TContext) {s : ETT.Sort} {a A B : ETT.Term}
                         (da : der (τ_Γ Γ) a A s) (deq : der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A B)
                         : H (τ Γ da) (τ Γ (der_type_conv (τ_Γ Γ) a A B s da deq)) ≔
  heq_trans
   (heq_of_transport (τ Γ da) (convert_T Γ (inv_sort da) (inv_eq_t1 deq)))
   (heq_of_transport (transport (convert_T Γ (inv_sort da) (inv_eq_t1 deq)) (τ Γ da)) (τ_eqT Γ deq));
