
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.TranslationDefinition;

// Compatibility with operations on derivations

// Translation of shifting
symbol τ_shift0T_eq (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
                    (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                    (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                    (a : ε _ (τ_T Γ dA)) :
  ε _ (eq _ (u (τ_s s))
      (τ_T Γ dT)
      (τ_T (TPush Γ s' A dA a) (der_shift0 dA (τ_dΓ Γ) dT)));
symbol τ_shift0T (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
                 (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                 (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                 (a : ε _ (τ_T Γ dA)) ≔
  transport (τ_shift0T_eq Γ dT dA a);
symbol τ_shift0T' (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
                  (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                  (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                  (a : ε _ (τ_T Γ dA)) ≔
  transport (inv_eq (τ_shift0T_eq Γ dT dA a));

symbol τ_shift0_eq (Γ : TContext) {s s' : ETT.Sort} {t T A : ETT.Term}
                   (dΓ : der_context (τ_Γ Γ))
                   (dt : der (τ_Γ Γ) t T s)
                   (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                   (a : ε _ (τ_T Γ dA)) :
  H (τ Γ dt)
    (τ (TPush Γ s' A dA a) (der_shift0 dA dΓ dt));

symbol τ_shift1T_eq (Γ : TContext) {s sa sb : ETT.Sort} {T A B : ETT.Term}
                    (dT : der (Push A sa (τ_Γ Γ)) T (ETT.tsort s) (ETT.snext s))
                    (dA : der (τ_Γ Γ) A (ETT.tsort sa) (ETT.snext sa))
                    (dB : der (τ_Γ Γ) B (ETT.tsort sb) (ETT.snext sb))
                    (a : ε _ (τ_T Γ dA)) (b : ε _ (τ_T Γ dB)) :
  ε _ (eq _ (u (τ_s s))
      (τ_T (TPush Γ sa A dA a) dT)
      (τ_T (TPush (TPush Γ sb B dB b) sa (Shift A) (der_shift0 dB (τ_dΓ Γ) dA) (τ_shift0T Γ dA dB b a)) (der_shift1 dA dB (τ_dΓ Γ) dT)));
symbol τ_shift1T (Γ : TContext) {s sa sb : ETT.Sort} {T A B : ETT.Term}
                 (dT : der (Push A sa (τ_Γ Γ)) T (ETT.tsort s) (ETT.snext s))
                 (dA : der (τ_Γ Γ) A (ETT.tsort sa) (ETT.snext sa))
                 (dB : der (τ_Γ Γ) B (ETT.tsort sb) (ETT.snext sb))
                 (a : ε _ (τ_T Γ dA)) (b : ε _ (τ_T Γ dB)) ≔
  transport (τ_shift1T_eq Γ dT dA dB a b);
symbol τ_shift1T' (Γ : TContext) {s sa sb : ETT.Sort} {T A B : ETT.Term}
                  (dT : der (Push A sa (τ_Γ Γ)) T (ETT.tsort s) (ETT.snext s))
                  (dA : der (τ_Γ Γ) A (ETT.tsort sa) (ETT.snext sa))
                  (dB : der (τ_Γ Γ) B (ETT.tsort sb) (ETT.snext sb))
                  (a : ε _ (τ_T Γ dA)) (b : ε _ (τ_T Γ dB)) ≔
  transport (inv_eq (τ_shift1T_eq Γ dT dA dB a b));

// Translation of substitution
symbol τ_substT_eq (Γ : TContext) {s s' : ETT.Sort} {A B a : ETT.Term}
                   (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (da : der (τ_Γ Γ) a A s) :
  ε _ (eq _ (u (τ_s s'))
    (τ_T (TPush Γ s A (inv_sort (τ_dΓ Γ) da) (τ Γ da)) dB)
    (τ_T Γ (substitution (τ_dΓ Γ) dB da)));
symbol τ_substT (Γ : TContext) {s s' : ETT.Sort} {A B a : ETT.Term}
                (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (da : der (τ_Γ Γ) a A s) ≔
  transport (τ_substT_eq Γ dB da);
symbol τ_substT' (Γ : TContext) {s s' : ETT.Sort} {A B a : ETT.Term}
                 (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (da : der (τ_Γ Γ) a A s) ≔
  transport (inv_eq (τ_substT_eq Γ dB da));

symbol τ_subst_eq (Γ : TContext) {s s' : ETT.Sort} {A B b a : ETT.Term}
                  (db : der (Push A s (τ_Γ Γ)) b B s')
                  (da : der (τ_Γ Γ) a A s) :
  HEq (τ_s s')
    (τ_T (TPush Γ s A (inv_sort (τ_dΓ Γ) da) (τ Γ da)) (inv_sort (τ_dΓ (TPush Γ _ _ (inv_sort (τ_dΓ Γ) da) (τ Γ da))) db))
    (τ_T Γ (inv_sort (τ_dΓ Γ) (substitution (τ_dΓ Γ) db da)))
    (τ (TPush Γ s A (inv_sort (τ_dΓ Γ) da) (τ Γ da)) db)
    (τ Γ (substitution (τ_dΓ Γ) db da));

// Préservation of head type

// Translation of product
symbol τ_fun_eq (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
                (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                (df : der (τ_Γ Γ) (ETT.tfun A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) :
  ε _ (eq _ (u (τ_s (ETT.smax s s')))
    (τ_T Γ df)
    (P (τ_s s) (τ_s s') (τ_T Γ dA) (λ a, τ_T (TPush Γ s A dA a) dB)));
symbol τ_fun (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
             (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (df : der (τ_Γ Γ) (ETT.tfun A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport (τ_fun_eq Γ dA dB df);
symbol τ_fun' (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
              (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
              (df : der (τ_Γ Γ) (ETT.tfun A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport (inv_eq (τ_fun_eq Γ dA dB df));

// Translation of pairs
symbol τ_sum_eq (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
                (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                (dp : der (τ_Γ Γ) (ETT.tsum A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) :
  ε _ (eq _ (u (τ_s (ETT.smax s s')))
        (τ_T Γ dp)
        (S (τ_s s) (τ_s s') (τ_T Γ dA) (λ a, τ_T (TPush Γ s A dA a) dB)));
symbol τ_sum (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
             (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
             (dp : der (τ_Γ Γ) (ETT.tsum A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport (τ_sum_eq Γ dA dB dp);
symbol τ_sum' (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
              (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s)) (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
              (dp : der (τ_Γ Γ) (ETT.tsum A B) (ETT.tsort (ETT.smax s s')) (ETT.snext (ETT.smax s s'))) ≔
  transport (inv_eq (τ_sum_eq Γ dA dB dp));

// Translation of equality
symbol τ_equality_eq (Γ : TContext) {s : ETT.Sort} {A a a' : ETT.Term}
                     (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                     (da : der (τ_Γ Γ) a A s) (da' : der (τ_Γ Γ) a' A s)
                     (de : der (τ_Γ Γ) (ETT.teq A a a') (ETT.tsort s) (ETT.snext s)) :
  ε _ (eq _ (u (τ_s s))
        (τ_T Γ de)
        (eq (τ_s s) (τ_T Γ dA)
            (transport (convert_T Γ (inv_sort (τ_dΓ Γ) da)  dA) (τ Γ da))
            (transport (convert_T Γ (inv_sort (τ_dΓ Γ) da') dA) (τ Γ da'))));
symbol τ_equality (Γ : TContext) {s : ETT.Sort} {A a a' : ETT.Term}
                  (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                  (da : der (τ_Γ Γ) a A s) (da' : der (τ_Γ Γ) a' A s)
                  (de : der (τ_Γ Γ) (ETT.teq A a a') (ETT.tsort s) (ETT.snext s)) ≔
  transport (τ_equality_eq Γ dA da da' de);
symbol τ_equality' (Γ : TContext) {s : ETT.Sort} {A a a' : ETT.Term}
                   (dA : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                   (da : der (τ_Γ Γ) a A s) (da' : der (τ_Γ Γ) a' A s)
                   (de : der (τ_Γ Γ) (ETT.teq A a a') (ETT.tsort s) (ETT.snext s)) ≔
  transport (inv_eq (τ_equality_eq Γ dA da da' de));

