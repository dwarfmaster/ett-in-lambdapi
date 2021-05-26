
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.TranslationDefinition;

// Translation of shifting
symbol τ_shift0T_eq (Γ : TContext) {s s' : ETT.Sort} {T A : ETT.Term}
                    (dT : der (τ_Γ Γ) T (ETT.tsort s) (ETT.snext s))
                    (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                    (a : ε _ (τ_T Γ dA)) :
  ε _ (eq _ (u (τ_s s))
      (τ_T Γ dT)
      (τ_T (TPush Γ s' A dA a) (der_shift0 (Push A s' (τ_Γ Γ)) dT)));
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
                   (dt : der (τ_Γ Γ) t T s)
                   (dA : der (τ_Γ Γ) A (ETT.tsort s') (ETT.snext s'))
                   (a : ε _ (τ_T Γ dA)) :
  H (τ Γ dt)
    (τ (TPush Γ s' A dA a) (der_shift0 (Push A s' (τ_Γ Γ)) dt));

symbol τ_shift1T_eq (Γ : TContext) {s sa sb : ETT.Sort} {T A B : ETT.Term}
                    (dT : der (Push A sa (τ_Γ Γ)) T (ETT.tsort s) (ETT.snext s))
                    (dA : der (τ_Γ Γ) A (ETT.tsort sa) (ETT.snext sa))
                    (dB : der (τ_Γ Γ) B (ETT.tsort sb) (ETT.snext sb))
                    (a : ε _ (τ_T Γ dA)) (b : ε _ (τ_T Γ dB)) :
  ε _ (eq _ (u (τ_s s))
      (τ_T (TPush Γ sa A dA a) dT)
      (τ_T (TPush (TPush Γ sb B dB b) sa (Shift A) (der_shift0 (Push B sb (τ_Γ Γ)) dA) (τ_shift0T Γ dA dB b a)) (der_shift1 B sb dT)));
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

// Translation of substitution
symbol τ_substT_eq (Γ : TContext) {s s' : ETT.Sort} {A B a : ETT.Term}
                   (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s')) (da : der (τ_Γ Γ) a A s) :
  ε _ (eq _ (u (τ_s s'))
    (τ_T (TPush Γ s A (inv_sort da) (τ Γ da)) dB)
    (τ_T Γ (substitution dB da)));
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
    (τ_T (TPush Γ s A (inv_sort da) (τ Γ da)) (inv_sort db))
    (τ_T Γ (inv_sort (substitution db da)))
    (τ (TPush Γ s A (inv_sort da) (τ Γ da)) db)
    (τ Γ (substitution db da));

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
            (transport (convert_T Γ (inv_sort da)  dA) (τ Γ da))
            (transport (convert_T Γ (inv_sort da') dA) (τ Γ da'))));
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

// Translation of context conversion
symbol τ_conv_in_ctx (Γ : TContext) {s s' : ETT.Sort} {A A' t B : ETT.Term}
                     (deqA : der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A A')
                     (dB : der (Push A s (τ_Γ Γ)) t B s')
                     (a : ε _ (τ Γ (inv_eq_t1 deqA)))
                     : HEq (τ_s s')
                        (τ_T (TPush Γ s A  (inv_eq_t1 deqA) a) (inv_sort dB))
                        (τ_T (TPush Γ s A' (inv_eq_t2 deqA) (transport (τ_eqT Γ deqA) a))
                             (inv_sort (der_conv_in_ctx (τ_Γ Γ) s s' A A' t B deqA dB)))
                        (τ (TPush Γ s A  (inv_eq_t1 deqA) a) dB)
                        (τ (TPush Γ s A' (inv_eq_t2 deqA) (transport (τ_eqT Γ deqA) a))
                           (der_conv_in_ctx (τ_Γ Γ) s s' A A' t B deqA dB));
symbol τ_convT_in_ctx (Γ : TContext) {s s' : ETT.Sort} {A A' B : ETT.Term}
                      (deqA : der_eq (τ_Γ Γ) (ETT.snext s) (ETT.tsort s) A A')
                      (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                      (a : ε _ (τ Γ (inv_eq_t1 deqA)))
                      : ε _ (eq (τ_s (ETT.snext s')) (u (τ_s s'))
                               (τ_T (TPush Γ s A  (inv_eq_t1 deqA) a) dB)
                               (τ_T (TPush Γ s A' (inv_eq_t2 deqA) (transport (τ_eqT Γ deqA) a))
                                  (der_conv_in_ctx (τ_Γ Γ) s (ETT.snext s') A A' B (ETT.tsort s') deqA dB))) ≔
  heq_to_eq (τ_conv_in_ctx Γ deqA dB a);

symbol τ_transport_in_ctx (Γ : TContext) {s s' : ETT.Sort} {A B t : ETT.Term}
                          (dA dA' : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                          (dt : der (Push A s (τ_Γ Γ)) t B s')
                          (p : ε _ (eq _ (u (τ_s s)) (τ_T Γ dA) (τ_T Γ dA')))
                          (a : ε _ (τ_T Γ dA))
                          : HEq (τ_s s')
                              (τ_T (TPush Γ s A dA a) (inv_sort dt))
                              (τ_T (TPush Γ s A dA' (transport p a)) (inv_sort dt))
                              (τ (TPush Γ s A dA a) dt)
                              (τ (TPush Γ s A dA' (transport p a)) dt);
symbol τ_T_transport_in_ctx (Γ : TContext) {s s' : ETT.Sort} {A B : ETT.Term}
                            (dA dA' : der (τ_Γ Γ) A (ETT.tsort s) (ETT.snext s))
                            (dB : der (Push A s (τ_Γ Γ)) B (ETT.tsort s') (ETT.snext s'))
                            (p : ε _ (eq _ (u (τ_s s)) (τ_T Γ dA) (τ_T Γ dA')))
                            (a : ε _ (τ_T Γ dA))
                            : ε _ (eq _ (u (τ_s s'))
                                (τ_T (TPush Γ s A dA a) dB)
                                (τ_T (TPush Γ s A dA' (transport p a)) dB)) ≔
  heq_to_eq (τ_transport_in_ctx Γ dA dA' dB p a);
