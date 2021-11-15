
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require open ETT.XCongruences;
require ETT.main as M;
require ETT.TranslationDefinition as Tr;
require ETT.Inversions as I;

// Helpers
builtin "0" ≔ db0;
builtin "+1" ≔ dbsucc;
symbol magic_der (Γ : Context) (t T : Term) (s : Sort) : der Γ t T s;
symbol magic_der' {Γ : Context} (_ : der_context Γ) (t T : Term) (s : Sort) : der Γ t T s;
symbol magic_der_eq (Γ : Context) (t1 t2 T : Term) (s : Sort) : der_eq Γ s T t1 t2;
symbol magic_der_eq' {Γ : Context} (_ : der_context Γ) (t1 t2 T : Term) (s : Sort) : der_eq Γ s T t1 t2;

symbol getΓ {Γ : Context} : der_context Γ → Context ≔ λ _, Γ;

symbol dprod {Γ : Context} {A B : Term} {s s' : Sort}
  : der_context Γ
  → der Γ A (tsort s) (snext s)
  → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
  → der Γ (tfun A B) (tsort (smax s s')) (snext (smax s s')) ≔
  λ dΓ dA dB, der_prod Γ s s' A B dA (dB (pushΓ dA dΓ));
symbol dabs {Γ : Context} {A B t : Term} {s s' : Sort}
  : der_context Γ
  → der Γ A (tsort s) (snext s)
  → (der_context (Push A s Γ) → der (Push A s Γ) t B s')
  → der Γ (tabs A B t) (tfun A B) (smax s s') ≔
  λ dΓ dA dt, der_abs Γ s s' A t B dA (I.inv_sort (pushΓ dA dΓ) (dt (pushΓ dA dΓ))) (dt (pushΓ dA dΓ));
symbol dapp {Γ : Context} {A B f a : Term} {s s' : Sort}
  : der_context Γ
  → der Γ A (tsort s) (snext s)
  → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
  → der Γ f (tfun A B) (smax s s')
  → der Γ a A s
  → der Γ (tapp A B f a) (apply1 B a) s' ≔
  λ dΓ dA dB df da, der_app Γ s s' A f a B dA (dB (pushΓ dA dΓ)) df da;
symbol deta {Γ : Context} {s s' : Sort} {A f B : Term}
            : der_context Γ
            → der Γ A (tsort s) (snext s)
            → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
            → der Γ f (tfun A B) (smax s s')
            → der_eq Γ (smax s s') (tfun A B) (tabs A B (tapp (Shift A) (Shift1 B) (Shift f) (var 0))) f ≔
  λ dΓ dA dB df, der_eq_eta Γ s s' A f B dA (dB (pushΓ dA dΓ)) df;
symbol dcong_tabs_body {Γ : Context} {s s' : Sort} {A B t1 t2 : Term}
                       : der_context Γ
                       → der Γ A (tsort s) (snext s)
                       → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
                       → (der_context (Push A s Γ) → der_eq (Push A s Γ) s' B t1 t2)
                       → der_eq Γ (smax s s') (tfun A B) (tabs A B t1) (tabs A B t2) ≔
  λ dΓ dA dB dt,
    der_eq_cong_tabs Γ s s' A A B B t1 t2
                     (der_eq_refl Γ (snext s) A (tsort s) dA)
                     (der_eq_refl (Push A s Γ) (snext s') B (tsort s') (dB (pushΓ dA dΓ)))
                     (dt (pushΓ dA dΓ))
                     (dB (pushΓ dA dΓ)) (dB (pushΓ dA dΓ))
                     (I.inv_eq_t1 (pushΓ dA dΓ) (dt (pushΓ dA dΓ))) (I.inv_eq_t2 (pushΓ dA dΓ) (dt (pushΓ dA dΓ)));
symbol dcong_tapp {Γ : Context} {s s' : Sort} {A1 A2 B1 B2 f1 f2 a1 a2 : Term}
                  : der_context Γ
                  → der_eq Γ (snext s) (tsort s) A1 A2
                  → (der_context (Push A1 s Γ) → der_eq (Push A1 s Γ) (snext s') (tsort s') B1 B2)
                  → der_eq Γ (smax s s') (tfun A1 B1) f1 f2
                  → der_eq Γ s A1 a1 a2
                  → der_eq Γ s' (apply1 B1 a1) (tapp A1 B1 f1 a1) (tapp A2 B2 f2 a2) ≔
  λ dΓ deqA deqB deqf deqa,
    der_eq_cong_tapp Γ s s' A1 A2 B1 B2 f1 f2 a1 a2
                     deqA (deqB (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ)) deqf deqa
                     (I.inv_eq_t1 (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ) (deqB (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ)))
                     (convert_der (ECPush (EC0 dΓ) (I.inv_eq_t1 dΓ deqA) (I.inv_eq_t2 dΓ deqA) deqA)
                                  (I.inv_eq_t2 (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ) (deqB (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ))))
                     (I.inv_eq_t1 dΓ deqf)
                     (der_type_conv Γ f2 (tfun A1 B1) (tfun A2 B2) (smax s s') (I.inv_eq_t2 dΓ deqf)
                                    (der_eq_cong_tfun Γ s s' A1 A2 B1 B2
                                       deqA (deqB (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ))
                                       (I.inv_eq_t1 (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ) (deqB (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ)))
                                       (convert_der (ECPush (EC0 dΓ) (I.inv_eq_t1 dΓ deqA) (I.inv_eq_t2 dΓ deqA) deqA)
                                                    (I.inv_eq_t2 (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ) (deqB (pushΓ (I.inv_eq_t1 dΓ deqA) dΓ))))))
                     (I.inv_eq_t1 dΓ deqa)
                     (der_type_conv Γ a2 A1 A2 s (I.inv_eq_t2 dΓ deqa) deqA);
symbol dcong_teq {Γ : Context} {s : Sort} {A1 A2 a1 a2 b1 b2 : Term}
                 : der_context Γ
                 → der_eq Γ (snext s) (tsort s) A1 A2
                 → der_eq Γ s A1 a1 a2
                 → der_eq Γ s A1 b1 b2
                 → der_eq Γ (snext s) (tsort s) (teq A1 a1 b1) (teq A2 a2 b2) ≔
  λ dΓ deqA deqa deqb,
    der_eq_cong_teq Γ s A1 A2 a1 a2 b1 b2
                    deqA deqa deqb
                    (I.inv_eq_t1 dΓ deqa)
                    (der_type_conv Γ a2 A1 A2 s (I.inv_eq_t2 dΓ deqa) deqA)
                    (I.inv_eq_t1 dΓ deqb)
                    (der_type_conv Γ b2 A1 A2 s (I.inv_eq_t2 dΓ deqb) deqA);
symbol fromCong {Γ : Context} {t1 t2 T : Term} {s : Sort}
       : der_context Γ → der_eq Γ s T t1 t2 → der Γ (trefl T t1) (teq T t1 t2) s ≔
  λ dΓ deq,
    der_type_conv Γ (trefl T t1) (teq T t1 t1) (teq T t1 t2) s
      (der_refl Γ s t1 T (I.inv_sort dΓ (I.inv_eq_t1 dΓ deq)) (I.inv_eq_t1 dΓ deq))
      (der_eq_cong_teq Γ s T T t1 t1 t1 t2
        (der_eq_refl Γ (snext s) T (tsort s) (I.inv_sort dΓ (I.inv_eq_t1 dΓ deq)))
        (der_eq_refl Γ s t1 T (I.inv_eq_t1 dΓ deq))
        deq
        (I.inv_eq_t1 dΓ deq) (I.inv_eq_t1 dΓ deq)
        (I.inv_eq_t1 dΓ deq) (I.inv_eq_t2 dΓ deq));

// Very simple test
symbol poly_id (s : Sort) : Term ≔
  tabs (tsort s) (tfun (var 0) (var 1)) // A
  (tabs (var 0) (var 1) (var 0)); // λ x. x
symbol poly_id_type (s : Sort) : Term ≔
  tfun (tsort s) (tfun (var 0) (var 1));
symbol poly_id_der (s : Sort) : der Empty (poly_id s) (poly_id_type s) (smax (snext s) (smax s s)) ≔
  dabs der_context_empty (der_sort Empty s)
    (λ dΓ, dabs dΓ (der_var (getΓ dΓ) 0)
      (λ dΓ, der_var (getΓ dΓ) 0));

compute Tr.τ Tr.TEmpty (I.inv_sort der_context_empty (poly_id_der s0));
compute Tr.τ Tr.TEmpty (poly_id_der s0);

// Transport
symbol trans (s : Sort) : Term ≔
  tabs (tsort s) (tfun (tsort s) (tfun (teq (tsort s) (var 1) (var 0)) (tfun (var 2) (var 2))))
  (tabs (tsort s) (tfun (teq (tsort s) (var 1) (var 0)) (tfun (var 2) (var 2)))
  (tabs (teq (tsort s) (var 1) (var 0)) (tfun (var 2) (var 2))
  (tabs (var 2) (var 2) (var 0))));
symbol trans_type (s : Sort) : Term ≔
  tfun (tsort s) (tfun (tsort s) (tfun (teq (tsort s) (var 1) (var 0)) (tfun (var 2) (var 2))));
symbol trans_der (s : Sort) : der Empty (trans s) (trans_type s) _ ≔
  dabs der_context_empty (der_sort Empty s)
    (λ dΓ, dabs dΓ (der_sort (getΓ dΓ) s)
      (λ dΓ, dabs dΓ (der_prop_type_eq (getΓ dΓ) (snext s) _ _ _ (der_sort (getΓ dΓ) s) (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0))
        (λ dΓ, dabs dΓ (der_var (getΓ dΓ) 2)
          (λ dΓ, der_type_conv (getΓ dΓ) _ _ _ s
            (der_var (getΓ dΓ) 0)
            (der_eq_lift (getΓ dΓ) _ _ _ _ _ (der_var (getΓ dΓ) 1))))));

compute Tr.τ Tr.TEmpty (I.inv_sort der_context_empty (trans_der s0));
compute Tr.τ Tr.TEmpty (trans_der s0);

// Application
symbol app (s s' : Sort) : Term ≔
  tfun (tsort s) // A
  (tfun (tfun (var 0) (tsort s')) // B
  (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0))) // f
  (tfun (var 2) // x
  // B x
  (tapp (var 3) (tsort s') (var 2) (var 0)))));
symbol app_term (s s' : Sort) : Term ≔
  tabs (tsort s)
    (tfun (tfun (var 0) (tsort s'))
    (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (tfun (var 2)
    (tapp (var 3) (tsort s') (var 2) (var 0)))))
  (tabs (tfun (var 0) (tsort s'))
    (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (tfun (var 2)
    (tapp (var 3) (tsort s') (var 2) (var 0))))
  (tabs (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (tfun (var 2)
    (tapp (var 3) (tsort s') (var 2) (var 0)))
  (tabs (var 2)
    (tapp (var 3) (tsort s') (var 2) (var 0))
  (tapp (var 3) (tapp (var 4) (tsort s') (var 3) (var 0)) (var 1) (var 0)))));
symbol der_app_term (s s' : Sort) : der Empty (app_term s s') (app s s') _ ≔
  dabs der_context_empty (der_sort _ s)
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 0) (λ dΓ, der_sort (getΓ dΓ) s'))
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 1) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 2) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0)))
  (λ dΓ, dabs dΓ (der_var (getΓ dΓ) 2)
  (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 3)
                 (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 4) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 3) (der_var (getΓ dΓ) 0))
                 (der_var (getΓ dΓ) 1)
                 (der_var (getΓ dΓ) 0)))));

compute Tr.τ Tr.TEmpty (I.inv_sort der_context_empty (der_app_term s0 s0));
compute Tr.τ Tr.TEmpty (der_app_term s0 s0);

// J
symbol tJ (s s' : Sort) : Term ≔
  tfun (tsort s) // A : U s
  (tfun (var 0) // x : A
  (tfun (tfun (var 1) (tfun (teq (var 2) (var 1) (var 0)) (tsort s'))) // P : Π(y : A), x = y → U s'
  (tfun (tapp (teq (var 2) (var 1) (var 1)) (tsort s') (tapp (var 2) (tfun (teq (var 3) (var 2) (var 0)) (tsort s')) (var 0) (var 1)) (trefl (var 2) (var 1))) // w : P x (refl x)
  (tfun (var 3) // y : A
  (tfun (teq (var 4) (var 3) (var 0)) // p : x = y
  (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0))))))); // P y p
symbol tJ_term (s s' : Sort) : Term ≔
  tabs (tsort s)
    (tfun (var 0) // x : A
    (tfun (tfun (var 1) (tfun (teq (var 2) (var 1) (var 0)) (tsort s'))) // P : Π(y : A), x = y → U s'
    (tfun (tapp (teq (var 2) (var 1) (var 1)) (tsort s') (tapp (var 2) (tfun (teq (var 3) (var 2) (var 0)) (tsort s')) (var 0) (var 1)) (trefl (var 2) (var 1))) // w : P x (refl x)
    (tfun (var 3) // y : A
    (tfun (teq (var 4) (var 3) (var 0)) // p : x = y
    (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0)))))))
  (tabs (var 0)
    (tfun (tfun (var 1) (tfun (teq (var 2) (var 1) (var 0)) (tsort s'))) // P : Π(y : A), x = y → U s'
    (tfun (tapp (teq (var 2) (var 1) (var 1)) (tsort s') (tapp (var 2) (tfun (teq (var 3) (var 2) (var 0)) (tsort s')) (var 0) (var 1)) (trefl (var 2) (var 1))) // w : P x (refl x)
    (tfun (var 3) // y : A
    (tfun (teq (var 4) (var 3) (var 0)) // p : x = y
    (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0))))))
  (tabs (tfun (var 1) (tfun (teq (var 2) (var 1) (var 0)) (tsort s')))
    (tfun (tapp (teq (var 2) (var 1) (var 1)) (tsort s') (tapp (var 2) (tfun (teq (var 3) (var 2) (var 0)) (tsort s')) (var 0) (var 1)) (trefl (var 2) (var 1))) // w : P x (refl x)
    (tfun (var 3) // y : A
    (tfun (teq (var 4) (var 3) (var 0)) // p : x = y
    (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0)))))
  (tabs (tapp (teq (var 2) (var 1) (var 1)) (tsort s') (tapp (var 2) (tfun (teq (var 3) (var 2) (var 0)) (tsort s')) (var 0) (var 1)) (trefl (var 2) (var 1)))
    (tfun (var 3) // y : A
    (tfun (teq (var 4) (var 3) (var 0)) // p : x = y
    (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0))))
  (tabs (var 3)
    (tfun (teq (var 4) (var 3) (var 0)) // p : x = y
    (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0)))
  (tabs (teq (var 4) (var 3) (var 0))
    (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0))
  (var 2))))));
symbol der_tJ_term (s s' : Sort) : der Empty (tJ_term s s') (tJ s s') _ ≔
  dabs der_context_empty (der_sort _ s)
  (λ dΓ, dabs dΓ (der_var (getΓ dΓ) 0)
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 1) (λ dΓ, dprod dΓ (der_prop_type_eq _ s _ _ _ (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0)) (λ dΓ, der_sort (getΓ dΓ) s')))
  (λ dΓ, dabs dΓ (dapp dΓ
                       (der_prop_type_eq _ s _ _ _ (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 1))
                       (λ dΓ, der_sort (getΓ dΓ) s')
                       (dapp dΓ
                             (der_var (getΓ dΓ) 2)
                             (λ dΓ, dprod dΓ (der_prop_type_eq _ s _ _ _ (der_var (getΓ dΓ) 3) (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 0)) (λ dΓ, der_sort (getΓ dΓ) s'))
                             (der_var (getΓ dΓ) 0)
                             (der_var (getΓ dΓ) 1))
                       (der_refl _ s _ _ (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 1)))
  (λ dΓ, dabs dΓ (der_var (getΓ dΓ) 3)
  (λ dΓ, dabs dΓ (der_prop_type_eq _ s _ _ _ (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 3) (der_var (getΓ dΓ) 0))
  (λ dΓ, der_type_conv _ _ _ _ s' (der_var (getΓ dΓ) 2)
    // (magic_der_eq' dΓ
    //   (tapp (teq (var 5) (var 4) (var 4)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 4)) (trefl (var 5) (var 4)))
    //   (tapp (teq (var 5) (var 4) (var 1)) (tsort s') (tapp (var 5) (tfun (teq (var 6) (var 5) (var 0)) (tsort s')) (var 3) (var 1)) (var 0))
    //   (tsort s')
    //   (snext s'))))))));
    (dcong_tapp dΓ
      (dcong_teq dΓ
        (der_eq_refl (getΓ dΓ) _ _ _ (der_var (getΓ dΓ) 5))
        (der_eq_refl (getΓ dΓ) _ _ _ (der_var (getΓ dΓ) 4))
        (der_eq_lift (getΓ dΓ) s (var 0) (var 4) (var 1) (var 5) (der_var (getΓ dΓ) 0)))
      (λ dΓ, der_eq_refl (getΓ dΓ) _ _ _ (der_sort (getΓ dΓ) s'))
      (dcong_tapp dΓ
        (der_eq_refl (getΓ dΓ) _ _ _ (der_var (getΓ dΓ) 5))
        (λ dΓ, der_eq_refl (getΓ dΓ) _ _ _
          (dprod dΓ
            (der_prop_type_eq _ s _ _ _ (der_var (getΓ dΓ) 6) (der_var (getΓ dΓ) 5) (der_var (getΓ dΓ) 0))
            (λ dΓ, der_sort (getΓ dΓ) s')))
        (der_eq_refl (getΓ dΓ) _ _ _ (der_var (getΓ dΓ) 3))
        (der_eq_lift (getΓ dΓ) s (var 0) (var 4) (var 1) (var 5) (der_var (getΓ dΓ) 0)))
      (der_eq_symm _ _ _ _ _ (der_eq_lift _ _ _ _ _ _
        (der_K (getΓ dΓ) s _ _ _
          (der_var (getΓ dΓ) 5)
          (der_var (getΓ dΓ) 4)
          (der_type_conv _ _ _ _ s (der_var (getΓ dΓ) 0)
            (der_eq_symm _ _ _ _ _
              (dcong_teq dΓ
                (der_eq_refl (getΓ dΓ) _ _ _ (der_var (getΓ dΓ) 5))
                (der_eq_refl (getΓ dΓ) _ _ _ (der_var (getΓ dΓ) 4))
                (der_eq_lift (getΓ dΓ) s (var 0) (var 4) (var 1) (var 5) (der_var (getΓ dΓ) 0)))))))))))))));

// Takes too long to compute
// compute Tr.τ Tr.TEmpty (I.inv_sort der_context_empty (der_tJ_term s0 s0));

// Eta equality
symbol eta_eq (s s' : Sort) : Term ≔
  tfun (tsort s) // A
  (tfun (tfun (var 0) (tsort s')) // B
  (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0))) // f
  // f = λx, f x
  (teq (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
    (var 0)
    (tabs (var 2) (tapp (var 3) (tsort s') (var 2) (var 0))
          (tapp (var 3) (tapp (var 4) (tsort s') (var 3) (var 0)) (var 1) (var 0))))));
symbol eta_eq_term (s s' : Sort) : Term ≔
  tabs (tsort s)
    (tfun (tfun (var 0) (tsort s'))
    (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (teq (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
      (var 0)
      (tabs (var 2) (tapp (var 3) (tsort s') (var 2) (var 0))
            (tapp (var 3) (tapp (var 4) (tsort s') (var 3) (var 0)) (var 1) (var 0))))))
  (tabs (tfun (var 0) (tsort s'))
    (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (teq (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
      (var 0)
      (tabs (var 2) (tapp (var 3) (tsort s') (var 2) (var 0))
            (tapp (var 3) (tapp (var 4) (tsort s') (var 3) (var 0)) (var 1) (var 0)))))
  (tabs (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (teq (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
      (var 0)
      (tabs (var 2) (tapp (var 3) (tsort s') (var 2) (var 0))
            (tapp (var 3) (tapp (var 4) (tsort s') (var 3) (var 0)) (var 1) (var 0))))
    (trefl (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
           (var 0))));
symbol der_eta_eq (s s' : Sort) : der Empty (eta_eq_term s s') (eta_eq s s') _ ≔
  dabs der_context_empty (der_sort _ s)
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 0) (λ dΓ, der_sort (getΓ dΓ) s'))
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 1) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 2) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0)))
  (λ dΓ, fromCong dΓ
  (der_eq_symm (getΓ dΓ) _ _ _ _
  (deta dΓ
    (der_var (getΓ dΓ) 2)
    (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 3) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 0))
    (der_var (getΓ dΓ) 0))))));

compute Tr.τ Tr.TEmpty (I.inv_sort der_context_empty (der_eta_eq s0 s0));
// Takes too long and too much RAM
// compute Tr.τ Tr.TEmpty (der_eta_eq s0 s0);

// Functional extensionality
symbol funext (s s' : Sort) : Term ≔
  tfun (tsort s) // A
  (tfun (tfun (var 0) (tsort s')) // B
  (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0))) // f
  (tfun (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0))) // g
  (tfun (tfun (var 3)
              (teq (tapp (var 4) (tsort s') (var 3) (var 0))
                   (tapp (var 4) (tapp (var 5) (tsort s') (var 4) (var 0)) (var 2) (var 0))
                   (tapp (var 4) (tapp (var 5) (tsort s') (var 4) (var 0)) (var 1) (var 0)))) // Π x, f x = g x
        (teq (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2) (var 1)))))); // f = g
symbol funext_term (s s' : Sort) : Term ≔
  let hyp : Term ≔
    tfun (var 3)
         (teq (tapp (var 4) (tsort s') (var 3) (var 0))
              (tapp (var 4) (tapp (var 5) (tsort s') (var 4) (var 0)) (var 2) (var 0))
              (tapp (var 4) (tapp (var 5) (tsort s') (var 4) (var 0)) (var 1) (var 0))) in
  tabs (tsort s)
    (tfun (tfun (var 0) (tsort s'))
    (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (tfun (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
    (tfun hyp (teq (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2) (var 1))))))
  (tabs (tfun (var 0) (tsort s'))
    (tfun (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (tfun (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
    (tfun hyp (teq (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2) (var 1)))))
  (tabs (tfun (var 1) (tapp (var 2) (tsort s') (var 1) (var 0)))
    (tfun (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
    (tfun hyp (teq (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2) (var 1))))
  (tabs (tfun (var 2) (tapp (var 3) (tsort s') (var 2) (var 0)))
    (tfun hyp (teq (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2) (var 1)))
  (tabs hyp
    (teq (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2) (var 1))
  (trefl (tfun (var 4) (tapp (var 5) (tsort s') (var 4) (var 0))) (var 2))))));
symbol funext_der (s s' : Sort) : der Empty (funext_term s s') (funext s s')
       (smax (snext s) (smax (smax s (snext s')) (smax (smax s s') (smax (smax s s') (smax (smax s s') (smax s s')))))) ≔
  dabs der_context_empty (der_sort _ s)
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 0) (λ dΓ, der_sort (getΓ dΓ) s'))
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 1) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 2) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0)))
  (λ dΓ, dabs dΓ (dprod dΓ (der_var (getΓ dΓ) 2) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 3) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 0)))
  (λ dΓ, dabs dΓ
    (dprod dΓ (der_var (getΓ dΓ) 3)
      (λ dΓ, der_prop_type_eq (getΓ dΓ) s' _ _ _
              (dapp dΓ (der_var (getΓ dΓ) 4) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 3) (der_var (getΓ dΓ) 0))
              (dapp dΓ (der_var (getΓ dΓ) 4) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 5) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 0)) (der_var (getΓ dΓ) 2) (der_var (getΓ dΓ) 0))
              (dapp dΓ (der_var (getΓ dΓ) 4) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 5) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 0)) (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0))))
  (λ dΓ, fromCong dΓ
    (der_eq_trans (getΓ dΓ) (smax s s') _ _ _ _
      (der_eq_symm (getΓ dΓ) (smax s s') _ _ _ (deta dΓ (der_var (getΓ dΓ) 4) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 5) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 0)) (der_var (getΓ dΓ) 2)))
      (der_eq_trans (getΓ dΓ) (smax s s') _ _ _ _
        (dcong_tabs_body dΓ
          (der_var (getΓ dΓ) 4) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 5) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 0))
          (λ dΓ, der_eq_lift (getΓ dΓ) s' _ _ _ _
            (dapp dΓ (der_var (getΓ dΓ) 5)
              (λ dΓ, der_prop_type_eq (getΓ dΓ) s' _ _ _
                       (dapp dΓ (der_var (getΓ dΓ) 6) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 5) (der_var (getΓ dΓ) 0))
                       (dapp dΓ (der_var (getΓ dΓ) 6) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 7) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 6) (der_var (getΓ dΓ) 0)) (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 0))
                       (dapp dΓ (der_var (getΓ dΓ) 6) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 7) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 6) (der_var (getΓ dΓ) 0)) (der_var (getΓ dΓ) 3) (der_var (getΓ dΓ) 0)))
              (der_var (getΓ dΓ) 1) (der_var (getΓ dΓ) 0))))
        (deta dΓ (der_var (getΓ dΓ) 4) (λ dΓ, dapp dΓ (der_var (getΓ dΓ) 5) (λ dΓ, der_sort (getΓ dΓ) s') (der_var (getΓ dΓ) 4) (der_var (getΓ dΓ) 0)) (der_var (getΓ dΓ) 1)))))))));

compute Tr.τ Tr.TEmpty (I.inv_sort der_context_empty (funext_der s0 s0));
// Takes too long and too much RAM
//compute Tr.τ Tr.TEmpty (funext_der s0 s0);
