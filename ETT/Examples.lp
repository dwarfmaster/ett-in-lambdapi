
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
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

symbol dprod {Γ : Context} {A B : Term} {s s' : Sort}
  : der Γ A (tsort s) (snext s)
  → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
  → der Γ (tfun A B) (tsort (smax s s')) (snext (smax s s')) ≔
  λ dA dB, der_prod Γ s s' A B dA (dB (pushΓ dA));
symbol dabs {Γ : Context} {A B t : Term} {s s' : Sort}
  : der Γ A (tsort s) (snext s)
  → (der_context (Push A s Γ) → der (Push A s Γ) t B s')
  → der Γ (tabs A B t) (tfun A B) (smax s s') ≔
  λ dA dt, der_abs Γ s s' A t B dA (I.inv_sort (dt (pushΓ dA))) (dt (pushΓ dA));
symbol dapp {Γ : Context} {A B f a : Term} {s s' : Sort}
  : der Γ A (tsort s) (snext s)
  → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
  → der Γ f (tfun A B) (smax s s')
  → der Γ a A s
  → der Γ (tapp A B f a) (apply1 B a) s' ≔
  λ dA dB df da, der_app Γ s s' A f a B dA (dB (pushΓ dA)) df da;
symbol deta {Γ : Context} {s s' : Sort} {A f B : Term}
            : der Γ A (tsort s) (snext s)
            → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
            → der Γ f (tfun A B) (smax s s')
            → der_eq Γ (smax s s') (tfun A B) (tabs A B (tapp (Shift A) (Shift1 B) (Shift f) (var 0))) f ≔
  λ dA dB df, der_eq_eta Γ s s' A f B dA (dB (pushΓ dA)) df;
symbol dcong_tabs_body {Γ : Context} {s s' : Sort} {A B t1 t2 : Term}
                       : der Γ A (tsort s) (snext s)
                       → (der_context (Push A s Γ) → der (Push A s Γ) B (tsort s') (snext s'))
                       → (der_context (Push A s Γ) → der_eq (Push A s Γ) s' B t1 t2)
                       → der_eq Γ (smax s s') (tfun A B) (tabs A B t1) (tabs A B t2) ≔
  λ dA dB dt,
    der_eq_cong_tabs Γ s s' A A B B t1 t2
                     (der_eq_refl Γ (snext s) A (tsort s) dA)
                     (der_eq_refl (Push A s Γ) (snext s') B (tsort s') (dB (pushΓ dA)))
                     (dt (pushΓ dA))
                     (dB (pushΓ dA)) (dB (pushΓ dA))
                     (I.inv_eq_t1 (dt (pushΓ dA))) (I.inv_eq_t2 (dt (pushΓ dA)));

symbol fromCong {Γ : Context} {t1 t2 T : Term} {s : Sort}
       : der_eq Γ s T t1 t2 → der Γ (trefl T t1) (teq T t1 t2) s;

// Very simple test
symbol poly_id (s : Sort) : Term ≔
  tabs (tsort s) (tfun (var 0) (var 1)) // A
  (tabs (var 0) (var 1) (var 0)); // λ x. x
symbol poly_id_type (s : Sort) : Term ≔
  tfun (tsort s) (tfun (var 0) (var 1));
symbol poly_id_der (s : Sort) : der Empty (poly_id s) (poly_id_type s) (smax (snext s) (smax s s)) ≔
  dabs (der_sort Empty s der_context_empty)
    (λ dΓ, dabs (der_var _ 0 dΓ)
      (λ dΓ, der_var _ 0 dΓ));

compute Tr.τ Tr.TEmpty (I.inv_sort (poly_id_der s0));
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
  dabs (der_sort Empty s der_context_empty)
    (λ dΓ, dabs (der_sort _ s dΓ)
      (λ dΓ, dabs (der_prop_type_eq _ _ _ _ _ (der_sort _ s dΓ) (der_var _ 1 dΓ) (der_var _ 0 dΓ))
        (λ dΓ, dabs (der_var _ 2 dΓ)
          (λ dΓ, der_type_conv _ _ _ _ _
            (der_var _ 0 dΓ)
            (der_eq_lift _ _ _ _ _ _ (der_var _ 1 dΓ))))));

// Execution
compute Tr.τ Tr.TEmpty (I.inv_sort (trans_der s0));
compute Tr.τ Tr.TEmpty (trans_der s0);

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
symbol funext_der (s s' : Sort) : der Empty (funext_term s s') (funext s s') _ ≔
  dabs (der_sort _ s der_context_empty)
  (λ dΓ, dabs (dprod (der_var _ 0 dΓ) (λ dΓ, der_sort _ s' dΓ))
  (λ dΓ, dabs (dprod (der_var _ 1 dΓ) (λ dΓ, dapp (der_var _ 2 dΓ) (der_sort _ s') (der_var _ 1 dΓ) (der_var _ 0 dΓ)))
  (λ dΓ, dabs (dprod (der_var _ 2 dΓ) (λ dΓ, dapp (der_var _ 3 dΓ) (der_sort _ s') (der_var _ 2 dΓ) (der_var _ 0 dΓ)))
  (λ dΓ, dabs (dprod (der_var _ 3 dΓ)
    (λ dΓ, der_prop_type_eq _ _ _ _ _
            (dapp (der_var _ 4 dΓ) (der_sort _ s') (der_var _ 3 dΓ) (der_var _ 0 dΓ))
            (dapp (der_var _ 4 dΓ) (λ dΓ, dapp (der_var _ 5 dΓ) (der_sort _ s') (der_var _ 4 dΓ) (der_var _ 0 dΓ)) (der_var _ 2 dΓ) (der_var _ 0 dΓ))
            (dapp (der_var _ 4 dΓ) (λ dΓ, dapp (der_var _ 5 dΓ) (der_sort _ s') (der_var _ 4 dΓ) (der_var _ 0 dΓ)) (der_var _ 1 dΓ) (der_var _ 0 dΓ))))
  (λ dΓ, fromCong
    (der_eq_trans _ _ _ _ _ _
      (der_eq_symm _ _ _ _ _ (deta (der_var _ 4 dΓ) (λ dΓ, dapp (der_var _ 5 dΓ) (der_sort _ s') (der_var _ 4 dΓ) (der_var _ 0 dΓ)) (der_var _ 2 dΓ)))
      (der_eq_trans _ _ _ _ _ _
        (dcong_tabs_body
          (der_var _ 4 dΓ) (λ dΓ, dapp (der_var _ 5 dΓ) (der_sort _ s') (der_var _ 4 dΓ) (der_var _ 0 dΓ))
          (λ dΓ, der_eq_lift _ _ _ _ _ _
            (dapp (der_var _ 5 dΓ)
              (λ dΓ, der_prop_type_eq _ _ _ _ _
                       (dapp (der_var _ 6 dΓ) (der_sort _ s') (der_var _ 5 dΓ) (der_var _ 0 dΓ))
                       (dapp (der_var _ 6 dΓ) (λ dΓ, dapp (der_var _ 7 dΓ) (der_sort _ s') (der_var _ 6 dΓ) (der_var _ 0 dΓ)) (der_var _ 4 dΓ) (der_var _ 0 dΓ))
                       (dapp (der_var _ 6 dΓ) (λ dΓ, dapp (der_var _ 7 dΓ) (der_sort _ s') (der_var _ 6 dΓ) (der_var _ 0 dΓ)) (der_var _ 3 dΓ) (der_var _ 0 dΓ)))
              (der_var _ 1 dΓ) (der_var _ 0 dΓ))))
        (deta (der_var _ 4 dΓ) (λ dΓ, dapp (der_var _ 5 dΓ) (der_sort _ s') (der_var _ 4 dΓ) (der_var _ 0 dΓ)) (der_var _ 1 dΓ)))))))));

//compute funext_der s0 s0;
//compute Tr.τ Tr.TEmpty (I.inv_sort (funext_der s0 s0));
//compute Tr.τ Tr.TEmpty (funext_der s0 s0);
