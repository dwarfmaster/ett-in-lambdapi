
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

symbol funext (s s' : Sort) : Term ≔
  tfun (tsort s) // A
  (tfun (tfun (var 0) (tsort s')) // B
  (tfun (tfun (var 1) (var 1)) // f
  (tfun (tfun (var 2) (var 2)) // g
  (tfun (tfun (var 2)
              (teq (var 3)
                   (tapp (var 4) (var 3) (var 2) (var 0))
                   (tapp (var 4) (var 3) (var 1) (var 0)))) // Π x, f x = g x
        (teq (tfun (var 4) (var 3)) (var 2) (var 1)))))); // f = g

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
