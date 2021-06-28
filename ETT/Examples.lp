
require open ETT.XAst;
require open ETT.DeBruijn;
require open ETT.XTyping;
require open ETT.XLemmas;
require ETT.main as M;
require ETT.TranslationDefinition as Tr;
require ETT.Inversions as I;

builtin "0" ≔ db0;
builtin "+1" ≔ dbsucc;

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
  der_abs Empty _ _ _ _ _
    (der_sort Empty s der_context_empty)
    (der_prod (Push (tsort s) (snext s) Empty) _ _ _ _
      (der_var _ 0
        (pushΓ (der_sort Empty s der_context_empty)))
      (der_var _ 1
        (pushΓ (der_var _ 0 (pushΓ (der_sort Empty s der_context_empty))))))
    (der_abs (Push (tsort s) (snext s) Empty) _ _ _ _ _
      (der_var _ 0
        (pushΓ (der_sort Empty s der_context_empty)))
      (der_var _ 1
        (pushΓ (der_var _ 0 (pushΓ (der_sort Empty s der_context_empty)))))
      (der_var _ 0
        (pushΓ (der_var _ 0 (pushΓ (der_sort Empty s der_context_empty))))));

compute Tr.τ Tr.TEmpty (I.inv_sort (poly_id_der s0));
compute Tr.τ Tr.TEmpty (poly_id_der s0);
