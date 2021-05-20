
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.HEq;
require open ETT.Packing;

// Equalities
symbol eq_prod {s s' : Sort} {A A' : U s} (B : ε s A → U s') (B' : ε s A' → U s')
               (eqA : ε _ (eq (snext s) (u s) A A'))
               (eqB : Π(a : ε s A), ε _ (eq (snext s') (u s') (B a) (B' (transport eqA a))))
               : ε _ (eq (snext (smax s s')) (u (smax s s')) (P s s' A B) (P s s' A' B'));

// Product
symbol cong_prod {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                 (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                 : H (P s s' A1 B1) (P s s' A2 B2);

// Lambda
symbol cong_lambda {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                   (t1 : ε _ (P s s' A1 B1)) (t2 : ε _ (P s s' A2 B2))
                   (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                   (_ : Π(p : Pack A1 A2), H (t1 (projT1 p)) (t2 (projT2 p)))
                   : H t1 t2;

// Application
symbol cong_app {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                {f1 : ε _ (P s s' A1 B1)} {f2 : ε _ (P s s' A2 B2)} {a1 : ε s A1} {a2 : ε s A2}
                (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                (_ : H f1 f2) (_ : H a1 a2)
                : H (f1 a1) (f2 a2);

// Sum
symbol cong_sum {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                : H (S s s' A1 B1) (S s s' A2 B2);

// Pair
symbol cong_pair {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                 {a1 : ε s A1} {a2 : ε s A2} {b1 : ε s' (B1 a1)} {b2 : ε s' (B2 a2)}
                 (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                 (_ : H a1 a2) (_ : H b1 b2)
                 : H (mkS s s' A1 B1 a1 b1) (mkS s s' A2 B2 a2 b2);

// First projection
symbol cong_proj1 {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                  {s1 : ε _ (S s s' A1 B1)} {s2 : ε _ (S s s' A2 B2)}
                  (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                  (_ : H s1 s2)
                  : H (proj1 s s' A1 B1 s1) (proj1 s s' A2 B2 s2);

// Second projection
symbol cong_proj2 {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                  {s1 : ε _ (S s s' A1 B1)} {s2 : ε _ (S s s' A2 B2)}
                  (_ : H A1 A2) (_ : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                  (_ : H s1 s2)
                  : H (proj2 s s' A1 B1 s1) (proj2 s s' A2 B2 s2);

// Equality
symbol cong_eq {s : Sort} {A1 A2 : U s} {a1 b1 : ε s A1} {a2 b2 : ε s A2}
               (_ : H A1 A2) (_ : H a1 a2) (_ : H b1 b2)
               : H (eq s A1 a1 b1) (eq s A2 a2 b2);

// Reflexivity
symbol cong_refl {s : Sort} {A1 A2 : U s} {a1 : ε s A1} {a2 : ε s A2}
                 (_ : H A1 A2) (_ : H a1 a2)
                 : H (refl s A1 a1) (refl s A2 a2);
