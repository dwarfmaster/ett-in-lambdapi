
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.HEq;
require open ETT.Packing;

// Product
symbol cong_prod {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                 (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                 : H (P s s' A1 B1) (P s s' A2 B2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, H' (P s s' A1 B1) (P s s' A B))))
    (λ B hB, rewr (packExtT B1 B hB)
      (λ B, H' (P s s' A1 B1) (P s s' A1 B))
      (heq_refl _ (P s s' A1 B1))))
    A2 hA B2 hB;

// Still too weak
symbol cong_prod2 {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                  (hA : ε _ (eq (snext s) (u s) A1 A2)) (hB : Π(a : ε s A1), ε _ (eq (snext s') (u s') (B1 a) (B2 (transport hA a))))
                  : ε _ (eq (snext (smax s s')) (u (smax s s')) (P s s' A1 B1) (P s s' A2 B2)) ≔
  (J _ _ (u s) A1
     (λ A pA, P _ _ (P _ _ A (λ _, u s'))
                (λ B, P _ _ (P _ _ A1 (λ a, eq _ _ (B1 a) (B (transport pA a))))
                        (λ _, eq _ _ (P s s' A1 B1) (P s s' A B))))
     (λ B hB, J _ _ (P _ _ A1 (λ _, u s')) B1
        (λ B pB, eq _ _ (P s s' A1 B1) (P s s' A1 B))
        (refl _ _ (P s s' A1 B1))
        B
        (funext _ _ A1 (λ _, u s') B1 B hB)))
  A2 hA B2 hB;

// Lambda
symbol cong_lambda {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                   (t1 : ε _ (P s s' A1 B1)) (t2 : ε _ (P s s' A2 B2))
                   (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                   (ht : Π(p : Pack A1 A2), H (t1 (projT1 p)) (t2 (projT2 p)))
                   : H t1 t2 ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, P _ _ (P _ _ A B) (λ t, P _ _ (P _ _ (Pack' A1 A) (λ p, HEq' _ (B1 (projT1 p)) (B (projT2 p)) (t1 (projT1 p)) (t (projT2
p)))) (λ _, HEq' _ (P _ _ A1 B1) (P _ _ A B) t1 t)))))
    (λ B hB, @rewr _ _ _ B1 B (packExtT B1 B hB)
      (λ B, P _ _ (P _ _ A1 B) (λ t, P _ _ (P _ _ (Pack' A1 A1) (λ p, HEq' _ (B1 (projT1 p)) (B (projT2 p)) (t1 (projT1 p)) (t (projT2 p)))) (λ _, HEq' _ (P _ _ A1 B1) (P _ _ A1 B) t1 t)))
      (λ(t : ε _ (P _ _ A1 B1)) ht, rewr (packExt t1 t ht)
        (λ t, HEq' _ (P _ _ A1 B1) (P _ _ A1 B1) t1 t)
        (heq_refl (P _ _ A1 B1) t1))))
    A2 hA B2 hB t2 ht;

// Application
symbol cong_app {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                {f1 : ε _ (P s s' A1 B1)} {f2 : ε _ (P s s' A2 B2)} {a1 : ε s A1} {a2 : ε s A2}
                (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                (hf : H f1 f2) (ha : H a1 a2)
                : H (f1 a1) (f2 a2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, P _ _ (P _ _ A B) (λ(f : ε _ ((P _ _ A B))), P _ _ (H' f1 f) (λ _, P _ _ A (λ(a : ε _ (A)), P _ _ (H' a1 a) (λ _, HEq' _
(B1 a1) (B a) (f1 a1) (f a))))))))
    (λ B hB, @rewr _ _ _ B1 B (packExtT B1 B hB)
      (λ B, P _ _ (P _ _ A1 B) (λ(f : ε _ ((P _ _ A1 B))), P _ _ (H' f1 f) (λ _, P _ _ A1 (λ(a : ε _ (A1)), P _ _ (H' a1 a) (λ _, HEq' _ (B1 a1) (B a) (f1 a1) (f a))))))
      (λ f hf, @rewr _ _ (P _ _ A1 B1) f1 f (heq_to_eq hf)
        (λ f, P _ _ A1 (λ(a : ε _ (A1)), P _ _ (H' a1 a) (λ _, HEq' _ (B1 a1) (B1 a) (f1 a1) (f a))))
        (λ a ha, @rewr _ _ A1 a1 a (heq_to_eq ha)
          (λ a, HEq' _ (B1 a1) (B1 a) (f1 a1) (f1 a))
          (heq_refl (B1 a1) (f1 a1))))))
    A2 hA B2 hB f2 hf a2 ha;

// Sum
symbol cong_sum {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                : H (S s s' A1 B1) (S s s' A2 B2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, HEq' _ (u (smax s s')) (u (smax s s')) (S s s' A1 B1) (S s s' A B))))
    (λ B hB, @rewr _ _ _ B1 B (packExtT B1 B hB)
      (λ B, HEq' _ (u (smax s s')) (u (smax s s')) (S s s' A1 B1) (S s s' A1 B))
      (heq_refl (u (smax s s')) (S s s' A1 B1))))
  A2 hA B2 hB;

// Pair
symbol cong_pair {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                 {a1 : ε s A1} {a2 : ε s A2} {b1 : ε s' (B1 a1)} {b2 : ε s' (B2 a2)}
                 (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                 (ha : H a1 a2) (hb : H b1 b2)
                 : H (mkS s s' A1 B1 a1 b1) (mkS s s' A2 B2 a2 b2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, P _ _ A (λ(a : ε _ (A)), P _ _ (H' a1 a) (λ _, P _ _ (B a) (λ(b : ε _ ((B a))), P _ _ (H' b1 b) (λ _, HEq' _ (S _ _ A1 B1) (S _ _ A B) (mkS _ _ A1 B1 a1 b1) (mkS _ _ A B a b))))))))
    (λ B hB, @rewr _ _ _ B1 B (packExtT B1 B hB)
      (λ B, P _ _ A1 (λ(a : ε _ (A1)), P _ _ (H' a1 a) (λ _, P _ _ (B a) (λ(b : ε _ ((B a))), P _ _ (H' b1 b) (λ _, HEq' _ (S _ _ A1 B1) (S _ _ A1 B) (mkS _ _ A1 B1 a1 b1) (mkS _ _ A1 B a b))))))
      (λ a ha, @rewr _ _ A1 a1 a (heq_to_eq ha)
        (λ a, P _ _ (B1 a) (λ(b : ε _ ((B1 a))), P _ _ (H' b1 b) (λ _, HEq' _ (S _ _ A1 B1) (S _ _ A1 B1) (mkS _ _ A1 B1 a1 b1) (mkS _ _ A1 B1 a b))))
        (λ b hb, @rewr _ _ (B1 a1) b1 b (heq_to_eq hb)
          (λ b, HEq' _ (S _ _ A1 B1) (S _ _ A1 B1) (mkS _ _ A1 B1 a1 b1) (mkS _ _ A1 B1 a1 b))
          (heq_refl (S _ _ A1 B1) (mkS _ _ A1 B1 a1 b1))))))
  A2 hA B2 hB a2 ha b2 hb;

// First projection
symbol cong_proj1 {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                  {s1 : ε _ (S s s' A1 B1)} {s2 : ε _ (S s s' A2 B2)}
                  (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                  (hs : H s1 s2)
                  : H (proj1 s s' A1 B1 s1) (proj1 s s' A2 B2 s2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, P _ _ (S _ _ A B) (λ(s : ε _ ((S _ _ A B))), P _ _ (H' s1 s) (λ _, HEq' _ A1 A (proj1 _ _ A1 B1 s1) (proj1 _ _ A B s))))))
    (λ B hB, @rewr _ _ _ B1 B (packExtT B1 B hB)
      (λ B, P _ _ (S _ _ A1 B) (λ(s : ε _ ((S _ _ A1 B))), P _ _ (H' s1 s) (λ _, HEq' _ A1 A1 (proj1 _ _ A1 B1 s1) (proj1 _ _ A1 B s))))
      (λ s hs, @rewr _ _ (S _ _ A1 B1) s1 s (heq_to_eq hs)
        (λ s, HEq' _ A1 A1 (proj1 _ _ A1 B1 s1) (proj1 _ _ A1 B1 s))
        (heq_refl A1 (proj1 _ _ A1 B1 s1)))))
  A2 hA B2 hB s2 hs;

// Second projection
symbol cong_proj2 {s s' : Sort} {A1 A2 : U s} (B1 : ε s A1 → U s') (B2 : ε s A2 → U s')
                  {s1 : ε _ (S s s' A1 B1)} {s2 : ε _ (S s s' A2 B2)}
                  (hA : H A1 A2) (hB : Π(p : Pack A1 A2), H (B1 (projT1 p)) (B2 (projT2 p)))
                  (hs : H s1 s2)
                  : H (proj2 s s' A1 B1 s1) (proj2 s s' A2 B2 s2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ (P _ _ A (λ _, u s')) (λ B, P _ _ (P _ _ (Pack' A1 A) (λ p, H' (B1 (projT1 p)) (B (projT2 p)))) (λ _, P _ _ (S _ _ A B) (λ(s : ε _ ((S _ _ A B))), P _ _ (H' s1 s) (λ _, HEq' _ (B1 (proj1 _ _ A1 B1 s1)) (B (proj1 _ _ A B s)) (proj2 _ _ A1 B1 s1) (proj2 _ _ A B s))))))
    (λ B hB, @rewr _ _ _ B1 B (packExtT B1 B hB)
      (λ B, P _ _ (S _ _ A1 B) (λ(s : ε _ ((S _ _ A1 B))), P _ _ (H' s1 s) (λ _, HEq' _ (B1 (proj1 _ _ A1 B1 s1)) (B (proj1 _ _ A1 B s)) (proj2 _ _ A1 B1 s1) (proj2 _ _ A1 B s))))
      (λ s hs, @rewr _ _ (S _ _ A1 B1) s1 s (heq_to_eq hs)
        (λ s, HEq' _ (B1 (proj1 _ _ A1 B1 s1)) (B1 (proj1 _ _ A1 B1 s)) (proj2 _ _ A1 B1 s1) (proj2 _ _ A1 B1 s))
        (heq_refl (B1 (proj1 _ _ A1 B1 s1)) (proj2 _ _ A1 B1 s1)))))
  A2 hA B2 hB s2 hs;

// Equality
symbol cong_eq {s : Sort} {A1 A2 : U s} {a1 b1 : ε s A1} {a2 b2 : ε s A2}
               (hA : H A1 A2) (ha : H a1 a2) (hb : H b1 b2)
               : H (eq s A1 a1 b1) (eq s A2 a2 b2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ A (λ(a : ε _ (A)), P _ _ (H' a1 a) (λ _, P _ _ A (λ(b : ε _ (A)), P _ _ (H' b1 b) (λ _, HEq' _ (u s) (u s) (eq _ A1 a1 b1) (eq _ A a b))))))
    (λ a ha, @rewr _ _ A1 a1 a (heq_to_eq ha)
      (λ a, P _ _ A1 (λ(b : ε _ (A1)), P _ _ (H' b1 b) (λ _, HEq' _ (u s) (u s) (eq _ A1 a1 b1) (eq _ A1 a b))))
      (λ b hb, @rewr _ _ A1 b1 b (heq_to_eq hb)
        (λ b, HEq' _ (u s) (u s) (eq _ A1 a1 b1) (eq _ A1 a1 b))
        (heq_refl (u s) (eq _ A1 a1 b1)))))
  A2 hA a2 ha b2 hb;

// Reflexivity
symbol cong_refl {s : Sort} {A1 A2 : U s} {a1 : ε s A1} {a2 : ε s A2}
                 (hA : H A1 A2) (ha : H a1 a2)
                 : H (refl s A1 a1) (refl s A2 a2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ A (λ(a : ε _ (A)), P _ _ (H' a1 a) (λ _, HEq' _ (eq _ A1 a1 a1) (eq _ A a a) (refl _ A1 a1) (refl _ A a))))
    (λ a ha, @rewr _ _ A1 a1 a (heq_to_eq ha)
      (λ a, HEq' _ (eq _ A1 a1 a1) (eq _ A1 a a) (refl _ A1 a1) (refl _ A1 a))
      (heq_refl (eq _ A1 a1 a1) (refl _ A1 a1))))
  A2 hA a2 ha;

// Axiom K
symbol cong_K {s : Sort} {A1 A2 : U s} {a1 : ε s A1} {a2 : ε s A2}
              {p1 : ε s (eq s A1 a1 a1)} {p2 : ε s (eq s A2 a2 a2)}
              (hA : H A1 A2) (ha : H a1 a2) (hp : H p1 p2)
              : H (K p1) (K p2) ≔
  (λ _ hA, rewr (heq_to_eq hA)
    (λ A, P _ _ A (λ(a : ε _ (A)), P _ _ (H' a1 a) (λ _, P _ _ (eq _ A a a) (λ(p : ε _ ((eq _ A a a))), P _ _ (H' p1 p) (λ _, HEq' _ (eq _ (eq _ A1 a1 a1) p1 (refl _ A1 a1)) (eq _ (eq _ A a a) p (refl _ A a)) (K p1) (K p))))))
    (λ a ha, @rewr _ _ A1 a1 a (heq_to_eq ha)
      (λ a, P _ _ (eq _ A1 a a) (λ(p : ε _ ((eq _ A1 a a))), P _ _ (H' p1 p) (λ _, HEq' _ (eq _ (eq _ A1 a1 a1) p1 (refl _ A1 a1)) (eq _ (eq _ A1 a a) p (refl _ A1 a)) (K p1) (K p))))
      (λ p hp, @rewr _ _ (eq _ A1 a1 a1) p1 p (heq_to_eq hp)
        (λ p, HEq' _ (eq _ (eq _ A1 a1 a1) p1 (refl _ A1 a1)) (eq _ (eq _ A1 a1 a1) p (refl _ A1 a1)) (K p1) (K p))
        (heq_refl (eq _ (eq _ A1 a1 a1) p1 (refl _ A1 a1)) (K p1)))))
  A2 hA a2 ha p2 hp;
