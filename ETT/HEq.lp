
require open ETT.ITT;
require open ETT.ILemmas;

// Intuitionistic heterogeneous equality
symbol HEq' (s : Sort) (A B : U s) (a : ε s A) (b : ε s B) : U _ ≔
  S _ _ (eq _ (u s) A B) (λ p, eq s B (transport p a) b);
symbol HEq (s : Sort) (A B : U s) (a : ε s A) (b : ε s B) : TYPE ≔
  ε _ (HEq' s A B a b);
symbol H' {s : Sort} {A B : U s} (a : ε s A) (b : ε s B) ≔ HEq' s A B a b;
symbol H {s : Sort} {A B : U s} (a : ε s A) (b : ε s B)  ≔ HEq  s A B a b;

symbol mkHeq {s : Sort} (A B : U s) (a : ε s A) (b : ε s B) (p : ε _ (eq _ (u s) A B)) :
  (ε _ (eq s B (transport p a) b)) → HEq s A B a b ≔
  λ pB, mkS _ _ (eq _ (u s) A B) (λ p, eq s B (transport p a) b) p pB;
symbol getTeq {s : Sort} {A B : U s} {a : ε s A} {b : ε s B} (heq : HEq s A B a b) : ε _ (eq _ (u s) A B) ≔
  proj1 _ _ (eq (snext s) (u s) A B) (λ p, eq s B (transport p a) b) heq;
symbol getEq {s : Sort} {A B : U s} {a : ε s A} {b : ε s B} (heq : HEq s A B a b) :
  ε _ (eq s B (transport (getTeq heq) a) b) ≔
  proj2 _ _ (eq (snext s) (u s) A B) (λ p, eq s B (transport p a) b) heq;

symbol eq_to_heq {s : Sort} {A : U s} {a b : ε s A} (p : ε _ (eq s A a b)) : HEq s A A a b ≔
  mkHeq A A a b (refl (snext s) (u s) A) p;
symbol heq_refl {s : Sort} (A : U s) (a : ε s A) : HEq s A A a a ≔
  eq_to_heq (refl s A a);
symbol heq_trans {s : Sort} {A B C : U s} {a : ε s A} {b : ε s B} {c : ε s C}
                 (hab : HEq s A B a b) (hbc : HEq s B C b c) : HEq s A C a c ≔
  mkHeq A C a c (trans_eq (getTeq hab) (getTeq hbc))
        (trans_eq
          (path_comp s A B C (getTeq hab) (getTeq hbc) a)
          (trans_eq (lift_eq (transport (getTeq hbc)) (transport (getTeq hab) a) b (getEq hab)) (getEq hbc)));
symbol heq_symm {s : Sort} {A B : U s} {a : ε s A} {b : ε s B}
                (h : HEq s A B a b) : HEq s B A b a ≔
  mkHeq B A b a (inv_eq (getTeq h))
        (trans_eq
          (inv_eq (trans_eq
            (path_comp s A B A (getTeq h) (inv_eq (getTeq h)) a)
            (lift_eq (transport (inv_eq (getTeq h))) (transport (getTeq h) a) b (getEq h))))
          (homotopy s A A (trans_eq (getTeq h) (inv_eq (getTeq h))) (refl _ (u s) A) (eq_inverse (getTeq h)) a));
symbol lift_to_heq {s s' : Sort} {A : U s} {B : ε s A → U s'}
                   (f : ε _ (P s s' A B)) (u v : ε s A) (p : ε _ (eq s A u v))
                   : HEq s' (B u) (B v) (f u) (f v) ≔
  J s _ A u (λ v _, HEq' s' (B u) (B v) (f u) (f v)) (heq_refl (B u) (f u)) v p;

// Proved using K
symbol heq_to_eq {s : Sort} {A : U s} {a b : ε s A} (h : HEq s A A a b) : ε s (eq s A a b) ≔
  J (snext s) s (eq (snext s) (u s) A A) (getTeq h)
    (λ p _, eq s A (transport p a) b) (getEq h)
    (refl (snext s) (u s) A) (K (getTeq h));

// Extend heterogeneous equality with transports to the left and to the right
symbol heq_of_transport {s : Sort} {A B : U s} (a : ε s A)
                        (p : ε _ (eq _ (u s) A B)) :
                        HEq s A B a (transport p a) ≔
  mkHeq A B a (transport p a) p (refl s B (transport p a));
symbol eq_of_transport {s : Sort} {A : U s} (a : ε s A)
                       (p : ε _ (eq _ (u s) A A)) :
                       ε _ (eq s A a (transport p a)) ≔
  heq_to_eq (heq_of_transport a p);
symbol heq_conj {s : Sort} {A B C D : U s} {b : ε s B} {c : ε s C} (h : H b c)
                (pBA : ε _ (eq _ (u s) B A)) (pCD : ε _ (eq _ (u s) C D))
                : H (transport pBA b) (transport pCD c) ≔
  heq_trans
   (heq_symm (heq_of_transport b pBA))
   (heq_trans h (heq_of_transport c pCD));
symbol heq_conj' {s : Sort} {A B C D : U s} {b : ε s B} {c : ε s C} (h : H b c)
                 (pAB : ε _ (eq _ (u s) A B)) (pDC : ε _ (eq _ (u s) D C))
                 : H (transport (inv_eq pAB) b) (transport (inv_eq pDC) c) ≔
  heq_conj h (inv_eq pAB) (inv_eq pDC);
symbol heq_contract_R {s : Sort} {A B C : U s} (a : ε s A) (c : ε s C)
                    (p : ε _ (eq _ (u s) C B))
                    (h : HEq s A B a (transport p c)) :
                    HEq s A C a c ≔
  heq_trans h (heq_symm (heq_of_transport c p));
symbol heq_extend_R {s : Sort} {A B C : U s} (a : ε s A) (b : ε s B)
                    (p : ε _ (eq _ (u s) B C))
                    (h : HEq s A B a b) :
                    HEq s A C a (transport p b) ≔
  heq_trans h (heq_of_transport b p);
symbol heq_contract_L {s : Sort} {A B C : U s} (a : ε s A) (c : ε s C)
                    (p : ε _ (eq _ (u s) A B))
                    (h : HEq s B C (transport p a) c) :
                    HEq s A C a c ≔
  heq_trans (heq_of_transport a p) h;
symbol heq_extend_L {s : Sort} {A B C : U s} (b : ε s B) (c : ε s C)
                    (p : ε _ (eq _ (u s) B A))
                    (h : HEq s B C b c) :
                    HEq s A C (transport p b) c ≔
  heq_trans (heq_symm (heq_of_transport b p)) h;
