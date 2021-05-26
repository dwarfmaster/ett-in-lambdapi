
require open ETT.ITT;

// Basic lemmas about equality
symbol inv_eq {s : Sort} {A : U s} {u v : ε s A} : ε s (eq s A u v) → ε s (eq s A v u) ≔
  λ p, J s s A u (λ x _, eq s A x u) (refl s A u) v p;
symbol trans_eq {s : Sort} {A : U s} {u v w : ε s A} : ε s (eq s A u v) → ε s (eq s A v w) → ε s (eq s A u w) ≔
  λ p1 p2, J s s A v (λ x _, eq s A u x) p1 w p2;
symbol lift_eq {s s' : Sort} {A : U s} {B : U s'} (f : ε _ (P s s' A (λ _, B))) (u v : ε _ A) (p : ε _ (eq s A u v)) : ε _ (eq s' B (f u) (f v)) ≔
  J s s' A u (λ x _, eq s' B (f u) (f x)) (refl s' B (f u)) v p;
symbol eq_inverse {s : Sort} {A : U s} {u v : ε s A} (p : ε s (eq s A u v)) : ε _ (eq s (eq s A u u) (trans_eq p (inv_eq p)) (refl s A u)) ≔
  J s s A u (λ (x : ε s A) (p : ε s (eq s A u x)), eq s (eq s A u u) (trans_eq p (inv_eq p)) (refl s A u)) (refl s (eq s A u u) (refl s A u)) v p;
symbol apply_eq {s s' : Sort} {A : U s} {B : ε s A → U s'} {f g : ε _ (P s s' A B)}
                (p : ε _ (eq _ (P s s' A B) f g)) (a : ε s A)
                : ε _ (eq s' (B a) (f a) (g a)) ≔
  J (smax s s') s' (P s s' A B) f (λ g _, eq s' (B a) (f a) (g a)) (refl s' (B a) (f a)) g p;

// Transport
symbol transport {s : Sort} {T U : U s} (e : ε _ (eq (snext s) (u s) T U)) : ε s T → ε s U ≔
  λ t, J (snext s) s (u s) T (λ X _, X) t U e;
// Mimics injectivity in the second argument
unif_rule J (snext $s) $s (u $s) $T (λ X _, X) $x $U $e ≡ J (snext $s) $s (u $s) $T (λ X _, X) $y $U $e ↪ [ $x ≡ $y ];

// Lemmas about transport
symbol path_comp (s : Sort) (A B C : U s) (p1 : ε _ (eq (snext s) (u s) A B)) (p2 : ε _ (eq (snext s) (u s) B C)) (a : ε _ A) :
  ε _ (eq s C
          (transport (trans_eq p1 p2) a)
          (transport p2 (transport p1 a))) ≔
  J (snext s) s (u s) B
    (λ (C : U s) (p : ε _ (eq _ (u s) B C)), eq s C (transport (trans_eq p1 p) a) (transport p (transport p1 a)))
    (refl s B (transport p1 a)) C p2;
symbol homotopy (s : Sort) (T U : U s) (p1 p2 : ε _ (eq _ (u s) T U)) (p : ε _ (eq _ (eq _ (u s) T U) p1 p2)) (t : ε _ T) :
  ε _ (eq s U (transport p1 t) (transport p2 t)) ≔
  lift_eq (λ (p : ε _ (eq _ (u s) T U)), transport p t) p1 p2 p;

// Eta-reduction is propositionaly acceptable, due to funext
symbol η_exp {s s' : Sort} {A : U s} {B : ε s A → U s'} (f : Π(a : ε s A), ε s' (B a))
             : ε _ (eq (smax s s') (P s s' A B) f (λ a, f a)) ≔
  funext s s' A B f (λ a, f a) (λ a, refl s' (B a) (f a));
