
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.HEq;

symbol Pack' {s : Sort} (A B : U s) : U _ ≔
  S s _ A (λ a, S s _ B (λ b, HEq' s A B a b));
symbol Pack {s : Sort} (A B : U s) : TYPE ≔ ε _ (Pack' A B);
symbol mkPack {s : Sort} {A B : U s} (a : ε s A) (b : ε s B) (h : H a b) : Pack A B ≔
  mkS s _ A (λ a, S s _ B (λ b, H' a b)) a (mkS s _ B (λ b, H' a b) b h);

symbol projT1 {s : Sort} {A B : U s} (p : Pack A B) : ε s A ≔
  proj1 _ _ _ _ p;
symbol projT2 {s : Sort} {A B : U s} (p : Pack A B) : ε s B ≔
  proj1 _ _ _ _ (proj2 _ _ _ _ p);
symbol projHEq {s : Sort} {A B : U s} (p : Pack A B) : HEq s A B (projT1 p) (projT2 p) ≔
  proj2 _ _ _ _ (proj2 _ _ _ _ p);
symbol projP {s : Sort} {A B : U s} (p : Pack A B) : ε _ (eq (snext s) (u s) A B) ≔
  getTeq (proj2 _ _ _ _ (proj2 _ _ _ _ p));
symbol packHEq {s : Sort} {A B : U s} {a : ε s A} {b : ε s B} (h : HEq s A B a b) : Pack A B ≔
  mkS s _ A (λ a, S s _ B (λ b, HEq' s A B a b)) a (mkS s _ B (λ b, HEq' s A B a b) b h);
symbol packTransport {s : Sort} {A B : U s} (a : ε s A) (p : ε _ (eq _ (u s) A B)) : Pack A B ≔
  packHEq (heq_of_transport a p);
symbol packRefl {s : Sort} {A : U s} (a : ε s A) : Pack A A ≔
  packHEq (heq_refl A a);

// Extensionality reformulation using packing
symbol packExtT {s s' : Sort} {A : U s} (B1 : ε s A → U s') (B2 : ε s A → U s')
               (h : Π(p : Pack A A), H (B1 (projT1 p)) (B2 (projT2 p)))
               : ε _ (eq _ (P s (snext s') A (λ _, u s')) B1 B2) ≔
  funext s (snext s') A (λ _, u s') B1 B2
         (λ a, heq_to_eq (h (mkPack a a (heq_refl _ a))));
symbol packExt {s s' : Sort} {A : U s} {B : ε s A → U s'}
               (t1 t2 : ε _ (P s s' A B))
               (h : Π(p : Pack A A), H (t1 (projT1 p)) (t2 (projT2 p)))
               : ε _ (eq _ (P s s' A B) t1 t2);
