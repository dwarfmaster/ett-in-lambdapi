
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.HEq;

injective symbol Pack' {s : Sort} (A B : U s) : U _ ≔
  S s _ A (λ a, S s _ B (λ b, HEq' s A B a b));
injective symbol Pack {s : Sort} (A B : U s) : TYPE ≔ ε _ (Pack' A B);

symbol projT1 {s : Sort} {A B : U s} (p : Pack A B) : ε s A ≔
  proj1 _ _ _ _ p;
symbol projT2 {s : Sort} {A B : U s} (p : Pack A B) : ε s B ≔
  proj1 _ _ _ _ (proj2 _ _ _ _ p);
symbol projHEq {s : Sort} {A B : U s} (p : Pack A B) : HEq s A B (projT1 p) (projT2 p) ≔
  proj2 _ _ _ _ (proj2 _ _ _ _ p);
symbol projP {s : Sort} {A B : U s} (p : Pack A B) : ε _ (eq (snext s) (u s) A B) ≔
  getTeq (proj2 _ _ _ _ (proj2 _ _ _ _ p));
