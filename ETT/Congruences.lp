
require open ETT.ITT;
require open ETT.ILemmas;

// Equalities
symbol eq_pair {s s' : Sort} {A A' : U s} (B : ε s A → U s') (B' : ε s A' → U s')
               (eqA : ε _ (eq (snext s) (u s) A A'))
               (eqB : Π(a : ε s A), ε _ (eq (snext s') (u s') (B a) (B' (transport eqA a)))) :
               ε _ (eq (snext (smax s s')) (u (smax s s')) (S s s' A B) (S s s' A' B'));
symbol eq_prod {s s' : Sort} {A A' : U s} (B : ε s A → U s') (B' : ε s A' → U s')
               (eqA : ε _ (eq (snext s) (u s) A A'))
               (eqB : Π(a : ε s A), ε _ (eq (snext s') (u s') (B a) (B' (transport eqA a))))
               : ε _ (eq (snext (smax s s')) (u (smax s s')) (P s s' A B) (P s s' A' B'));
