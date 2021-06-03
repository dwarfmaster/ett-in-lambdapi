
// Sorts
constant symbol Sort : TYPE;
constant symbol s0 : Sort;
constant symbol snext : Sort → Sort;
symbol smax : Sort → Sort → Sort;
rule smax s0 $s ↪ $s
with smax $s s0 ↪ $s
with smax (snext $s1) (snext $s2) ↪ snext (smax $s1 $s2)
with smax $s $s ↪ $s;

// Interpretation of sorts
constant symbol U : Sort → TYPE;
injective symbol ε : Π(s : Sort), U s → TYPE;

// Axioms
constant symbol u : Π(s : Sort), U (snext s);
rule ε (snext $s) (u $s) ↪ U $s;
unif_rule U $s ≡ ε $s' $x ↪ [ $s' ≡ (snext $s); $x ≡ u $s ];

// Product
constant symbol P : Π(s1 s2 : Sort), Π(a : U s1), (ε s1 a → U s2) → U (smax s1 s2);
rule ε _ (P $s1 $s2 $a $b) ↪ Π(x : ε $s1 $a), ε $s2 ($b x);

// Dependent sum
constant symbol S : Π(s s' : Sort), Π(A : U s), (ε s A → U s') → U (smax s s');
constant symbol mkS (s s' : Sort) (A : U s) (B : ε s A → U s') : Π(x : ε s A), ε s' (B x) → ε (smax s s') (S s s' A B);
symbol proj1 (s s' : Sort) (A : U s) (B : ε s A → U s') : ε (smax s s') (S s s' A B) → ε s A;
rule proj1 _ _ _ _ (mkS _ _ _ _ $x _) ↪ $x;
symbol proj2 (s s' : Sort) (A : U s) (B : ε s A → U s') : Π(p : ε (smax s s') (S s s' A B)), ε s' (B (proj1 s s' A B p));
rule proj2 _ _ _ _ (mkS _ _ _ _ _ $y) ↪ $y;

// Homogeneous equality
constant symbol eq (s : Sort) (A : U s) : ε s A → ε s A → U s;
constant symbol refl (s : Sort) (A : U s) (x : ε s A) : ε s (eq s A x x);
symbol J (s s' : Sort) (A : U s) (u : ε s A) (P : Π(x : ε s A), ε s (eq s A u x) → U s')
         (_ : ε s' (P u (refl s A u))) (v : ε s A) (p : ε s (eq s A u v)) : ε s' (P v p);
rule J _ _ _ _ _ $w _ (refl _ _ _) ↪ $w;

// Axioms
symbol K {s : Sort} {A : U s} {a : ε s A} (p : ε s (eq s A a a))
         : ε s (eq s (eq s A a a) p (refl s A a));
rule K (refl $s $A $a) ↪ refl $s (eq $s $A $a $a) (refl $s $A $a);
constant symbol funext (s s' : Sort) (A : U s) (B : ε s A → U s') (f g : ε (smax s s') (P s s' A B))
                       (_ : Π(x : ε s A), ε s' (eq s' (B x) (f x) (g x)))
              : ε (smax s s') (eq (smax s s') (P s s' A B) f g);

// True
constant symbol ⊤ (s : Sort) : U s;
constant symbol I (s : Sort) : ε s (⊤ s);

// False
constant symbol ⊥ (s : Sort) : U s;
constant symbol ⊥_elim (s1 s2 : Sort) (A : U s2) : ε _ (P s1 s2 (⊥ s1) (λ _, A));

