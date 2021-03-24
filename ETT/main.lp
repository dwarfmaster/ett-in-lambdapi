
/* Sorts */
symbol Sort : TYPE;
constant symbol s0 : Sort;
constant symbol snext : Sort → Sort;
symbol smax : Sort → Sort → Sort;
rule smax s0 $n ↪ $n;
rule smax $n s0 ↪ $n;
rule smax (snext $n) (snext $m) ↪ snext (smax $n $m);

/* Terms */
/* HOAS style, in order to avoid having to bother with De Brujin indices and α
renaming. */
symbol Term : TYPE;
// Dependent λ-calculus
constant symbol tabs
              : Term // Type of the argument
              → (Term → Term) // Type of result
              → (Term → Term) // Body of the abstraction
              → Term;
constant symbol tapp
              : Term // Type of the argument of the function
              → (Term → Term) // Type of the result
              → Term // Function
              → Term // Argument
              → Term;
constant symbol tfun
              : Term // Type of the argument
              → (Term → Term) // Type of the result
              → Term;
constant symbol tsort : Sort → Term;
// Dependent pairs
constant symbol tpair
              : Term // Type of the first element
              → (Term → Term) // Type of the second element
              → Term // First element
              → Term // Second element
              → Term;
constant symbol π1
              : Term // First type of the pair
              → (Term → Term) // Second type of the pair
              → Term // The pair
              → Term;
constant symbol π2
              : Term // First type of the pair
              → (Term → Term) // Second type of the pair
              → Term // The pair
              → Term;
constant symbol tsum
              : Term // Type of the first element
              → (Term → Term) // Type of the second element
              → Term;
// Propositional equality
constant symbol trefl
              : Term // Type
              → Term // Term
              → Term;
constant symbol J
              : Term // Type of the term to rewrite A
              → Term // Term to rewrite u
              → (Term → Term → Term) // Proposition depending on the term and the equality aka P
              → Term // Proof of P(u, refl A u)
              → Term // Term to rewrite u by
              → Term // Proof of equality between the terms to rewrite
              → Term;
constant symbol teq
              : Term // Type of the equality
              → Term → Term → Term;
// Axioms
constant symbol funext
              : Term // Type of the argument
              → (Term → Term) // Type of the result
              → Term // First function
              → Term // Second function
              → Term // Proof of equality point by point
              → Term;
constant symbol uip
              : Term // Type
              → Term → Term // The two terms
              → Term → Term // The two equalities
              → Term;

/* Typing derivation */
constant symbol der : Term → Term → TYPE;
constant symbol der_eq : Term → Term → Term → TYPE;
constant symbol VAR : Term → Term; // Represents a bound variable of type its argument

// Types
constant symbol der_sort : Π(s : Sort), der (tsort s) (tsort (snext s));
constant symbol der_prod :
  Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
  der A (tsort s) → der (B A) (tsort s') → der (tfun A B) (tsort (smax s s'));
constant symbol der_sigma :
  Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
  der A (tsort s) → der (B A) (tsort s') → der (tsum A B) (tsort (smax s s'));
constant symbol der_prop_type_eq :
  Π(s : Sort), Π(A u v : Term),
  der A (tsort s) → der u A → der v A → der (teq A u v) (tsort s);

// Structural rules
constant symbol der_var : Π(A : Term), der (VAR A) A;
constant symbol der_type_conv :
  Π (u A B : Term), Π(s : Sort),
  der u A → der_eq A B (tsort s) → der u B;

// λ-calculus terms
constant symbol der_abs :
  Π(s s' : Sort), Π(A : Term), Π(t B : Term → Term),
  der A (tsort s) → der (B (VAR A)) (tsort s') → der (t (VAR A)) (B (VAR A))
  → der (tabs A B t) (tfun A B);
constant symbol der_app :
  Π(s s' : Sort), Π(A t u : Term), Π(B : Term → Term),
  der A (tsort s) → der (B (VAR A)) (tsort s')
  → der t (tfun A B) → der u A → der (tapp A B t u) (B u);
constant symbol der_pair :
  Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
  der A (tsort s) → der u A → der (B (VAR A)) (tsort s') → der v (B u)
  → der (tpair A B u v) (tsum A B);
constant symbol der_π1 :
  Π(p A : Term), Π(B : Term → Term),
  der p (tsum A B) → der (π1 A B p) A;
constant symbol der_π2 :
  Π(p A : Term), Π(B : Term → Term),
  der p (tsum A B) → der (π2 A B p) (B (π1 A B p));
// Equality terms
constant symbol der_refl :
  Π(s : Sort), Π(u A : Term),
  der A (tsort s) → der u A → der (trefl A u) (teq A u u);
constant symbol der_uip :
  Π(e1 e2 u v A : Term),
  der e1 (teq A u v) → der e2 (teq A u v) → der (uip A u v e1 e2) (teq (teq A u v) e1 e2);
constant symbol der_J :
  Π(s s' : Sort), Π(A u v p w : Term), Π(P : Term → Term → Term),
  der A (tsort s) → der u A → der v A
  → der (P (VAR A) (VAR (teq A u (VAR A)))) (tsort s')
  → der p (teq A u v) → der w (P u (trefl A u))
  → der (J A u P w v p) (P v p);
constant symbol der_funext :
  Π(f g A e : Term), Π(B : Term → Term),
  der f (tfun A B) → der g (tfun A B)
  → der e (tfun A (λ u, teq (B u) (tapp A B f u) (tapp A B g u)))
  → der (funext A B f g e) (teq (tfun A B) f g);
// Computation
constant symbol der_eq_beta :
  Π(s s' : Sort), Π(u A : Term), Π(t B : Term → Term),
  der A (tsort s) → der (B (VAR A)) (tsort s') → der (t (VAR A)) (B (VAR A)) → der u A
  → der_eq (B u) (tapp A B (tabs A B t) u) (t u);
constant symbol der_eq_J :
  Π(s s' : Sort), Π(u A w : Term), Π(P : Term → Term → Term),
  der A (tsort s) → der u A → der (P (VAR A) (VAR (teq A u (VAR A)))) (tsort s')
  → der w (P u (trefl A u))
  → der_eq (P u (trefl A u)) (J A u P w u (trefl A u)) w;
constant symbol der_eq_π1 :
  Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
  der A (tsort s) → der u A → der (B (VAR A)) (tsort s') → der v (B u)
  → der_eq A (π1 A B (tpair A B u v)) u;
constant symbol der_eq_π2 :
  Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
  der A (tsort s) → der u A → der (B (VAR A)) (tsort s') → der v (B u)
  → der_eq (B u) (π2 A B (tpair A B u v)) v;
// Conversion
constant symbol der_eq_conversion :
  Π(s : Sort), Π(t1 t2 T1 T2 : Term),
  der T1 (tsort s) → der T2 (tsort s)
  → der_eq T1 t1 t2 → der_eq (tsort s) T1 T2
  → der_eq T2 t1 t2;
constant symbol der_eq_lift :
  Π(e u v A : Term),
  der e (teq A u v) → der_eq A u v;
