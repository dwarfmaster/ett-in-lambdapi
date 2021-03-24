
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
// TODO
// Computation
// TODO
// Conversion
// TODO
