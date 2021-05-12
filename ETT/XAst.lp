
require ETT.ITT as ITT;

symbol Prop : TYPE ≔ ITT.U ITT.s0;
builtin "Prop" ≔ Prop;
symbol π : Prop → TYPE ≔ ITT.ε ITT.s0;
builtin "P" ≔ π;

/* Sorts */
symbol Sort : TYPE;
constant symbol s0 : Sort;
constant symbol snext : Sort → Sort;
symbol smax : Sort → Sort → Sort;
rule smax s0 $n ↪ $n
with smax $n s0 ↪ $n
with smax (snext $n) (snext $m) ↪ snext (smax $n $m)
with smax $s $s ↪ $s;
symbol sadd : Sort → Sort → Sort;
rule sadd s0 $n ↪ $n
with sadd $n s0 ↪ $n
with sadd (snext $n) $m ↪ snext (sadd $n $m)
with sadd $n (snext $m) ↪ snext (sadd $n $m);

/* De Bruijn indices, only the definition */
constant symbol DBId : TYPE;

/* Terms */
inductive Term : TYPE ≔
// Dependent λ-calculus
| var : DBId → Term
| tabs
  : Term // Type of the argument
  → Term // Type of result
  → Term // Body of the abstraction
  → Term
| tapp
  : Term // Type of the argument of the function
  → Term // Type of the result
  → Term // Function
  → Term // Argument
  → Term
| tfun
  : Term // Type of the argument
  → Term // Type of the result
  → Term
| tsort : Sort → Term
// Dependent pairs
| tpair
  : Term // Type of the first element
  → Term // Type of the second element
  → Term // First element
  → Term // Second element
  → Term
| π1
  : Term // First type of the pair
  → Term // Second type of the pair
  → Term // The pair
  → Term
| π2
  : Term // First type of the pair
  → Term // Second type of the pair
  → Term // The pair
  → Term
| tsum
  : Term // Type of the first element
  → Term // Type of the second element
  → Term
// Propositional equality
| trefl
  : Term // Type
  → Term // Term
  → Term
| teq
  : Term // Type of the equality
  → Term → Term → Term
// Axioms
| funext
  : Term // Type of the argument
  → Term // Type of the result
  → Term // First function
  → Term // Second function
  → Term // Proof of equality point by point
  → Term
| uip
  : Term // Type
  → Term → Term // The two terms
  → Term → Term // The two equalities
  → Term;
