
// Sorts
constant symbol Sort : TYPE;
constant symbol s0 : Sort;
constant symbol snext : Sort → Sort;
symbol smax : Sort → Sort → Sort;
rule smax s0 $s ↪ $s;
rule smax $s s0 ↪ $s;
rule smax (snext $s1) (snext $s2) ↪ snext (smax $s1 $s2);

// Interpretation of sorts
constant symbol U : Sort → TYPE;
symbol ε : Π(s : Sort), U s → TYPE;

// Axioms
constant symbol u : Π(s : Sort), U (snext s);
rule ε (snext $s) (u $s) ↪ U $s;

// Rules
constant symbol π : Π(s1 s2 : Sort), Π(a : U s1), Π(b : ε s1 a → U s2), U (smax s1 s2);
rule ε _ (π $s1 $s2 $a $b) ↪ Π(x : ε $s1 $a), ε $s2 ($b x);
