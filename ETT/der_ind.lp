
require open ETT.main;
require ETT.itt as ITT;

symbol ε ≔ ITT.ε;

symbol der_ind :
  Π(S : ITT.Sort),
  Π(P : Π(t T : Term), der t T → ITT.U S),
  Π(Peq : Π(t1 t2 T : Term), der_eq t1 t2 T → ITT.U S),

  // Types
  // Sort case
  (Π(s : Sort), ε S (P _ _ (der_sort s)))
  // prod case
  → (Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : der (B A) (tsort s')),
    Π(HA : ε S (P _ _ dA)), Π(HB : ε S (P _ _ dB)),
    ε S (P _ _ (der_prod s s' A B dA dB)))
  // sigma case
  → (Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : der (B A) (tsort s')),
    Π(HA : ε S (P _ _ dA)), Π(HB : ε S (P _ _ dB)),
    ε S (P _ _ (der_sigma s s' A B dA dB)))
  // prop type eq
  → (Π(s : Sort), Π(A u v : Term),
    Π(dA : der A (tsort s)), Π(du : der u A), Π(dv : der v A),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)), Π(Hv : ε S (P _ _ dv)),
    ε S (P _ _ (der_prop_type_eq s A u v dA du dv)))

  // Structural rules
  // Var
  → (Π(A : Term), Π(v : Var), ε S (P _ _ (der_var A v)))
  // Conversion
  → (Π(u A B : Term), Π(s : Sort),
    Π(du : der u A), Π(deq : der_eq A B (tsort s)),
    Π(Hu : ε S (P _ _ du)), Π(Heq : ε S (Peq _ _ _ deq)),
    ε S (P _ _ (der_type_conv u A B s du deq)))

  // λ-calculus terms
  // Abstraction
  → (Π(s s' : Sort), Π(A : Term), Π(t B : Term → Term),
    Π(dA : der A (tsort s)),
    Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(dt : Π(v : Var), der (t (VAR v A)) (B (VAR v A))),
    Π(HA : ε S (P _ _ dA)), Π(HB : Π(v : Var), ε S (P _ _ (dB v))), Π(Ht : Π(v : Var), ε S (P _ _ (dt v))),
    ε S (P _ _ (der_abs s s' A t B dA dB dt)))
  // Application
  → (Π(s s' : Sort), Π(A t u : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(dfun : der t (tfun A B)), Π(du : der u A),
    Π(HA : ε S (P _ _ dA)), Π(HB : Π(v : Var), ε S (P _ _ (dB v))),
    Π(Hfun : ε S (P _ _ dfun)), Π(Hu : ε S (P _ _ du)),
    ε S (P _ _ (der_app s s' A t u B dA dB dfun du)))
  // Pair
  → (Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')), Π(dv : der v (B u)),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)), Π(HB : Π(v : Var), ε S (P _ _ (dB v))), Π(Hv : ε S (P _ _ dv)),
    ε S (P _ _ (der_pair s s' u A v B dA du dB dv)))
  // π1
  → (Π(p A : Term), Π(B : Term → Term),
    Π(dp : der p (tsum A B)), Π(Hp : ε S (P _ _ dp)),
    ε S (P _ _ (der_π1 p A B dp)))
  // π2
  → (Π(p A : Term), Π(B : Term → Term),
    Π(dp : der p (tsum A B)), Π(Hp : ε S (P _ _ dp)),
    ε S (P _ _ (der_π2 p A B dp)))
  // refl
  → (Π(s : Sort), Π(u A : Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)),
    ε S (P _ _ (der_refl s u A dA du)))
  // UIP
  → (Π(e1 e2 u v A : Term),
    Π(d1 : der e1 (teq A u v)), Π(d2 : der e2 (teq A u v)),
    Π(H1 : ε S (P _ _ d1)), Π(H2 : ε S (P _ _ d2)), ε S (P _ _ (der_uip e1 e2 u v A d1 d2)))
  // J
  // TODO

  → Π(t T : Term), Π(d : der t T), ε S (P t T d); //
