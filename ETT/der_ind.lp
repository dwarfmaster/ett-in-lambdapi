
require open ETT.main;
require ETT.itt as ITT;

constant symbol der_ind_T :
  Π(S : ITT.Sort),
  Π(_ : Π(t T : Term), der t T → ITT.U S),
  Π(_ : Π(T t1 t2 : Term), der_eq T t1 t2 → ITT.U S),
  TYPE;
symbol get_der_ind (S : ITT.Sort) (P : Π(t T : Term), der t T → ITT.U S)
                   (Peq : Π(T t1 t2 : Term), der_eq T t1 t2 → ITT.U S) :
  der_ind_T S P Peq → Π(t T : Term), Π(d : der t T), ITT.ε S (P t T d);
symbol get_der_eq_ind (S : ITT.Sort) (P : Π(t T : Term), der t T → ITT.U S)
                   (Peq : Π(T t1 t2 : Term), der_eq T t1 t2 → ITT.U S) :
  der_ind_T S P Peq → Π(T t1 t2 : Term), Π(d : der_eq T t1 t2), ITT.ε S (Peq T t1 t2 d);

symbol der_ind' :
  Π(S : ITT.Sort),
  Π(P : Π(t T : Term), der t T → ITT.U S),
  Π(Peq : Π(T t1 t2 : Term), der_eq T t1 t2 → ITT.U S),

  // Types
  // Sort case
  (Π(s : Sort), ITT.ε S (P _ _ (der_sort s)))
  // prod case
  → (Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(HA : ITT.ε S (P _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v ))),
    ITT.ε S (P _ _ (der_prod s s' A B dA dB)))
  // sigma case
  → (Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(HA : ITT.ε S (P _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))),
    ITT.ε S (P _ _ (der_sigma s s' A B dA dB)))
  // prop type eq
  → (Π(s : Sort), Π(A u v : Term),
    Π(dA : der A (tsort s)), Π(du : der u A), Π(dv : der v A),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)), Π(Hv : ITT.ε S (P _ _ dv)),
    ITT.ε S (P _ _ (der_prop_type_eq s A u v dA du dv)))

  // Structural rules
  // Var
  → (Π(A : Term), Π(v : Var), ITT.ε S (P _ _ (der_var A v)))
  // Conversion
  → (Π(u A B : Term), Π(s : Sort),
    Π(du : der u A), Π(deq : der_eq (tsort s) A B),
    Π(Hu : ITT.ε S (P _ _ du)), Π(Heq : ITT.ε S (Peq _ _ _ deq)),
    ITT.ε S (P _ _ (der_type_conv u A B s du deq)))

  // λ-calculus terms
  // Abstraction
  → (Π(s s' : Sort), Π(A : Term), Π(t B : Term → Term),
    Π(dA : der A (tsort s)),
    Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(dt : Π(v : Var), der (t (VAR v A)) (B (VAR v A))),
    Π(HA : ITT.ε S (P _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))), Π(Ht : Π(v : Var), ITT.ε S (P _ _ (dt v))),
    ITT.ε S (P _ _ (der_abs s s' A t B dA dB dt)))
  // Application
  → (Π(s s' : Sort), Π(A t u : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(dfun : der t (tfun A B)), Π(du : der u A),
    Π(HA : ITT.ε S (P _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))),
    Π(Hfun : ITT.ε S (P _ _ dfun)), Π(Hu : ITT.ε S (P _ _ du)),
    ITT.ε S (P _ _ (der_app s s' A t u B dA dB dfun du)))
  // Pair
  → (Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')), Π(dv : der v (B u)),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)), Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))), Π(Hv : ITT.ε S (P _ _ dv)),
    ITT.ε S (P _ _ (der_pair s s' u A v B dA du dB dv)))
  // π1
  → (Π(p A : Term), Π(B : Term → Term),
    Π(dp : der p (tsum A B)), Π(Hp : ITT.ε S (P _ _ dp)),
    ITT.ε S (P _ _ (der_π1 p A B dp)))
  // π2
  → (Π(p A : Term), Π(B : Term → Term),
    Π(dp : der p (tsum A B)), Π(Hp : ITT.ε S (P _ _ dp)),
    ITT.ε S (P _ _ (der_π2 p A B dp)))
  // refl
  → (Π(s : Sort), Π(u A : Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)),
    ITT.ε S (P _ _ (der_refl s u A dA du)))
  // UIP
  → (Π(e1 e2 u v A : Term),
    Π(d1 : der e1 (teq A u v)), Π(d2 : der e2 (teq A u v)),
    Π(H1 : ITT.ε S (P _ _ d1)), Π(H2 : ITT.ε S (P _ _ d2)), ITT.ε S (P _ _ (der_uip e1 e2 u v A d1 d2)))
  // J
  → (Π(s s' : Sort), Π(A u v p w : Term), Π(E : Term → Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A), Π(dv : der v A),
    Π(dE : Π(v1 v2 : Var), der (E (VAR v1 A) (VAR v2 (teq A u (VAR v1 A)))) (tsort s')),
    Π(dp : der p (teq A u v)), Π(dw : der w (E u (trefl A u))),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)), Π(Hv : ITT.ε S (P _ _ dv)),
    Π(HE : Π(v1 v2 : Var), ITT.ε S (P _ _ (dE v1 v2))),
    Π(Hp : ITT.ε S (P _ _ dp)), Π(Hw : ITT.ε S (P _ _ dw)),
    ITT.ε S (P _ _ (der_J s s' A u v p w E dA du dv dE dp dw)))
  // Function extensionality
  → (Π(f g A e : Term), Π(B : Term → Term),
    Π(df : der f (tfun A B)), Π(dg : der g (tfun A B)),
    Π(de : der e (tfun A (λ u, teq (B u) (tapp A B f u) (tapp A B g u)))),
    Π(Hf : ITT.ε S (P _ _ df)), Π(Hg : ITT.ε S (P _ _ dg)), Π(He : ITT.ε S (P _ _ de)),
    ITT.ε S (P _ _ (der_funext f g A e B df dg de)))

  // Computation
  // β-reduction
  → (Π(s s' : Sort), Π(u A : Term), Π(t B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(dt : Π(v : Var), der (t (VAR v A)) (B (VAR v A))), Π(du : der u A),
    Π(HA : ITT.ε S (P _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))),
    Π(Ht : Π(v : Var), ITT.ε S (P _ _ (dt v))), Π(Hu : ITT.ε S (P _ _ du)),
    ITT.ε S (Peq _ _ _ (der_eq_beta s s' u A t B dA dB dt du)))
  // J
  → (Π(s s' : Sort), Π(u A w : Term), Π(E : Term → Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(dE : Π(v1 v2 : Var), der (E (VAR v1 A) (VAR v2 (teq A u (VAR v1 A)))) (tsort s')),
    Π(dw : der w (E u (trefl A u))),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)),
    Π(HE : Π(v1 v2 : Var), ITT.ε S (P _ _ (dE v1 v2))), Π(Hw : ITT.ε S (P _ _ dw)),
    ITT.ε S (Peq _ _ _ (der_eq_J s s' u A w E dA du dE dw)))
  // π1
  → (Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')), Π(dv : der v (B u)),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)),
    Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))), Π(Hv : ITT.ε S (P _ _ dv)),
    ITT.ε S (Peq _ _ _ (der_eq_π1 s s' u A v B dA du dB dv)))
  // π2
  → (Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')), Π(dv : der v (B u)),
    Π(HA : ITT.ε S (P _ _ dA)), Π(Hu : ITT.ε S (P _ _ du)),
    Π(HB : Π(v : Var), ITT.ε S (P _ _ (dB v))), Π(Hv : ITT.ε S (P _ _ dv)),
    ITT.ε S (Peq _ _ _ (der_eq_π2 s s' u A v B dA du dB dv)))
  // Conversion
  → (Π(s : Sort), Π(t1 t2 T1 T2 : Term),
    Π(dT1 : der T1 (tsort s)), Π(dT2 : der T2 (tsort s)),
    Π(deqt : der_eq T1 t1 t2), Π(deqT : der_eq (tsort s) T1 T2),
    Π(HT1 : ITT.ε S (P _ _ dT1)), Π(HT2 : ITT.ε S (P _ _ dT2)),
    Π(Heqt : ITT.ε S (Peq _ _ _ deqt)), Π(HeqT : ITT.ε S (Peq _ _ _ deqT)),
    ITT.ε S (Peq _ _ _ (der_eq_conversion s t1 t2 T1 T2 dT1 dT2 deqt deqT)))
  // Lifting
  → (Π(e u v A : Term), Π(de : der e (teq A u v)),
    Π(He : ITT.ε S (P _ _ de)), ITT.ε S (Peq _ _ _ (der_eq_lift e u v A de)))

  // Computation context
  // CTX Abstraction
  → (Π(s s' : Sort), Π(A A' : Term), Π(B B' t t' : Term → Term),
    Π(dA : der_eq (tsort s) A A'),
    Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(dt : Π(v : Var), der_eq (B (VAR v A)) (t (VAR v A)) (t' (VAR v A))),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    Π(Ht : Π(v : Var), ITT.ε S (Peq _ _ _ (dt v))),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_abs s s' A A' B B' t t' dA dB dt)))
  // CTX Application
  → (Π(s s' : Sort), Π(A A' f f' u u' : Term), Π(B B' : Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(df : der_eq (tfun A B) f f'),
    Π(du : der_eq A u u'), Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(Hf : ITT.ε S (Peq _ _ _ df)),
    Π(Hu : ITT.ε S (Peq _ _ _ du)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_app s s' A A' f f' u u' B B' dA df du dB)))
  // CTX Product
  → (Π(s s' : Sort), Π(A A' : Term), Π(B B' : Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_prod s s' A A' B B' dA dB)))
  // CTX Pair
  → (Π(s s' : Sort), Π(u u' A A' v v' : Term), Π(B B' : Term → Term),
    Π(du : der_eq A u u'), Π(dA : der_eq (tsort s) A A'), Π(dv : der_eq (B u) v v'),
    Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(Hu : ITT.ε S (Peq _ _ _ du)), Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(Hv : ITT.ε S (Peq _ _ _ dv)),
    Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_pair s s' u u' A A' v v' B B' du dA dv dB)))
  // CTX π1
  → (Π(s s' : Sort), Π(p p' A A' : Term), Π(B B' : Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(dp : der_eq (tsum A B) p p'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    Π(Hp : ITT.ε S (Peq _ _ _ dp)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_π1 s s' p p' A A' B B' dA dB dp)))
  // CTX π2
  → (Π(s s' : Sort), Π(p p' A A' : Term), Π(B B' : Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(dp : der_eq (tsum A B) p p'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    Π(Hp : ITT.ε S (Peq _ _ _ dp)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_π2 s s' p p' A A' B B' dA dB dp)))
  // CTX sum
  → (Π(s s' : Sort), Π(A A' : Term), Π(B B' : Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_sum s s' A A' B B' dA dB)))
  // CTX refl
  → (Π(s : Sort), Π(A A' u u' : Term),
    Π(dA : der_eq (tsort s) A A'), Π(du : der_eq A u u'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(Hu : ITT.ε S (Peq _ _ _ du)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_refl s A A' u u' dA du)))
  // CTX J
  → (Π(s s' : Sort), Π(A A' u u' v v' w w' p p' : Term), Π(E E' : Term → Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(du : der_eq A u u'), Π(dv : der_eq A v v'),
    Π(dE : Π(v1 v2 : Var), der_eq (tsort s') (E  (VAR v1 A) (VAR v2 (teq A u (VAR v1 A))))
                                             (E' (VAR v1 A) (VAR v2 (teq A u (VAR v1 A))))),
    Π(dp : der_eq (teq A u v) p p'), Π(dw : der_eq (E u (trefl A u)) w w'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(Hu : ITT.ε S (Peq _ _ _ du)), Π(Hv : ITT.ε S (Peq _ _ _ dv)),
    Π(HE : Π(v1 v2 : Var), ITT.ε S (Peq _ _ _ (dE v1 v2))),
    Π(Hp : ITT.ε S (Peq _ _ _ dp)), Π(Hw : ITT.ε S (Peq _ _ _ dw)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_J s s' A A' u u' v v' w w' p p' E E' dA du dv dE dp dw)))
  // CTX equality
  → (Π(s : Sort), Π(A A' u u' v v' : Term),
    Π(dA : der_eq (tsort s) A A'), Π(du : der_eq A u u'), Π(dv : der_eq A v v'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(Hu : ITT.ε S (Peq _ _ _ du)), Π(Hv : ITT.ε S (Peq _ _ _ dv)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_teq s A A' u u' v v' dA du dv)))
  // CTX function extensionality
  → (Π(s s' : Sort), Π(f f' g g' A A' e e' : Term), Π(B B' : Term → Term),
    Π(dA : der_eq (tsort s) A A'), Π(dB : Π(v : Var), der_eq (tsort s') (B (VAR v A)) (B' (VAR v A))),
    Π(df : der_eq (tfun A B) f f'), Π(dg : der_eq (tfun A B) g g'),
    Π(de : der_eq (tfun A (λ u, teq (B u) (tapp A B f u) (tapp A B g u))) e e'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(HB : Π(v : Var), ITT.ε S (Peq _ _ _ (dB v))),
    Π(Hf : ITT.ε S (Peq _ _ _ df)), Π(Hg : ITT.ε S (Peq _ _ _ dg)),
    Π(He : ITT.ε S (Peq _ _ _ de)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_funext s s' f f' g g' A A' e e' B B' dA dB df dg de)))
  // CTX UIP
  → (Π(s : Sort), Π(e1 e1' e2 e2' u u' v v' A A' : Term),
    Π(dA : der_eq (tsort s) A A'), Π(du : der_eq A u u'), Π(dv : der_eq A v v'),
    Π(de1 : der_eq (teq A u v) e1 e1'), Π(de2 : der_eq (teq A u v) e2 e2'),
    Π(HA : ITT.ε S (Peq _ _ _ dA)), Π(Hu : ITT.ε S (Peq _ _ _ du)), Π(Hv : ITT.ε S (Peq _ _ _ dv)),
    Π(He1 : ITT.ε S (Peq _ _ _ de1)), Π(He2 : ITT.ε S (Peq _ _ _ de2)),
    ITT.ε S (Peq _ _ _ (der_eq_ctx_uip s e1 e1' e2 e2' u u' v v' A A' dA du dv de1 de2)))

  → der_ind_T S P Peq;

// Helpers
symbol der_ind S P Peq csort cprod csigma ctypeeq cvar cconv
               cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
               cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift
               ctxabs ctxapp ctxprod ctxpair ctxπ1 ctxπ2 ctxsum
               ctxrefl ctxJ ctxteq ctxfunext ctxuip
               ≔ get_der_ind S P Peq
                             (der_ind' S P Peq csort cprod csigma ctypeeq cvar cconv
                                       cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
                                       cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift
                                       ctxabs ctxapp ctxprod ctxpair ctxπ1 ctxπ2 ctxsum
                                       ctxrefl ctxJ ctxteq ctxfunext ctxuip);
symbol der_eq_ind S P Peq csort cprod csigma ctypeeq cvar cconv
                  cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
                  cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift
                  ctxabs ctxapp ctxprod ctxpair ctxπ1 ctxπ2 ctxsum
                  ctxrefl ctxJ ctxteq ctxfunext ctxuip
                  ≔ get_der_eq_ind S P Peq
                                   (der_ind' S P Peq csort cprod csigma ctypeeq cvar cconv
                                             cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
                                             cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift
                                             ctxabs ctxapp ctxprod ctxpair ctxπ1 ctxπ2 ctxsum
                                             ctxrefl ctxJ ctxteq ctxfunext ctxuip);

// Computation rules
// rule get_der_ind _ _ _ (der_ind' _ _ _ $csort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ (der_sort $s)
//   ↪ $csort $s
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_prod $s $s' $A $B $dA $dB)
//   ↪ $cprod $s $s' $A $B $dA $dB
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dB)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_sigma $s $s' $A $B $dA $dB)
//   ↪ $csigma $s $s' $A $B $dA $dB
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dB)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_prop_type_eq $s $A $u $v $dA $du $dv)
//   ↪ $ctypeeq $s $A $u $v $dA $du $dv
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
// with get_der_ind _ _ _ (der_ind' _ _ _ _ _ _ _ $cvar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ (der_var $A $v)
//   ↪ $cvar $A $v
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_type_conv $u $A $B $s $du $deq)
//   ↪ $cconv $u $A $B $s $du $deq
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (der_eq_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ _ $deq)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_abs $s $s' $A $t $B $dA $dB $dt)
//   ↪ $cabs $s $s' $A $t $B $dA $dB $dt
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dt v))
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_app $s $s' $A $t $u $B $dA $dB $dt $du)
//   ↪ $capp $s $s' $A $t $u $B $dA $dB $dt $du
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dt)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_pair $s $s' $u $A $v $B $dA $du $dB $dv)
//   ↪ $cpair $s $s' $u $A $v $B $dA $du $dB $dv
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_π1 $p $A $B $dp)
//   ↪ $cπ1 $p $A $B $dp
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dp)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_π2 $p $A $B $dp)
//   ↪ $cπ2 $p $A $B $dp
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dp)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_refl $s $u $A $dA $du)
//   ↪ $crefl $s $u $A $dA $du
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_uip $e1 $e2 $u $v $A $de1 $de2)
//   ↪ $cuip $e1 $e2 $u $v $A $de1 $de2
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de1)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de2)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_J $s $s' $A $u $v $p $w $E $dA $du $dv $dE $dp $dw)
//   ↪ $cJ $s $s' $A $u $v $p $w $E $dA $du $dv $dE $dp $dw
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
//         (λ v1 v2, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                           $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                           $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dE v1 v2))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dp)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dw)
// with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
//                  (der_funext $f $g $A $e $B $df $dg $de)
//   ↪ $cfunext $f $g $A $e $B $df $dg $de
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $df)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dg)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de)
// with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
//                  (der_eq_beta $s $s' $u $A $t $B $dA $dB $dt $du)
//   ↪ $cbeta $s $s' $u $A $t $B $dA $dB $dt $du
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dt v))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
// with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
//                  (der_eq_J $s $s' $u $A $w $E $dA $du $dE $dw)
//   ↪ $ceqJ $s $s' $u $A $w $E $dA $du $dE $dw
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (λ v1 v2, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                           $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                           $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dE v1 v2))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dw)
// with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
//                  (der_eq_π1 $s $s' $u $A $v $B $dA $du $dB $dv)
//   ↪ $ceqπ1 $s $s' $u $A $v $B $dA $du $dB $dv
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
// with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
//                  (der_eq_π2 $s $s' $u $A $v $B $dA $du $dB $dv)
//   ↪ $ceqπ2 $s $s' $u $A $v $B $dA $du $dB $dv
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
//         (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                       $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                       $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
// with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
//                  (der_eq_conversion $s $t1 $t2 $T1 $T2 $dT1 $dT2 $deqt $deqT)
//   ↪ $ceqconv $s $t1 $t2 $T1 $T2 $dT1 $dT2 $deqt $deqT
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dT1)
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dT2)
//         (der_eq_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ _ $deqt)
//         (der_eq_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ _ $deqT)
// with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                                     $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                                     $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
//                  (der_eq_lift $e $u $v $A $de)
//   ↪ $ceqlift $e $u $v $A $de
//         (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
//                  $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
//                  $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de);
