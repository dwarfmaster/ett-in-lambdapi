
require open ETT.main;
require ETT.itt as ITT;

symbol ε ≔ ITT.ε;

constant symbol der_ind_T :
  Π(S : ITT.Sort),
  Π(_ : Π(t T : Term), der t T → ITT.U S),
  Π(_ : Π(t1 t2 T : Term), der_eq t1 t2 T → ITT.U S),
  TYPE;
symbol get_der_ind (S : ITT.Sort) (P : Π(t T : Term), der t T → ITT.U S)
                   (Peq : Π(t1 t2 T : Term), der_eq t1 t2 T → ITT.U S) :
  der_ind_T S P Peq → Π(t T : Term), Π(d : der t T), ε S (P t T d);
symbol get_der_eq_ind (S : ITT.Sort) (P : Π(t T : Term), der t T → ITT.U S)
                   (Peq : Π(t1 t2 T : Term), der_eq t1 t2 T → ITT.U S) :
  der_ind_T S P Peq → Π(t1 t2 T : Term), Π(d : der_eq t1 t2 T), ε S (Peq t1 t2 T d);

symbol der_ind' :
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
    Π(du : der u A), Π(deq : der_eq (tsort s) A B),
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
  → (Π(s s' : Sort), Π(A u v p w : Term), Π(E : Term → Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A), Π(dv : der v A),
    Π(dE : Π(v1 v2 : Var), der (E (VAR v1 A) (VAR v2 (teq A u (VAR v1 A)))) (tsort s')),
    Π(dp : der p (teq A u v)), Π(dw : der w (E u (trefl A u))),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)), Π(Hv : ε S (P _ _ dv)),
    Π(HE : Π(v1 v2 : Var), ε S (P _ _ (dE v1 v2))),
    Π(Hp : ε S (P _ _ dp)), Π(Hw : ε S (P _ _ dw)),
    ε S (P _ _ (der_J s s' A u v p w E dA du dv dE dp dw)))
  // Function extensionality
  → (Π(f g A e : Term), Π(B : Term → Term),
    Π(df : der f (tfun A B)), Π(dg : der g (tfun A B)),
    Π(de : der e (tfun A (λ u, teq (B u) (tapp A B f u) (tapp A B g u)))),
    Π(Hf : ε S (P _ _ df)), Π(Hg : ε S (P _ _ dg)), Π(He : ε S (P _ _ de)),
    ε S (P _ _ (der_funext f g A e B df dg de)))

  // Computation
  // β-reduction
  → (Π(s s' : Sort), Π(u A : Term), Π(t B : Term → Term),
    Π(dA : der A (tsort s)), Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')),
    Π(dt : Π(v : Var), der (t (VAR v A)) (B (VAR v A))), Π(du : der u A),
    Π(HA : ε S (P _ _ dA)), Π(HB : Π(v : Var), ε S (P _ _ (dB v))),
    Π(Ht : Π(v : Var), ε S (P _ _ (dt v))), Π(Hu : ε S (P _ _ du)),
    ε S (Peq _ _ _ (der_eq_beta s s' u A t B dA dB dt du)))
  // J
  → (Π(s s' : Sort), Π(u A w : Term), Π(E : Term → Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(dE : Π(v1 v2 : Var), der (E (VAR v1 A) (VAR v2 (teq A u (VAR v1 A)))) (tsort s')),
    Π(dw : der w (E u (trefl A u))),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)),
    Π(HE : Π(v1 v2 : Var), ε S (P _ _ (dE v1 v2))), Π(Hw : ε S (P _ _ dw)),
    ε S (Peq _ _ _ (der_eq_J s s' u A w E dA du dE dw)))
  // π1
  → (Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')), Π(dv : der v (B u)),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)),
    Π(HB : Π(v : Var), ε S (P _ _ (dB v))), Π(Hv : ε S (P _ _ dv)),
    ε S (Peq _ _ _ (der_eq_π1 s s' u A v B dA du dB dv)))
  // π2
  → (Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
    Π(dA : der A (tsort s)), Π(du : der u A),
    Π(dB : Π(v : Var), der (B (VAR v A)) (tsort s')), Π(dv : der v (B u)),
    Π(HA : ε S (P _ _ dA)), Π(Hu : ε S (P _ _ du)),
    Π(HB : Π(v : Var), ε S (P _ _ (dB v))), Π(Hv : ε S (P _ _ dv)),
    ε S (Peq _ _ _ (der_eq_π2 s s' u A v B dA du dB dv)))
  // Conversion
  → (Π(s : Sort), Π(t1 t2 T1 T2 : Term),
    Π(dT1 : der T1 (tsort s)), Π(dT2 : der T2 (tsort s)),
    Π(deqt : der_eq T1 t1 t2), Π(deqT : der_eq (tsort s) T1 T2),
    Π(HT1 : ε S (P _ _ dT1)), Π(HT2 : ε S (P _ _ dT2)),
    Π(Heqt : ε S (Peq _ _ _ deqt)), Π(HeqT : ε S (Peq _ _ _ deqT)),
    ε S (Peq _ _ _ (der_eq_conversion s t1 t2 T1 T2 dT1 dT2 deqt deqT)))
  // Lifting
  → (Π(e u v A : Term), Π(de : der e (teq A u v)),
    Π(He : ε S (P _ _ de)), ε S (Peq _ _ _ (der_eq_lift e u v A de)))

  → der_ind_T S P Peq;

// Helpers
symbol der_ind S P Peq csort cprod csigma ctypeeq cvar cconv
               cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
               cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift
               ≔ get_der_ind S P Peq
                             (der_ind' S P Peq csort cprod csigma ctypeeq cvar cconv
                                       cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
                                       cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift);
symbol der_eq_ind S P Peq csort cprod csigma ctypeeq cvar cconv
                  cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
                  cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift
                  ≔ get_der_eq_ind S P Peq
                                   (der_ind' S P Peq csort cprod csigma ctypeeq cvar cconv
                                             cabs capp cpair cπ1 cπ2 crefl cuip cJ cfunext
                                             cbeta ceqJ ceqπ1 ceqπ2 ceqconv ceqlift);

// Computation rules
rule get_der_ind _ _ _ (der_ind' _ _ _ $csort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ (der_sort $s)
  ↪ $csort $s
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_prod $s $s' $A $B $dA $dB)
  ↪ $cprod $s $s' $A $B $dA $dB
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dB)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_sigma $s $s' $A $B $dA $dB)
  ↪ $csigma $s $s' $A $B $dA $dB
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dB)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_prop_type_eq $s $A $u $v $dA $du $dv)
  ↪ $ctypeeq $s $A $u $v $dA $du $dv
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
with get_der_ind _ _ _ (der_ind' _ _ _ _ _ _ _ $cvar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ (der_var $A $v)
  ↪ $cvar $A $v
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_type_conv $u $A $B $s $du $deq)
  ↪ $cconv $u $A $B $s $du $deq
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (der_eq_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ _ $deq)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_abs $s $s' $A $t $B $dA $dB $dt)
  ↪ $cabs $s $s' $A $t $B $dA $dB $dt
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dt v))
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_app $s $s' $A $t $u $B $dA $dB $dt $du)
  ↪ $capp $s $s' $A $t $u $B $dA $dB $dt $du
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dt)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_pair $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ $cpair $s $s' $u $A $v $B $dA $du $dB $dv
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_π1 $p $A $B $dp)
  ↪ $cπ1 $p $A $B $dp
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dp)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_π2 $p $A $B $dp)
  ↪ $cπ2 $p $A $B $dp
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dp)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_refl $s $u $A $dA $du)
  ↪ $crefl $s $u $A $dA $du
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_uip $e1 $e2 $u $v $A $de1 $de2)
  ↪ $cuip $e1 $e2 $u $v $A $de1 $de2
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de1)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de2)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_J $s $s' $A $u $v $p $w $E $dA $du $dv $dE $dp $dw)
  ↪ $cJ $s $s' $A $u $v $p $w $E $dA $du $dv $dE $dp $dw
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
        (λ v1 v2, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                          $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                          $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dE v1 v2))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dp)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dw)
with get_der_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _
                 (der_funext $f $g $A $e $B $df $dg $de)
  ↪ $cfunext $f $g $A $e $B $df $dg $de
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $df)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dg)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de)
with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
                 (der_eq_beta $s $s' $u $A $t $B $dA $dB $dt $du)
  ↪ $cbeta $s $s' $u $A $t $B $dA $dB $dt $du
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dt v))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
                 (der_eq_J $s $s' $u $A $w $E $dA $du $dE $dw)
  ↪ $ceqJ $s $s' $u $A $w $E $dA $du $dE $dw
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (λ v1 v2, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                          $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                          $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dE v1 v2))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dw)
with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
                 (der_eq_π1 $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ $ceqπ1 $s $s' $u $A $v $B $dA $du $dB $dv
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
                 (der_eq_π2 $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ $ceqπ2 $s $s' $u $A $v $B $dA $du $dB $dv
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dA)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $du)
        (λ v, der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                      $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                      $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ ($dB v))
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dv)
with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
                 (der_eq_conversion $s $t1 $t2 $T1 $T2 $dT1 $dT2 $deqt $deqT)
  ↪ $ceqconv $s $t1 $t2 $T1 $T2 $dT1 $dT2 $deqt $deqT
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dT1)
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $dT2)
        (der_eq_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ _ $deqt)
        (der_eq_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ _ $deqT)
with get_der_eq_ind _ _ _ (der_ind' $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                                    $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                                    $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift) _ _ _
                 (der_eq_lift $e $u $v $A $de)
  ↪ $ceqlift $e $u $v $A $de
        (der_ind $S $P $Peq $csort $cprod $csigma $ctypeeq $cvar $cconv
                 $cabs $capp $cpair $cπ1 $cπ2 $crefl $cuip $cJ $cfunext
                 $cbeta $ceqJ $ceqπ1 $ceqπ2 $ceqconv $ceqlift _ _ $de);
