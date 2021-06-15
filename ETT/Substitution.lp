
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.Packing;
require open ETT.Congruences;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;
require open ETT.Translation;
require open ETT.TContext;

symbol magic {s : Sort} (A : U s) : ε s A;
symbol magic_teq (t1 t2 : ETT.Term) : TEq t1 t2;
symbol magic_der_eq (Γ : Context) (s : ETT.Sort) (T t1 t2 : ETT.Term) : der_eq Γ s T t1 t2;

// SubstContext
constant symbol SubstContext {Γ : Context} {A : ETT.Term} {s : ETT.Sort} : der Γ A (ETT.tsort s) (ETT.snext s) → ETT.DBId → TYPE;
symbol sc_to_ctx {Γ : Context} {A : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                 : SubstContext d id → Context;
symbol sc_to_dctx {Γ : Context} {A : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                  (sc : SubstContext d id) : der_context (sc_to_ctx sc);
symbol sc_to_sctx {Γ : Context} {A t : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                  (d : der Γ t A s) : SubstContext (inv_sort d) id → Context;
symbol sc_to_dsctx {Γ : Context} {A t : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                   (dt : der Γ t A s) (sc : SubstContext (inv_sort dt) id) : der_context (sc_to_sctx dt sc);

constant symbol SC0 {Γ : Context} {s : ETT.Sort} {A : ETT.Term} (d : der Γ A (ETT.tsort s) (ETT.snext s)) : SubstContext d db0;
constant symbol SCPush {Γ : Context} {s s' : ETT.Sort} {A B : ETT.Term} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                       (sc : SubstContext d id) : der (sc_to_ctx sc) B (ETT.tsort s') (ETT.snext s') → SubstContext d (dbsucc id);

rule sc_to_ctx (@SC0 $Γ $s $A _) ↪ Push $A $s $Γ
with sc_to_ctx (@SCPush _ _ $s _ $B _ _ $sc _) ↪ Push $B $s (sc_to_ctx $sc)
with sc_to_sctx _ (@SC0 $Γ _ _ _) ↪ $Γ
with @sc_to_sctx _ _ $t _ _ $dt (@SCPush _ _ $s _ $B _ $id $sc _) ↪ Push (subst $id (Shift* $id $t) $B) $s (sc_to_sctx $dt $sc);
rule sc_to_dctx (SC0 $d) ↪ pushΓ $d
with sc_to_dctx (SCPush _ $dB) ↪ pushΓ $dB;

// TODO deq_cong_subst
symbol deq_cong_subst {Γ : Context} (id : ETT.DBId)
                      {s s' : ETT.Sort} {A1 A2 B1 f1 f2 : ETT.Term} (t1 t2 : ETT.Term)
                      (deqA : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2)
                      (dt1 : der Γ t1 A1 s) (dt2 : der Γ t2 A2 s)
                      (sc1 : SubstContext (inv_sort dt1) id)
                      (_ : der_eq (sc_to_ctx sc1) s' B1 f1 f2) (_ : der_eq Γ s A1 t1 t2)
                      : der_eq (sc_to_sctx dt1 sc1) s' (subst id (Shift* id t1) B1) (subst id (Shift* id t1) f1) (subst id (Shift* id t2) f2);
// TODO deq_subst_convert
symbol deq_subst_convert {Γ : Context} (id : ETT.DBId)
                         {s s' : ETT.Sort} {A1 A2 B f : ETT.Term} (t1 t2 : ETT.Term)
                         (deqA : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2)
                         (dt1 : der Γ t1 A1 s) (dt2 : der Γ t2 A2 s)
                         (sc1 : SubstContext (inv_sort dt1) id)
                         (_ : der (sc_to_ctx sc1) f B s') (_ : der_eq Γ s A1 t1 t2)
                         : der_eq (sc_to_sctx dt1 sc1) s' (subst id (Shift* id t1) B) (subst id (Shift* id t1) f) (subst id (Shift* id t2) f);
rule @der_eq_cong_apply _ _ _ _ _ _ _ _ _ $deqA $deqB $deqt _ _ $dt1 $dt2
  ↪ deq_cong_subst db0 _ _ $deqA $dt1 $dt2
                    (SC0 (inv_sort $dt1))
                    $deqB $deqt;

symbol der_subst {Γ : Context} (id : ETT.DBId)
                 {s s' : ETT.Sort} {A B C u : ETT.Term}
                 (du : der Γ u A s) (sc : SubstContext (inv_sort du) id)
                 (_ : der (sc_to_ctx sc) C B s')
                 : der (sc_to_sctx du sc) (subst id (Shift* id u) C) (subst id (Shift* id u) B) s';
symbol der_context_subst
       {Γ : Context} (id : ETT.DBId)
       {s : ETT.Sort} {A u : ETT.Term}
       (d : der Γ u A s) (sc : SubstContext (inv_sort d) id)
       (i : ETT.DBId)
       : der (sc_to_sctx d sc) (dbselect id i (Shift* id u) (ETT.var i) (ETT.var (dbprev i)))
             (subst id (Shift* id u) (ShiftN i (get (sc_to_ctx sc) i)))
             (getS (sc_to_ctx sc) i);
symbol der_eq_subst {Γ : Context} (id : ETT.DBId)
                    {s s' : ETT.Sort} {A B C1 C2 u : ETT.Term}
                    (du : der Γ u A s) (sc : SubstContext (inv_sort du) id)
                    (_ : der_eq (sc_to_ctx sc) s' B C1 C2)
                    : der_eq (sc_to_sctx du sc) s' (subst id (Shift* id u) B) (subst id (Shift* id u) C1) (subst id (Shift* id u) C2);

rule substitution $dB $du ↪ der_subst db0 $du (SC0 (inv_sort $du)) $dB;

rule sc_to_dsctx _ (SC0 $dA) ↪ inv_context $dA
with sc_to_dsctx $d (SCPush $sc $dA) ↪ der_context_push _ _ _ (der_subst _ $d $sc $dA) (sc_to_dsctx $d $sc);

// Types
rule der_subst _ $d $sc (der_sort _ $s _) ↪ der_sort (sc_to_sctx $d $sc) $s (sc_to_dsctx $d $sc)
with der_subst $id $d $sc (der_prod _ $s $s' _ _ $dA $dB)
  ↪ der_prod (sc_to_sctx $d $sc) $s $s' _ _
              (der_subst $id $d $sc $dA)
              (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
with der_subst $id $d $sc (der_sigma _ $s $s' _ _ $dA $dB)
  ↪ der_sigma (sc_to_sctx $d $sc) $s $s' _ _
               (der_subst $id $d $sc $dA)
               (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
with der_subst $id $d $sc (der_prop_type_eq _ $s _ _ _ $dA $du $dv)
  ↪ der_prop_type_eq _ $s _ _ _
                      (der_subst $id $d $sc $dA)
                      (der_subst $id $d $sc $du)
                      (der_subst $id $d $sc $dv)

// Structural
with der_subst $id $d $sc (der_var _ $i _)
  ↪ der_context_subst $id $d $sc $i
with der_context_subst db0 $d (SC0 _) db0
  ↪ $d
with @der_context_subst _ (dbsucc $id) _ _ $x $d (@SCPush _ _ _ _ $A _ _ $sc $dA) db0
  ↪ JT (teq_inv (teq_subst_shift $id (Shift* $id $x) $A))
        (der_var (sc_to_sctx $d (SCPush $sc $dA)) db0 (sc_to_dsctx $d (SCPush $sc $dA)))
with @der_context_subst _ db0 _ _ $x _ (@SC0 $Γ _ _ $dA) (dbsucc $i)
  ↪ JT (teq_inv (teq_shift_cancel_subst db0 $x (Shift* $i (get $Γ $i))))
        (der_var $Γ $i (inv_context $dA))
with @der_context_subst _ (dbsucc $id) _ _ $x $d (SCPush $sc $dA) (dbsucc $i)
  ↪ JtT (teq_inv (teq_select_shift $id $i (Shift* $id $x)))
         (teq_inv (teq_subst_shift $id (Shift* $id $x) (ShiftN $i (get (sc_to_ctx $sc) $i))))
         (der_shift0
           (der_subst _ $d $sc $dA)
           (der_context_subst $id $d $sc $i))
with der_subst _ $d $sc (der_type_conv _ _ _ _ $s $du $deq)
  ↪ der_type_conv _ _ _ _ $s
                   (der_subst _ $d $sc $du)
                   (der_eq_subst _ $d $sc $deq)
with der_eq_subst $id $d $sc $deq
  ↪ deq_cong_subst $id _ _ (der_eq_refl _ _ _ _ (inv_sort $d)) $d $d $sc
                    $deq (der_eq_refl _ _ _ _ $d)

// λ-calculus
with der_subst $id $d $sc (der_abs _ $s $s' _ _ _ $dA $dB $dt)
  ↪ der_abs _ $s $s' _ _ _
             (der_subst $id $d $sc $dA)
             (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
             (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dt)
with @der_subst _ $id _ _ _ _ _ $x $d $sc (der_app _ $s $s' _ _ $a $B $dA $dB $df $da)
  ↪ JT (teq_inv (teq_subst_apply $id $x $a $B))
        (der_app _ $s $s' _ _ _ _
                 (der_subst $id $d $sc $dA)
                 (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
                 (der_subst $id $d $sc $df)
                 (der_subst $id $d $sc $da))
with @der_subst _ $id _ _ _ _ _ $x $d $sc (der_pair _ $s $s' $u _ _ $B $dA $du $dB $dv)
  ↪ der_pair _ $s $s' _ _ _ _
              (der_subst $id $d $sc $dA)
              (der_subst $id $d $sc $du)
              (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
              (JT (teq_subst_apply $id $x $u $B)
                  (der_subst $id $d $sc $dv))
with der_subst $id $d $sc (der_π1 _ $s $s' _ _ _ $dA $dB $dp)
  ↪ der_π1 _ $s $s' _ _ _
            (der_subst $id $d $sc $dA)
            (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
            (der_subst $id $d $sc $dp)
with @der_subst _ $id _ _ _ _ _ $x $d $sc (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ JT (teq_inv (teq_subst_apply $id $x (ETT.π1 $A $B $p) $B))
        (der_π2 _ $s $s' _ _ _
                (der_subst $id $d $sc $dA)
                (der_subst (dbsucc $id) $d (SCPush $sc $dA) $dB)
                (der_subst $id $d $sc $dp))
// Equality
with der_subst $id $d $sc (der_refl _ $s _ _ $dA $du)
  ↪ der_refl _ $s _ _
              (der_subst $id $d $sc $dA)
              (der_subst $id $d $sc $du)
;

// SubstTContext
constant symbol SubstTContext (Γ : TContext) {t A : ETT.Term} {s : ETT.Sort} : der (τ_Γ Γ) t A s → ETT.DBId → TYPE;
symbol tsc_to_tc {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                 : SubstTContext Γ d id → TContext;
symbol tsc_to_stc {Γ : TContext} {A t : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                  : SubstTContext Γ d id → TContext;
symbol tsc_to_sc {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                 : SubstTContext Γ d id → SubstContext (inv_sort d) id;

symbol tsc_to_ctx {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                 : SubstTContext Γ d id → Context;
rule tsc_to_ctx $sc ↪ sc_to_ctx (tsc_to_sc $sc)
with τ_Γ (tsc_to_tc $sc) ↪ sc_to_ctx (tsc_to_sc $sc);
symbol tsc_to_sctx {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                  : SubstTContext Γ d id → Context;
rule @tsc_to_sctx _ _ _ _ $d _ $sc ↪ sc_to_sctx $d (tsc_to_sc $sc)
with τ_Γ (@tsc_to_stc _ _ _ _ $d _ $sc) ↪ sc_to_sctx $d (tsc_to_sc $sc);

constant symbol TSC0 (Γ : TContext) {s : ETT.Sort} {t A : ETT.Term} (d : der (τ_Γ Γ) t A s) : SubstTContext Γ d db0;
constant symbol TSCPush {Γ : TContext} {s s' : ETT.Sort} {t A B : ETT.Term} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                        (sc : SubstTContext Γ d id) (dB : der (tsc_to_ctx sc) B (ETT.tsort s') (ETT.snext s'))
                        : ε _ (τ (tsc_to_tc sc) dB) → SubstTContext Γ d (dbsucc id);

rule tsc_to_tc (TSC0 $Γ $d) ↪ TPush $Γ _ _ (inv_sort $d) (τ $Γ $d)
with tsc_to_tc (TSCPush $sc $dB $b) ↪ TPush (tsc_to_tc $sc) _ _ $dB $b
with tsc_to_sc (TSC0 _ $d) ↪ SC0 (inv_sort $d)
with tsc_to_sc (TSCPush $sc $dB _) ↪ SCPush (tsc_to_sc $sc) $dB;

symbol τ_subst_n {Γ : TContext} (id : ETT.DBId)
                 {s s' : ETT.Sort} {A B b a : ETT.Term}
                 (da : der (τ_Γ Γ) a A s) (sc : SubstTContext Γ da id)
                 (db : der (tsc_to_ctx sc) b B s') :
  H (τ (tsc_to_tc sc) db)
    (τ (tsc_to_stc sc) (der_subst id da (tsc_to_sc sc) db));
symbol τ_context_subst_n
       {Γ : TContext} (id : ETT.DBId)
       {s : ETT.Sort} {A u : ETT.Term}
       (d : der (τ_Γ Γ) u A s) (sc : SubstTContext Γ d id)
       (i : ETT.DBId)
       : H (tgetShift i (tsc_to_tc sc))
           (τ (tsc_to_stc sc) (der_context_subst id d (tsc_to_sc sc) i));

rule tsc_to_stc (TSC0 $Γ _) ↪ $Γ
with tsc_to_stc (@TSCPush _ _ _ _ _ _ $d $id $sc $dB $b)
   ↪ TPush (tsc_to_stc $sc) _ _
            (der_subst $id $d (tsc_to_sc $sc) $dB)
            (transport (heq_to_eq (τ_subst_n $id $d $sc $dB)) $b);
rule τ_subst_eq $Γ $db $da ↪ τ_subst_n db0 $da (TSC0 $Γ $da) $db
with τ_substT_eq $Γ $dB $da ↪ heq_to_eq (τ_subst_eq $Γ $dB $da);

// Helper to work with term equality
symbol τtT (Γ : TContext) {s : ETT.Sort} {t1 t2 T1 T2 : ETT.Term}
           (eqt : TEq t1 t2) (eqT : TEq T1 T2)
           (d : der (τ_Γ Γ) t1 T1 s)
           : H (τ Γ d)
               (τ Γ (JtT eqt eqT d));
symbol τT (Γ : TContext) {s : ETT.Sort} {t T1 T2 : ETT.Term}
          (eqT : TEq T1 T2) (d : der (τ_Γ Γ) t T1 s)
          : H (τ Γ d)
              (τ Γ (JT eqT d));
symbol τt (Γ : TContext) {s : ETT.Sort} {t1 t2 T : ETT.Term}
          (eqt : TEq t1 t2) (d : der (τ_Γ Γ) t1 T s)
          : H (τ Γ d)
              (τ Γ (Jt eqt d));
rule τtT $Γ (TRefl _) (TRefl _) $d ↪ heq_refl _ (τ $Γ $d)
with @τt $Γ _ _ _ $T $eqt $d ↪ τtT $Γ $eqt (TRefl $T) $d
with @τT $Γ _ $t _ _ $eqT $d ↪ τtT $Γ (TRefl $t) $eqT $d;


// Types
rule τ_subst_n _ _ _ (der_sort _ $s _)
  ↪ heq_refl _ (u (τ_s $s))
with τ_subst_n $id $d $sc (der_prod _ $s _ $A _ $dA $dB)
  ↪ cong_prod
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id $d (tsc_to_sc $sc) $dA) a)
                      (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (τ_subst_n $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n _ $d (TSCPush $sc $dA (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) $dA) (der_subst $id $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
with τ_subst_n $id $d $sc (der_sigma _ $s _ $A _ $dA $dB)
  ↪ cong_sum
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id $d (tsc_to_sc $sc) $dA) a)
                      (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (τ_subst_n $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n _ $d (TSCPush $sc $dA (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) $dA) (der_subst $id $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
with τ_subst_n $id $d $sc (der_prop_type_eq _ _ _ _ _ $dA $da1 $da2)
  ↪ cong_eq
       (τ_subst_n $id $d $sc $dA)
       (heq_conj
         (τ_subst_n $id $d $sc $da1)
         (convert_T (tsc_to_tc $sc) (inv_sort $da1) $dA)
         (convert_T (tsc_to_stc $sc) (inv_sort (der_subst $id $d (tsc_to_sc $sc) $da1)) (der_subst $id $d (tsc_to_sc $sc) $dA)))
       (heq_conj
         (τ_subst_n $id $d $sc $da2)
         (convert_T (tsc_to_tc $sc) (inv_sort $da2) $dA)
         (convert_T (tsc_to_stc $sc) (inv_sort (der_subst $id $d (tsc_to_sc $sc) $da2)) (der_subst $id $d (tsc_to_sc $sc) $dA)))
// Structural rules
with τ_subst_n $id $d $sc (der_var _ $i $dΓ)
  ↪ heq_trans
       (heq_symm (heq_of_transport
         (tgetShift $i (tsc_to_tc $sc))
         (convert_T (tsc_to_tc $sc)
                    (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc)))
                    (der_shift $i $dΓ (der_getΓ $i $dΓ)))))
       (τ_context_subst_n $id $d $sc $i)
with τ_context_subst_n db0 _ (TSC0 $Γ $d) db0
  ↪ heq_symm (heq_of_transport
       (τ $Γ $d)
       (τ_shift0T_eq $Γ (inv_sort $d) (inv_sort $d) (τ $Γ $d)))
with @τ_context_subst_n _ (dbsucc $id) _ _ $x $d (@TSCPush _ _ _ _ _ $A _ _ $sc $dA $a) db0
  ↪ heq_trans
       (heq_trans
         (heq_symm (heq_of_transport $a
           (τ_shift0T_eq (tsc_to_tc $sc) $dA $dA $a)))
         (heq_trans
           (heq_trans
             (heq_of_transport $a
               (heq_to_eq (τ_subst_n $id $d $sc $dA)))
             (heq_of_transport
               (transport (heq_to_eq (τ_subst_n $id $d $sc $dA)) $a)
               (τ_shift0T_eq (tsc_to_stc $sc)
                 (der_subst _ $d (tsc_to_sc $sc) $dA)
                 (der_subst _ $d (tsc_to_sc $sc) $dA)
                 (transport (heq_to_eq (τ_subst_n $id $d $sc $dA)) $a))))
           (heq_of_transport
             (tgetShift db0 (tsc_to_stc (TSCPush $sc $dA $a)))
             (convert_T (tsc_to_stc (TSCPush $sc $dA $a))
                        (der_shift db0 (τ_dΓ (tsc_to_stc (TSCPush $sc $dA $a))) (tgetD db0 (tsc_to_stc (TSCPush $sc $dA $a))))
                        (der_shift db0 (sc_to_dsctx $d (SCPush (tsc_to_sc $sc) $dA)) (der_getΓ db0 (sc_to_dsctx $d (SCPush (tsc_to_sc $sc) $dA))))))))
       (τT (tsc_to_stc (TSCPush $sc $dA $a)) (teq_inv (teq_subst_shift $id (Shift* $id $x) $A))
           (der_var (sc_to_sctx $d (SCPush (tsc_to_sc $sc) $dA)) db0 (sc_to_dsctx $d (SCPush (tsc_to_sc $sc) $dA))))
with @τ_context_subst_n _ db0 _ _ $x _ (TSC0 $Γ $d) (dbsucc $i)
  ↪ heq_trans
       (heq_conj
         (heq_refl _ (tgetShift $i $Γ))
         (τ_shift0T_eq $Γ (der_shift $i (τ_dΓ $Γ) (tgetD $i $Γ)) (inv_sort $d) (τ $Γ $d))
         (convert_T $Γ
           (der_shift $i (τ_dΓ $Γ) (tgetD $i $Γ))
           (der_shift $i (inv_context (inv_sort $d)) (der_getΓ $i (inv_context (inv_sort $d))))))
       (τT $Γ (teq_inv (teq_shift_cancel_subst db0 $x (Shift* $i (get (τ_Γ $Γ) $i))))
           (der_var (τ_Γ $Γ) $i (inv_context (inv_sort $d))))
with @τ_context_subst_n _ (dbsucc $id) _ _ $x $d (TSCPush $sc $dA $a) (dbsucc $i)
  ↪ heq_trans
       (heq_trans
         (heq_trans
           (heq_symm (heq_of_transport
             (tgetShift $i (tsc_to_tc $sc))
             (τ_shift0T_eq (tsc_to_tc $sc) (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc))) $dA $a)))
           (τ_context_subst_n $id $d $sc $i))
         (τ_shift0_eq (tsc_to_stc $sc) (der_context_subst $id $d (tsc_to_sc $sc) $i)
                      (der_subst $id $d (tsc_to_sc $sc) $dA)
                      (transport (heq_to_eq (τ_subst_n $id $d $sc $dA)) $a)))
       (τtT (tsc_to_stc (TSCPush $sc $dA $a))
            (teq_inv (teq_select_shift $id $i (Shift* $id $x)))
            (teq_inv (teq_subst_shift $id (Shift* $id $x) (ShiftN $i (get (tsc_to_ctx $sc) $i))))
            (der_shift0
              (der_subst _ $d (tsc_to_sc $sc) $dA)
              (der_context_subst $id $d (tsc_to_sc $sc) $i)))
with τ_subst_n $id $d $sc (der_type_conv _ _ _ _ _ $du $deq)
  ↪ heq_conj
       (heq_conj
         (τ_subst_n $id $d $sc $du)
         (convert_T (tsc_to_tc $sc) (inv_sort $du) (inv_eq_t1 $deq))
         (convert_T (tsc_to_stc $sc)
                    (inv_sort (der_subst $id $d (tsc_to_sc $sc) $du))
                    (inv_eq_t1 (der_eq_subst $id $d (tsc_to_sc $sc) $deq))))
       (τ_eqT (tsc_to_tc $sc) $deq)
       (τ_eqT (tsc_to_stc $sc) (der_eq_subst $id $d (tsc_to_sc $sc) $deq))
// λ-calculus
with τ_subst_n $id $d $sc (der_abs _ $s _ $A _ _ $dA _ $dt)
  ↪ cong_lambda
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) (inv_sort $dt))
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id $d (tsc_to_sc $sc) $dA) a)
                      (inv_sort (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dt)))
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dt)
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id $d (tsc_to_sc $sc) $dA) a)
                      (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dt))
       (τ_subst_n $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n _ $d (TSCPush $sc $dA (projT1 p)) (inv_sort $dt))
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) $dA) (der_subst $id $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) (inv_sort $dt))
                   (inv_sort (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dt))))
       (λ p, heq_trans
         (τ_subst_n _ $d (TSCPush $sc $dA (projT1 p)) $dt)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) $dA) (der_subst $id $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dt)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dt)))
with @τ_subst_n _ $id _ _ _ _ _ $x $d $sc (der_app _ $s $s' $A _ $a $B $dA $dB $df $da)
  ↪ heq_trans
       (heq_conj
         (cong_app
           (λ a, τ (TPush (tsc_to_tc $sc) $s $A (inv_sort $da) a) $dB)
           (λ a, τ (TPush (tsc_to_stc $sc) $s _ (inv_sort (der_subst _ $d (tsc_to_sc $sc) $da)) a)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB))
           (heq_trans
             (τ_subst_n _ $d $sc (inv_sort $da))
             (convert (tsc_to_stc $sc)
               (der_subst _ $d (tsc_to_sc $sc) (inv_sort $da))
               (inv_sort (der_subst _ $d (tsc_to_sc $sc) $da))))
           (λ p, heq_trans
             (τ_subst_n _ $d (TSCPush $sc (inv_sort $da) (projT1 p)) $dB)
             (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) (inv_sort $da)) (inv_sort (der_subst $id $d (tsc_to_sc $sc) $da))
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc (inv_sort $da))))) (projHEq p)))
                       (der_subst _ $d (SCPush (tsc_to_sc $sc) (inv_sort $da)) $dB)
                       (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
           (heq_conj
             (τ_subst_n _ $d $sc $df)
             (τ_fun_eq (tsc_to_tc $sc) (inv_sort $da) $dB (inv_sort $df))
             (τ_fun_eq (tsc_to_stc $sc)
                       (inv_sort (der_subst _ $d (tsc_to_sc $sc) $da))
                       (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                       (inv_sort (der_subst _ $d (tsc_to_sc $sc) $df))))
           (τ_subst_n _ $d $sc $da))
         (τ_substT_eq (tsc_to_tc $sc) $dB $da)
         (τ_substT_eq (tsc_to_stc $sc)
                      (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                      (der_subst _ $d (tsc_to_sc $sc) $da)))
       (τT (tsc_to_stc $sc) (teq_inv (teq_subst_apply $id $x $a $B))
           (der_app _ $s $s' _ _ _ _
                    (der_subst _ $d (tsc_to_sc $sc) $dA)
                    (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                    (der_subst _ $d (tsc_to_sc $sc) $df)
                    (der_subst _ $d (tsc_to_sc $sc) $da)))
with @τ_subst_n _ $id _ _ _ _ _ $x $d $sc (der_pair _ $s _ $u $A _ $B $dA $du $dB $dv)
  ↪ cong_pair
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A (inv_sort $du) a) $dB)
       (λ a, τ (TPush (tsc_to_stc $sc) $s _ (inv_sort (der_subst _ $d (tsc_to_sc $sc) $du)) a)
               (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (heq_trans
         (τ_subst_n _ $d $sc (inv_sort $du))
         (convert (tsc_to_stc $sc)
           (der_subst _ $d (tsc_to_sc $sc) (inv_sort $du))
           (inv_sort (der_subst _ $d (tsc_to_sc $sc) $du))))
       (λ p, heq_trans
         (τ_subst_n _ $d (TSCPush $sc (inv_sort $du) (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) (inv_sort $du)) (inv_sort (der_subst $id $d (tsc_to_sc $sc) $du))
                         (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc (inv_sort $du))))) (projHEq p)))
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) (inv_sort $du)) $dB)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
       (τ_subst_n _ $d $sc $du)
       (heq_conj
         (heq_conj
           (heq_trans
             (τ_subst_n _ $d $sc $dv)
             (τT (tsc_to_stc $sc) (teq_subst_apply $id $x $u $B) (der_subst _ $d (tsc_to_sc $sc) $dv)))
           (convert_T (tsc_to_tc $sc) (inv_sort $dv) (substitution $dB $du))
           (convert_T (tsc_to_stc $sc)
                      (inv_sort (JT (teq_subst_apply $id $x $u $B) (der_subst _ $d (tsc_to_sc $sc) $dv)))
                      (substitution (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB) (der_subst _ $d (tsc_to_sc $sc) $du))))
         (inv_eq (τ_substT_eq (tsc_to_tc $sc) $dB $du))
         (inv_eq (τ_substT_eq (tsc_to_stc $sc)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ $d (tsc_to_sc $sc) $du))))
with τ_subst_n $id $d $sc (der_π1 _ $s _ _ $A _ $dA $dB $dp)
  ↪ cong_proj1
       (λ a, τ_T (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ_T (TPush (tsc_to_stc $sc) _ _ (der_subst _ $d (tsc_to_sc $sc) $dA) a)
                 (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (τ_subst_n $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n _ $d (TSCPush $sc $dA (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) $dA) (der_subst $id $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
       (heq_conj
         (τ_subst_n _ $d $sc $dp)
         (τ_sum_eq (tsc_to_tc $sc) $dA $dB (inv_sort $dp))
         (τ_sum_eq (tsc_to_stc $sc)
                   (der_subst _ $d (tsc_to_sc $sc) $dA)
                   (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (inv_sort (der_subst _ $d (tsc_to_sc $sc) $dp))))
with @τ_subst_n _ $id _ _ _ _ _ $x $d $sc (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ heq_trans
       (heq_conj
         (cong_proj2
           (λ a, τ_T (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
           (λ a, τ_T (TPush (tsc_to_stc $sc) _ _ (der_subst _ $d (tsc_to_sc $sc) $dA) a)
                     (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB))
           (τ_subst_n $id $d $sc $dA)
           (λ p, heq_trans
             (τ_subst_n _ $d (TSCPush $sc $dA (projT1 p)) $dB)
             (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id $d (tsc_to_sc $sc) $dA) (der_subst $id $d (tsc_to_sc $sc) $dA)
                                 (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $id $d $sc $dA)))) (projHEq p)))
                       (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                       (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
           (heq_conj
             (τ_subst_n _ $d $sc $dp)
             (τ_sum_eq (tsc_to_tc $sc) $dA $dB (inv_sort $dp))
             (τ_sum_eq (tsc_to_stc $sc)
                       (der_subst _ $d (tsc_to_sc $sc) $dA)
                       (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                       (inv_sort (der_subst _ $d (tsc_to_sc $sc) $dp)))))
         (τ_substT_eq (tsc_to_tc $sc) $dB (der_π1 (tsc_to_ctx $sc) $s $s' $p $A $B $dA $dB $dp))
         (τ_substT_eq (tsc_to_stc $sc)
           (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
           (der_π1 (tsc_to_sctx $sc) $s $s' _ _ _
             (der_subst _ $d (tsc_to_sc $sc) $dA)
             (der_subst _ $d (SCPush (tsc_to_sc $sc) $dA) $dB)
             (der_subst _ $d (tsc_to_sc $sc) $dp))))
       (τT (tsc_to_stc $sc)
           (teq_inv (teq_subst_apply $id $x (ETT.π1 $A $B $p) $B))
           (der_π2 _ $s $s' _ _ _
                   (der_subst $id $d (tsc_to_sc $sc) $dA)
                   (der_subst (dbsucc $id) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst $id $d (tsc_to_sc $sc) $dp)))
with τ_subst_n $id $d $sc (der_refl _ _ _ _ $dA $du)
  ↪ cong_refl
       (τ_subst_n $id $d $sc $dA)
       (heq_conj
         (τ_subst_n $id $d $sc $du)
         (convert_T (tsc_to_tc $sc) (inv_sort $du) $dA)
         (convert_T (tsc_to_stc $sc)
                    (inv_sort (der_subst _ $d (tsc_to_sc $sc) $du))
                    (der_subst _ $d (tsc_to_sc $sc) $dA)))
;


rule deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_beta _ $s $s' $u _ $t $B $dA $dB $dt $du) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (Jeq (teq_inv (teq_subst_apply $id $r1 $u $B))
            (TRefl _)
            (teq_inv (teq_subst_apply $id $r1 $u $t))
            (der_eq_beta (sc_to_sctx $dr1 $sc1) $s $s' _ _ _ _
                         (der_subst _ $dr1 $sc1 $dA)
                         (der_subst _ $dr1 (SCPush $sc1 $dA) $dB)
                         (der_subst _ $dr1 (SCPush $sc1 $dA) $dt)
                         (der_subst _ $dr1 $sc1 $du)))
       (deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1
                       (der_eq_subst db0 $du (SC0 (inv_sort $du)) (der_eq_refl _ _ _ _ $dt))
                       $deqr)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_eta _ $s $s' $A $f $B $dA $dB $df) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (Jeq (TRefl _)
            (Jcong (ETT.tabs (subst $id (Shift* $id $r1) $A) (subst (dbsucc $id) (Shift* (dbsucc $id) $r1) $B))
              (teq_trans
                (Jcong
                  (λ t, ETT.tapp t
                          (Shift1 (subst (dbsucc $id) (Shift* (dbsucc $id) $r1) $B))
                          (Shift (subst $id (Shift* $id $r1) $f))
                          (ETT.var db0))
                  (teq_inv (teq_subst_shift $id (Shift* $id $r1) $A)))
                (teq_trans
                  (Jcong
                    (λ t, ETT.tapp (subst (dbsucc $id) (Shift (Shift* $id $r1)) (Shift $A))
                            (Shift1 (subst (dbsucc $id) (Shift* (dbsucc $id) $r1) $B))
                            t (ETT.var db0))
                    (teq_inv (teq_subst_shift $id (Shift* $id $r1) $f)))
                  (Jcong
                    (λ t, ETT.tapp (subst (dbsucc $id) (Shift (Shift* $id $r1)) (Shift $A)) t
                            (subst (dbsucc $id) (Shift (Shift* $id $r1)) (Shift $f))
                            (ETT.var db0))
                    (teq_inv (teq_subst_shift1 $id (Shift* $id $r1) $B))))))
            (TRefl _)
            (der_eq_eta _ $s $s' _ _ _
                        (der_subst _ $dr1 $sc1 $dA)
                        (der_subst _ $dr1 (SCPush $sc1 $dA) $dB)
                        (der_subst _ $dr1 $sc1 $df)))
       (deq_subst_convert $id $r1 $r2 $deqA $dr1 $dr2 $sc1 $df $deqr)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_π1 _ $s $s' $u _ _ $B $dA $du $dB $dv) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_π1 _ $s $s' _ _ _ _
          (der_subst _ $dr1 $sc1 $dA)
          (der_subst _ $dr1 $sc1 $du)
          (der_subst _ $dr1 (SCPush $sc1 $dA) $dB)
          (JT (teq_subst_apply $id $r1 $u $B)
              (der_subst _ $dr1 $sc1 $dv)))
       (deq_subst_convert $id $r1 $r2 $deqA $dr1 $dr2 $sc1 $du $deqr)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_π2 _ $s $s' $u _ _ $B $dA $du $dB $dv) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (Jeq (teq_inv (teq_subst_apply $id $r1 $u $B))
            (TRefl _)
            (TRefl _)
            (der_eq_π2 _ $s $s' _ _ _ _
               (der_subst _ $dr1 $sc1 $dA)
               (der_subst _ $dr1 $sc1 $du)
               (der_subst _ $dr1 (SCPush $sc1 $dA) $dB)
               (JT (teq_subst_apply $id $r1 $u $B)
                   (der_subst _ $dr1 $sc1 $dv))))
       (deq_subst_convert $id $r1 $r2 $deqA $dr1 $dr2 $sc1 $dv $deqr)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_conversion _ $s _ _ _ _ $deqt $deqT) $deqr
  ↪ der_eq_conversion _ $s _ _ _ _
       (deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 $deqt $deqr)
       (der_eq_subst $id $dr1 $sc1 $deqT)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_lift _ $s _ _ _ _ $de) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_lift _ $s _ _ _ _ (der_subst _ $dr1 $sc1 $de))
       (deq_subst_convert $id $r1 $r2 $deqA $dr1 $dr2 $sc1
                          (inv_teq_t2 (inv_sort $de)) $deqr)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_refl _ _ _ _ $du) $deqr
  ↪ deq_subst_convert $id $r1 $r2 $deqA $dr1 $dr2 $sc1 $du $deqr
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_trans _ $s _ _ _ _ $duv $dvw) $deqr
  ↪ der_eq_trans _ $s _ _ _ _
                  (der_eq_subst $id $dr1 $sc1 $duv)
                  (deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 $dvw $deqr)
with deq_cong_subst $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (der_eq_symm _ _ _ _ _ $duv) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_symm _ _ _ _ _ (der_eq_subst $id $dr1 $sc1 $duv))
       (deq_subst_convert $id $r1 $r2 $deqA $dr1 $dr2 $sc1 (inv_eq_t1 $duv) $deqr)

with deq_cong_subst $id $r1 $r2 $deqR $dr1 $dr2 $sc1 (der_eq_cong_tfun _ $s $s' _ _ _ _ $deqA $deqB $dB1 $dB2) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_cong_tfun _ $s $s' _ _ _ _
                         (der_eq_subst $id $dr1 $sc1 $deqA)
                         (der_eq_subst (dbsucc $id) $dr1 (SCPush $sc1 (inv_eq_t1 $deqA)) $deqB)
                         (der_subst _ $dr1 (SCPush $sc1 (inv_eq_t1 $deqA)) $dB1)
                         (der_subst _ $dr1 (SCPush $sc1 (inv_eq_t2 $deqA)) $dB2))
       (deq_subst_convert $id $r1 $r2 $deqR $dr1 $dr2 $sc1 (der_prod _ _ _ _ _ (inv_eq_t2 $deqA) $dB2) $deqr)
with deq_cong_subst $id $r1 $r2 $deqR $dr1 $dr2 $sc1 (der_eq_cong_tabs _ $s $s' _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2) $deqr
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_cong_tabs _ $s $s' _ _ _ _ _ _
                         (der_eq_subst $id $dr1 $sc1 $deqA)
                         (der_eq_subst (dbsucc $id) $dr1 (SCPush $sc1 (inv_eq_t1 $deqA)) $deqB)
                         (der_eq_subst (dbsucc $id) $dr1 (SCPush $sc1 (inv_eq_t1 $deqA)) $deqt)
                         (der_subst _ $dr1 (SCPush $sc1 (inv_eq_t1 $deqA)) $dB1)
                         (der_subst _ $dr1 (SCPush $sc1 (inv_eq_t2 $deqA)) $dB2)
                         (der_subst _ $dr1 (SCPush $sc1 (inv_eq_t1 $deqA)) $dt1)
                         (der_subst _ $dr1 (SCPush $sc1 (inv_eq_t2 $deqA)) $dt2))
       (deq_subst_convert $id $r1 $r2 $deqR $dr1 $dr2 $sc1 (inv_eq_t2 (der_eq_cong_tabs _ _ _ _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)) $deqr)
;
