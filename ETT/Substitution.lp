
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.XCongruences;
require open ETT.TermEquality;
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

// SubstContext
constant symbol SubstContext {Γ : Context} {A : ETT.Term} {s : ETT.Sort} : der Γ A (ETT.tsort s) (ETT.snext s) → ETT.DBId → TYPE;
symbol sc_to_ctx {Γ : Context} {A : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                 : SubstContext d id → Context;
symbol sc_to_dctx {Γ : Context} {A : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                  (sc : SubstContext d id) : der_context (sc_to_ctx sc);
symbol sc_to_sctx {Γ : Context} {A t : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                  (d : der Γ t A s) (dΓ : der_context Γ) : SubstContext (inv_sort dΓ d) id → Context;
symbol sc_to_dsctx {Γ : Context} {A t : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                   (dt : der Γ t A s) (dΓ : der_context Γ) (sc : SubstContext (inv_sort dΓ dt) id) : der_context (sc_to_sctx dt dΓ sc);

constant symbol SC0 {Γ : Context} {s : ETT.Sort} {A : ETT.Term}
                    (d : der Γ A (ETT.tsort s) (ETT.snext s)) (_ : der_context Γ) : SubstContext d db0;
constant symbol SCPush {Γ : Context} {s s' : ETT.Sort} {A B : ETT.Term} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                       (sc : SubstContext d id) : der (sc_to_ctx sc) B (ETT.tsort s') (ETT.snext s') → SubstContext d (dbsucc id);

rule sc_to_ctx (@SC0 $Γ $s $A _ _) ↪ Push $A $s $Γ
with sc_to_ctx (@SCPush _ _ $s _ $B _ _ $sc _) ↪ Push $B $s (sc_to_ctx $sc)
with sc_to_sctx _ _ (@SC0 $Γ _ _ _ _) ↪ $Γ
with @sc_to_sctx _ _ $t _ _ $dt $dΓ (@SCPush _ _ $s _ $B _ $id $sc _) ↪ Push (subst $id (Shift* $id $t) $B) $s (sc_to_sctx $dt $dΓ $sc);
rule sc_to_dctx (SC0 $d $dΓ) ↪ pushΓ $d $dΓ
with sc_to_dctx (SCPush $sc $dB) ↪ pushΓ $dB (sc_to_dctx $sc);

// EqSubstContext
constant symbol EqSubstContext {Γ : Context} {A1 A2 : ETT.Term} {s : ETT.Sort}
                               : der Γ A1 (ETT.tsort s) (ETT.snext s)
                               → der Γ A2 (ETT.tsort s) (ETT.snext s)
                               → ETT.DBId → TYPE;
symbol esc_to_sc1 {Γ : Context} {A1 A2 : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                  {d1 : der Γ A1 (ETT.tsort s) (ETT.snext s)}
                  {d2 : der Γ A2 (ETT.tsort s) (ETT.snext s)}
                  : EqSubstContext d1 d2 id → SubstContext d1 id;
symbol esc_to_sc2 {Γ : Context} {A1 A2 : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                  {d1 : der Γ A1 (ETT.tsort s) (ETT.snext s)}
                  {d2 : der Γ A2 (ETT.tsort s) (ETT.snext s)}
                  : EqSubstContext d1 d2 id → SubstContext d2 id;
constant symbol ESC0 {Γ : Context} {A1 A2 : ETT.Term} {s : ETT.Sort}
                     (dΓ : der_context Γ)
                     (d1 : der Γ A1 (ETT.tsort s) (ETT.snext s))
                     (d2 : der Γ A2 (ETT.tsort s) (ETT.snext s))
                     : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2
                     → EqSubstContext d1 d2 db0;
constant symbol ESCPush {Γ : Context} {A1 A2 B : ETT.Term} {s s' : ETT.Sort} {id : ETT.DBId}
                        {d1 : der Γ A1 (ETT.tsort s) (ETT.snext s)}
                        {d2 : der Γ A2 (ETT.tsort s) (ETT.snext s)}
                        (esc : EqSubstContext d1 d2 id)
                        (dB1 : der (sc_to_ctx (esc_to_sc1 esc)) B (ETT.tsort s') (ETT.snext s'))
                        (dB2 : der (sc_to_ctx (esc_to_sc2 esc)) B (ETT.tsort s') (ETT.snext s'))
                        : EqSubstContext d1 d2 (dbsucc id);

rule esc_to_sc1 (ESC0 $dΓ $d1 _ _) ↪ SC0 $d1 $dΓ
with esc_to_sc1 (ESCPush $esc $d1 _) ↪ SCPush (esc_to_sc1 $esc) $d1
with esc_to_sc2 (ESC0 $dΓ _ $d2 _) ↪ SC0 $d2 $dΓ
with esc_to_sc2 (ESCPush $esc _ $d2) ↪ SCPush (esc_to_sc2 $esc) $d2;


// Conversion
symbol deq_subst_convert {Γ : Context} (id : ETT.DBId)
                         {s s' : ETT.Sort} {A1 A2 B f : ETT.Term} (t1 t2 : ETT.Term)
                         (dΓ : der_context Γ)
                         (deqA : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2)
                         (dt1 : der Γ t1 A1 s) (dt2 : der Γ t2 A2 s)
                         (esc : EqSubstContext (inv_sort dΓ dt1) (inv_sort dΓ dt2) id)
                         (_ : der (sc_to_ctx (esc_to_sc1 esc)) f B s') (_ : der_eq Γ s A1 t1 t2)
                         : der_eq (sc_to_sctx dt1 dΓ (esc_to_sc1 esc)) s' (subst id (Shift* id t1) B) (subst id (Shift* id t1) f) (subst id (Shift* id t2) f);
symbol deq_convert_var {Γ : Context} (id : ETT.DBId)
                       {s : ETT.Sort} {A1 A2 : ETT.Term} (t1 t2 : ETT.Term)
                       (dΓ : der_context Γ)
                       (deqA : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2)
                       (dt1 : der Γ t1 A1 s) (dt2 : der Γ t2 A2 s)
                       (esc : EqSubstContext (inv_sort dΓ dt1) (inv_sort dΓ dt2) id)
                       (i : ETT.DBId) (_ : der_eq Γ s A1 t1 t2)
                       : der_eq (sc_to_sctx dt1 dΓ (esc_to_sc1 esc))
                                (getS (sc_to_ctx (esc_to_sc1 esc)) i)
                                (subst id (Shift* id t1) (ShiftN i (get (sc_to_ctx (esc_to_sc1 esc)) i)))
                                (dbselect id i (Shift* id t1) (ETT.var i) (ETT.var (dbprev i)))
                                (dbselect id i (Shift* id t2) (ETT.var i) (ETT.var (dbprev i)));

symbol der_subst {Γ : Context} (id : ETT.DBId)
                 {s s' : ETT.Sort} {A B C u : ETT.Term}
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_sort dΓ du) id)
                 (_ : der (sc_to_ctx sc) C B s')
                 : der (sc_to_sctx du dΓ sc) (subst id (Shift* id u) C) (subst id (Shift* id u) B) s';
symbol der_context_subst
       {Γ : Context} (id : ETT.DBId)
       {s : ETT.Sort} {A u : ETT.Term}
       (dΓ : der_context Γ)
       (d : der Γ u A s) (sc : SubstContext (inv_sort dΓ d) id)
       (i : ETT.DBId)
       : der (sc_to_sctx d dΓ sc) (dbselect id i (Shift* id u) (ETT.var i) (ETT.var (dbprev i)))
             (subst id (Shift* id u) (ShiftN i (get (sc_to_ctx sc) i)))
             (getS (sc_to_ctx sc) i);
symbol der_eq_subst {Γ : Context} (id : ETT.DBId)
                    {s s' : ETT.Sort} {A B C1 C2 : ETT.Term} (u : ETT.Term)
                    (dΓ : der_context Γ)
                    (du : der Γ u A s) (sc : SubstContext (inv_sort dΓ du) id)
                    (_ : der_eq (sc_to_ctx sc) s' B C1 C2)
                    : der_eq (sc_to_sctx du dΓ sc) s' (subst id (Shift* id u) B) (subst id (Shift* id u) C1) (subst id (Shift* id u) C2);

rule substitution $dΓ $dB $du ↪ der_subst db0 $dΓ $du (SC0 (inv_sort $dΓ $du) $dΓ) $dB;

rule sc_to_dsctx _ _ (SC0 _ $dΓ) ↪ $dΓ
with sc_to_dsctx $d $dΓ (SCPush $sc $dA) ↪ pushΓ (der_subst _ $dΓ $d $sc $dA) (sc_to_dsctx $d $dΓ $sc);

// der_eq_cong_apply
rule der_eq_cong_apply $dΓ $deqA $deqB $deqt _ _ $dt1 $dt2
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_subst db0 _ $dΓ $dt1 (SC0 (inv_sort $dΓ $dt1) $dΓ) $deqB)
       (deq_subst_convert db0 _ _ $dΓ $deqA $dt1 $dt2 (ESC0 $dΓ (inv_sort $dΓ $dt1) (inv_sort $dΓ $dt2) $deqA) (inv_eq_t2 (pushIΓ $dΓ $dt1) $deqB) $deqt);

// Types
rule der_subst _ $dΓ $d $sc (der_sort _ $s) ↪ der_sort (sc_to_sctx $d $dΓ $sc) $s
with der_subst $id $dΓ $d $sc (der_prod _ $s $s' _ _ $dA $dB)
  ↪ der_prod (sc_to_sctx $d $dΓ $sc) $s $s' _ _
              (der_subst $id $dΓ $d $sc $dA)
              (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
with der_subst $id $dΓ $d $sc (der_sigma _ $s $s' _ _ $dA $dB)
  ↪ der_sigma (sc_to_sctx $d $dΓ $sc) $s $s' _ _
               (der_subst $id $dΓ $d $sc $dA)
               (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
with der_subst $id $dΓ $d $sc (der_prop_type_eq _ $s _ _ _ $dA $du $dv)
  ↪ der_prop_type_eq _ $s _ _ _
                      (der_subst $id $dΓ $d $sc $dA)
                      (der_subst $id $dΓ $d $sc $du)
                      (der_subst $id $dΓ $d $sc $dv)

// Structural
with der_subst $id $dΓ $d $sc (der_var _ $i)
  ↪ der_context_subst $id $dΓ $d $sc $i
with der_context_subst db0 _ $d (SC0 _ _) db0
  ↪ $d
with @der_context_subst _ (dbsucc $id) _ _ $x $dΓ $d (@SCPush _ _ _ _ $A _ _ $sc $dA) db0
  ↪ JT (teq_inv (teq_subst_shift $id (Shift* $id $x) $A))
        (der_var (sc_to_sctx $d $dΓ (SCPush $sc $dA)) db0)
with @der_context_subst _ db0 _ _ $x _ _ (@SC0 $Γ _ _ _ _) (dbsucc $i)
  ↪ JT (teq_inv (teq_shift_cancel_subst db0 $x (Shift* $i (get $Γ $i))))
        (der_var $Γ $i)
with @der_context_subst _ (dbsucc $id) _ _ $x $dΓ $d (SCPush $sc $dA) (dbsucc $i)
  ↪ JtT (teq_inv (teq_select_shift $id $i (Shift* $id $x)))
         (teq_inv (teq_subst_shift $id (Shift* $id $x) (ShiftN $i (get (sc_to_ctx $sc) $i))))
         (der_shift0
           (der_subst _ $dΓ $d $sc $dA)
           (sc_to_dsctx $d $dΓ $sc)
           (der_context_subst $id $dΓ $d $sc $i))
with der_subst _ $dΓ $d $sc (der_type_conv _ _ _ _ $s $du $deq)
  ↪ der_type_conv _ _ _ _ $s
                   (der_subst _ $dΓ $d $sc $du)
                   (der_eq_subst _ _ $dΓ $d $sc $deq)

// λ-calculus
with der_subst $id $dΓ $d $sc (der_abs _ $s $s' _ _ _ $dA $dB $dt)
  ↪ der_abs _ $s $s' _ _ _
             (der_subst $id $dΓ $d $sc $dA)
             (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
             (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dt)
with @der_subst _ $id _ _ _ _ _ $x $dΓ $d $sc (der_app _ $s $s' _ _ $a $B $dA $dB $df $da)
  ↪ JT (teq_inv (teq_subst_apply $id $x $a $B))
        (der_app _ $s $s' _ _ _ _
                 (der_subst $id $dΓ $d $sc $dA)
                 (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                 (der_subst $id $dΓ $d $sc $df)
                 (der_subst $id $dΓ $d $sc $da))
with @der_subst _ $id _ _ _ _ _ $x $dΓ $d $sc (der_pair _ $s $s' $u _ _ $B $dA $du $dB $dv)
  ↪ der_pair _ $s $s' _ _ _ _
              (der_subst $id $dΓ $d $sc $dA)
              (der_subst $id $dΓ $d $sc $du)
              (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
              (JT (teq_subst_apply $id $x $u $B)
                  (der_subst $id $dΓ $d $sc $dv))
with der_subst $id $dΓ $d $sc (der_π1 _ $s $s' _ _ _ $dA $dB $dp)
  ↪ der_π1 _ $s $s' _ _ _
            (der_subst $id $dΓ $d $sc $dA)
            (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
            (der_subst $id $dΓ $d $sc $dp)
with @der_subst _ $id _ _ _ _ _ $x $dΓ $d $sc (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ JT (teq_inv (teq_subst_apply $id $x (ETT.π1 $A $B $p) $B))
        (der_π2 _ $s $s' _ _ _
                (der_subst $id $dΓ $d $sc $dA)
                (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                (der_subst $id $dΓ $d $sc $dp))
// Equality
with der_subst $id $dΓ $d $sc (der_refl _ $s _ _ $dA $du)
  ↪ der_refl _ $s _ _
              (der_subst $id $dΓ $d $sc $dA)
              (der_subst $id $dΓ $d $sc $du)
with der_subst $id $dΓ $d $sc (der_uip _ $s _ _ _ $dA $da $dp)
  ↪ der_uip _ $s _ _ _
             (der_subst $id $dΓ $d $sc $dA)
             (der_subst $id $dΓ $d $sc $da)
             (der_subst $id $dΓ $d $sc $dp)
;

// SubstTContext
constant symbol SubstTContext (Γ : TContext) {t A : ETT.Term} {s : ETT.Sort} : der (τ_Γ Γ) t A s → ETT.DBId → TYPE;
symbol tsc_to_tc {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                 : SubstTContext Γ d id → TContext;
symbol tsc_to_stc {Γ : TContext} {A t : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                  : SubstTContext Γ d id → TContext;
symbol tsc_to_sc {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                 : SubstTContext Γ d id → SubstContext (inv_sort (τ_dΓ Γ) d) id;

symbol tsc_to_ctx {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                 : SubstTContext Γ d id → Context;
rule tsc_to_ctx $sc ↪ sc_to_ctx (tsc_to_sc $sc)
with τ_Γ (tsc_to_tc $sc) ↪ sc_to_ctx (tsc_to_sc $sc);
symbol tsc_to_sctx {Γ : TContext} {t A : ETT.Term} {s : ETT.Sort} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                  : SubstTContext Γ d id → Context;
rule @tsc_to_sctx $Γ _ _ _ $d _ $sc ↪ sc_to_sctx $d (τ_dΓ $Γ) (tsc_to_sc $sc)
with τ_Γ (@tsc_to_stc $Γ _ _ _ $d _ $sc) ↪ sc_to_sctx $d (τ_dΓ $Γ) (tsc_to_sc $sc);

constant symbol TSC0 (Γ : TContext) {s : ETT.Sort} {t A : ETT.Term} (d : der (τ_Γ Γ) t A s) : SubstTContext Γ d db0;
constant symbol TSCPush {Γ : TContext} {s s' : ETT.Sort} {t A B : ETT.Term} {d : der (τ_Γ Γ) t A s} {id : ETT.DBId}
                        (sc : SubstTContext Γ d id) (dB : der (tsc_to_ctx sc) B (ETT.tsort s') (ETT.snext s'))
                        : ε _ (τ (tsc_to_tc sc) dB) → SubstTContext Γ d (dbsucc id);

rule tsc_to_tc (TSC0 $Γ $d) ↪ TPush $Γ _ _ (inv_sort (τ_dΓ $Γ) $d) (τ $Γ $d)
with tsc_to_tc (TSCPush $sc $dB $b) ↪ TPush (tsc_to_tc $sc) _ _ $dB $b
with tsc_to_sc (TSC0 $Γ $d) ↪ SC0 (inv_sort (τ_dΓ $Γ) $d) (τ_dΓ $Γ)
with tsc_to_sc (TSCPush $sc $dB _) ↪ SCPush (tsc_to_sc $sc) $dB;

symbol τ_subst_n (Γ : TContext) (id : ETT.DBId)
                 {s s' : ETT.Sort} {A B b a : ETT.Term}
                 (da : der (τ_Γ Γ) a A s) (sc : SubstTContext Γ da id)
                 (db : der (tsc_to_ctx sc) b B s') :
  H (τ (tsc_to_tc sc) db)
    (τ (tsc_to_stc sc) (der_subst id (τ_dΓ Γ) da (tsc_to_sc sc) db));
symbol τ_context_subst_n
       {Γ : TContext} (id : ETT.DBId)
       {s : ETT.Sort} {A u : ETT.Term}
       (d : der (τ_Γ Γ) u A s) (sc : SubstTContext Γ d id)
       (i : ETT.DBId)
       : H (tgetShift i (tsc_to_tc sc))
           (τ (tsc_to_stc sc) (der_context_subst id (τ_dΓ Γ) d (tsc_to_sc sc) i));

rule tsc_to_stc (TSC0 $Γ _) ↪ $Γ
with tsc_to_stc (@TSCPush $Γ _ _ _ _ _ $d $id $sc $dB $b)
   ↪ TPush (tsc_to_stc $sc) _ _
            (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dB)
            (transport (heq_to_eq (τ_subst_n $Γ $id $d $sc $dB)) $b);
rule τ_subst_eq $Γ $db $da ↪ τ_subst_n _ db0 $da (TSC0 $Γ $da) $db
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

symbol magic_heq {s : Sort} {A B : U s} (a : ε s A) (b : ε s B) : HEq s A B a b;

// Types
rule τ_subst_n _ _ _ _ (der_sort _ $s)
  ↪ heq_refl _ (u (τ_s $s))
with τ_subst_n $Γ $id $d $sc (der_prod _ $s _ $A _ $dA $dB)
  ↪ cong_prod
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)
               (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (τ_subst_n $Γ $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n $Γ _ $d (TSCPush $sc $dA (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc))
                             (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                             (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
with τ_subst_n $Γ $id $d $sc (der_sigma _ $s _ $A _ $dA $dB)
  ↪ cong_sum
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)
                      (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (τ_subst_n $Γ $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n $Γ _ $d (TSCPush $sc $dA (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
with τ_subst_n $Γ $id $d $sc (der_prop_type_eq _ _ _ _ _ $dA $da1 $da2)
  ↪ cong_eq
       (τ_subst_n $Γ $id $d $sc $dA)
       (heq_conj
         (τ_subst_n $Γ $id $d $sc $da1)
         (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da1) $dA)
         (convert_T (tsc_to_stc $sc) (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da1)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)))
       (heq_conj
         (τ_subst_n $Γ $id $d $sc $da2)
         (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da2) $dA)
         (convert_T (tsc_to_stc $sc) (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da2)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)))
// Structural rules
with τ_subst_n _ $id $d $sc (der_var _ $i)
  ↪ heq_trans
       (heq_symm (heq_of_transport
         (tgetShift $i (tsc_to_tc $sc))
         (convert_T (tsc_to_tc $sc)
                    (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc)))
                    (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (der_getΓ $i (τ_dΓ (tsc_to_tc $sc)))))))
       (τ_context_subst_n $id $d $sc $i)
with τ_context_subst_n db0 _ (TSC0 $Γ $d) db0
  ↪ heq_symm (heq_of_transport
       (τ $Γ $d)
       (τ_shift0T_eq $Γ (inv_sort (τ_dΓ $Γ) $d) (inv_sort (τ_dΓ $Γ) $d) (τ $Γ $d)))
with @τ_context_subst_n $Γ (dbsucc $id) _ _ $x $d (@TSCPush _ _ _ _ _ $A _ _ $sc $dA $a) db0
  ↪ heq_trans
       (heq_trans
         (heq_symm (heq_of_transport $a
           (τ_shift0T_eq (tsc_to_tc $sc) $dA $dA $a)))
         (heq_trans
           (heq_trans
             (heq_of_transport $a
               (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))
             (heq_of_transport
               (transport (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)) $a)
               (τ_shift0T_eq (tsc_to_stc $sc)
                 (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                 (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                 (transport (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)) $a))))
           (heq_of_transport
             (tgetShift db0 (tsc_to_stc (TSCPush $sc $dA $a)))
             (convert_T (tsc_to_stc (TSCPush $sc $dA $a))
                        (der_shift db0 (τ_dΓ (tsc_to_stc (TSCPush $sc $dA $a))) (tgetD db0 (tsc_to_stc (TSCPush $sc $dA $a))))
                        (der_shift db0 (τ_dΓ (tsc_to_stc (TSCPush $sc $dA $a))) (der_getΓ db0 (τ_dΓ (tsc_to_stc (TSCPush $sc $dA $a)))))))))
       (τT (tsc_to_stc (TSCPush $sc $dA $a)) (teq_inv (teq_subst_shift $id (Shift* $id $x) $A))
           (der_var (sc_to_sctx $d (τ_dΓ $Γ) (SCPush (tsc_to_sc $sc) $dA)) db0))
with @τ_context_subst_n _ db0 _ _ $x _ (TSC0 $Γ $d) (dbsucc $i)
  ↪ heq_trans
       (heq_conj
         (heq_refl _ (tgetShift $i $Γ))
         (τ_shift0T_eq $Γ (der_shift $i (τ_dΓ $Γ) (tgetD $i $Γ)) (inv_sort (τ_dΓ $Γ) $d) (τ $Γ $d))
         (convert_T $Γ
           (der_shift $i (τ_dΓ $Γ) (tgetD $i $Γ))
           (der_shift $i (τ_dΓ $Γ) (der_getΓ $i (τ_dΓ $Γ)))))
       (τT $Γ (teq_inv (teq_shift_cancel_subst db0 $x (Shift* $i (get (τ_Γ $Γ) $i))))
           (der_var (τ_Γ $Γ) $i))
with @τ_context_subst_n $Γ (dbsucc $id) _ _ $x $d (TSCPush $sc $dA $a) (dbsucc $i)
  ↪ heq_trans
       (heq_trans
         (heq_trans
           (heq_symm (heq_of_transport
             (tgetShift $i (tsc_to_tc $sc))
             (τ_shift0T_eq (tsc_to_tc $sc) (der_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc))) $dA $a)))
           (τ_context_subst_n $id $d $sc $i))
         (τ_shift0_eq (tsc_to_stc $sc) (sc_to_dsctx $d (τ_dΓ $Γ) (tsc_to_sc $sc))
                      (der_context_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $i)
                      (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                      (transport (heq_to_eq (τ_subst_n _ $id $d $sc $dA)) $a)))
       (τtT (tsc_to_stc (TSCPush $sc $dA $a))
            (teq_inv (teq_select_shift $id $i (Shift* $id $x)))
            (teq_inv (teq_subst_shift $id (Shift* $id $x) (ShiftN $i (get (tsc_to_ctx $sc) $i))))
            (der_shift0
              (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
              (sc_to_dsctx $d (τ_dΓ $Γ) (tsc_to_sc $sc))
              (der_context_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $i)))
with τ_subst_n $Γ $id $d $sc (der_type_conv _ _ _ _ _ $du $deq)
  ↪ heq_conj
       (heq_conj
         (τ_subst_n $Γ $id $d $sc $du)
         (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du) (inv_eq_t1 (τ_dΓ (tsc_to_tc $sc)) $deq))
         (convert_T (tsc_to_stc $sc)
                    (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du))
                    (inv_eq_t1 (τ_dΓ (tsc_to_stc $sc)) (der_eq_subst $id _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $deq))))
       (τ_eqT (tsc_to_tc $sc) $deq)
       (τ_eqT (tsc_to_stc $sc) (der_eq_subst $id _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $deq))
// λ-calculus
with τ_subst_n $Γ $id $d $sc (der_abs _ $s _ $A _ _ $dA _ $dt)
  ↪ cong_lambda
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) (inv_sort (τ_dΓ (TPush (tsc_to_tc $sc) $s $A $dA a)) $dt))
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)
               (inv_sort (τ_dΓ (TPush (tsc_to_stc $sc) _ _ (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)) (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dt)))
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A $dA a) $dt)
       (λ a, τ (TPush (tsc_to_stc $sc) _ _ (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)
               (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dt))
       (τ_subst_n $Γ $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n $Γ _ $d (TSCPush $sc $dA (projT1 p)) (inv_sort (τ_dΓ (TPush (tsc_to_tc $sc) $s $A $dA (projT1 p))) $dt))
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) (inv_sort (τ_dΓ (TPush (tsc_to_tc $sc) $s $A $dA (projT1 p))) $dt))
                   (inv_sort (τ_dΓ (TPush (tsc_to_stc $sc) _ _ (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) (projT2 p))) (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dt))))
       (λ p, heq_trans
         (τ_subst_n $Γ _ $d (TSCPush $sc $dA (projT1 p)) $dt)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dt)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dt)))
with @τ_subst_n $Γ $id _ _ _ _ _ $x $d $sc (der_app _ $s $s' $A _ $a $B $dA $dB $df $da)
  ↪ heq_trans
       (heq_conj
         (cong_app
           (λ a, τ (TPush (tsc_to_tc $sc) $s $A (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da) a) $dB)
           (λ a, τ (TPush (tsc_to_stc $sc) $s _ (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da)) a)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB))
           (heq_trans
             (τ_subst_n $Γ _ $d $sc (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da))
             (convert (tsc_to_stc $sc)
               (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da))
               (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da))))
           (λ p, heq_trans
             (τ_subst_n $Γ _ $d (TSCPush $sc (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da) (projT1 p)) $dB)
             (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc))
                             (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da))
                             (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da))
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da))))) (projHEq p)))
                       (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da)) $dB)
                       (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
           (heq_conj
             (τ_subst_n $Γ _ $d $sc $df)
             (τ_fun_eq (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da) $dB (inv_sort (τ_dΓ (tsc_to_tc $sc)) $df))
             (τ_fun_eq (tsc_to_stc $sc)
                       (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da))
                       (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                       (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $df))))
           (τ_subst_n $Γ _ $d $sc $da))
         (τ_substT_eq (tsc_to_tc $sc) $dB $da)
         (τ_substT_eq (tsc_to_stc $sc)
                      (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                      (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da)))
       (τT (tsc_to_stc $sc) (teq_inv (teq_subst_apply $id $x $a $B))
           (der_app _ $s $s' _ _ _ _
                    (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                    (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                    (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $df)
                    (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da)))
with @τ_subst_n $Γ $id _ _ _ _ _ $x $d $sc (der_pair _ $s _ $u $A _ $B $dA $du $dB $dv)
  ↪ cong_pair
       (λ a, τ (TPush (tsc_to_tc $sc) $s $A (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du) a) $dB)
       (λ a, τ (TPush (tsc_to_stc $sc) $s _ (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du)) a)
               (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (heq_trans
         (τ_subst_n $Γ _ $d $sc (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du))
         (convert (tsc_to_stc $sc)
           (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du))
           (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du))))
       (λ p, heq_trans
         (τ_subst_n $Γ _ $d (TSCPush $sc (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du) (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du)) (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du))
                         (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du))))) (projHEq p)))
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du)) $dB)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
       (τ_subst_n $Γ _ $d $sc $du)
       (heq_conj
         (heq_conj
           (heq_trans
             (τ_subst_n $Γ _ $d $sc $dv)
             (τT (tsc_to_stc $sc) (teq_subst_apply $id $x $u $B) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dv)))
           (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $dv) (substitution (τ_dΓ (tsc_to_tc $sc)) $dB $du))
           (convert_T (tsc_to_stc $sc)
                      (inv_sort (τ_dΓ (tsc_to_stc $sc)) (JT (teq_subst_apply $id $x $u $B) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dv)))
                      (substitution (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du))))
         (inv_eq (τ_substT_eq (tsc_to_tc $sc) $dB $du))
         (inv_eq (τ_substT_eq (tsc_to_stc $sc)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du))))
with τ_subst_n $Γ $id $d $sc (der_π1 _ $s _ _ $A _ $dA $dB $dp)
  ↪ cong_proj1
       (λ a, τ_T (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
       (λ a, τ_T (TPush (tsc_to_stc $sc) _ _ (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)
                 (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB))
       (τ_subst_n $Γ $id $d $sc $dA)
       (λ p, heq_trans
         (τ_subst_n $Γ _ $d (TSCPush $sc $dA (projT1 p)) $dB)
         (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                             (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))) (projHEq p)))
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
       (heq_conj
         (τ_subst_n $Γ _ $d $sc $dp)
         (τ_sum_eq (tsc_to_tc $sc) $dA $dB (inv_sort (τ_dΓ (tsc_to_tc $sc)) $dp))
         (τ_sum_eq (tsc_to_stc $sc)
                   (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                   (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp))))
with @τ_subst_n $Γ $id _ _ _ _ _ $x $d $sc (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
  ↪ heq_trans
       (heq_conj
         (cong_proj2
           (λ a, τ_T (TPush (tsc_to_tc $sc) $s $A $dA a) $dB)
           (λ a, τ_T (TPush (tsc_to_stc $sc) _ _ (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) a)
                     (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB))
           (τ_subst_n $Γ $id $d $sc $dA)
           (λ p, heq_trans
             (τ_subst_n $Γ _ $d (TSCPush $sc $dA (projT1 p)) $dB)
             (convertR _ (PCPush (PCEmpty (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                                 (heq_trans (heq_symm (heq_of_transport (projT1 p) (heq_to_eq (τ_subst_n $Γ $id $d $sc $dA)))) (projHEq p)))
                       (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                       (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)))
           (heq_conj
             (τ_subst_n $Γ _ $d $sc $dp)
             (τ_sum_eq (tsc_to_tc $sc) $dA $dB (inv_sort (τ_dΓ (tsc_to_tc $sc)) $dp))
             (τ_sum_eq (tsc_to_stc $sc)
                       (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                       (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                       (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp)))))
         (τ_substT_eq (tsc_to_tc $sc) $dB (der_π1 (tsc_to_ctx $sc) $s $s' $p $A $B $dA $dB $dp))
         (τ_substT_eq (tsc_to_stc $sc)
           (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
           (der_π1 (tsc_to_sctx $sc) $s $s' _ _ _
             (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
             (der_subst _ (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
             (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp))))
       (τT (tsc_to_stc $sc)
           (teq_inv (teq_subst_apply $id $x (ETT.π1 $A $B $p) $B))
           (der_π2 _ $s $s' _ _ _
                   (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)
                   (der_subst (dbsucc $id) (τ_dΓ $Γ) $d (SCPush (tsc_to_sc $sc) $dA) $dB)
                   (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp)))
with τ_subst_n $Γ $id $d $sc (der_refl _ _ _ _ $dA $du)
  ↪ cong_refl
       (τ_subst_n $Γ $id $d $sc $dA)
       (heq_conj
         (τ_subst_n $Γ $id $d $sc $du)
         (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $du) $dA)
         (convert_T (tsc_to_stc $sc)
                    (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $du))
                    (der_subst _ (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA)))
with τ_subst_n $Γ $id $d $sc (der_uip _ $s $A $a $a $dA $da $dp)
  ↪ let dT ≔ der_prop_type_eq (τ_Γ (tsc_to_tc $sc)) $s $A $a $a $dA $da $da in
     let da' ≔ der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $da in
     let dA' ≔ der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dA in
     heq_conj
       (cong_K
           (τ_subst_n $Γ $id $d $sc $dA)
           (heq_conj
             (τ_subst_n $Γ $id $d $sc $da)
             (convert_T (tsc_to_tc $sc)  (inv_sort (τ_dΓ (tsc_to_tc $sc))  $da) $dA)
             (convert_T (tsc_to_stc $sc) (inv_sort (τ_dΓ (tsc_to_stc $sc)) da') dA'))
           (heq_conj
             (τ_subst_n $Γ $id $d $sc $dp)
             (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $dp) dT)
             (convert_T (tsc_to_stc $sc)
               (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp))
               (der_prop_type_eq (τ_Γ (tsc_to_stc $sc)) $s _ _ _ dA' da' da'))))
       (trans_eq_as_eq
         (transport (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $dp) dT) (τ (tsc_to_tc $sc) $dp))
         (eq_of_transport
           (refl (τ_s $s) (τ_T (tsc_to_tc $sc) $dA) (transport (convert_T (tsc_to_tc $sc) (inv_sort (τ_dΓ (tsc_to_tc $sc)) $da) $dA) (τ (tsc_to_tc $sc) $da)))
           (convert_T (tsc_to_tc $sc) dT dT)))
       (trans_eq_as_eq
         (transport
           (convert_T (tsc_to_stc $sc)
             (inv_sort (τ_dΓ (tsc_to_stc $sc)) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp))
             (der_prop_type_eq (τ_Γ (tsc_to_stc $sc)) $s _ _ _ dA' da' da'))
           (τ (tsc_to_stc $sc) (der_subst $id (τ_dΓ $Γ) $d (tsc_to_sc $sc) $dp)))
         (eq_of_transport
           (refl (τ_s $s) (τ_T (tsc_to_stc $sc) dA') (transport (convert_T (tsc_to_stc $sc) (inv_sort (τ_dΓ (tsc_to_stc $sc)) da') dA') (τ (tsc_to_stc $sc) da')))
           (convert_T (tsc_to_stc $sc)
             (der_prop_type_eq (τ_Γ (tsc_to_stc $sc)) $s _ _ _ dA' da' da')
             (der_prop_type_eq (τ_Γ (tsc_to_stc $sc)) $s _ _ _ dA' da' da'))))
;

rule der_eq_subst $id $r $dΓ $dr $sc (der_eq_beta _ $s $s' $u _ $t $B $dA $dB $dt $du)
  ↪ Jeq (teq_inv (teq_subst_apply $id $r $u $B))
         (TRefl _)
         (teq_inv (teq_subst_apply $id $r $u $t))
         (der_eq_beta (sc_to_sctx $dr $dΓ $sc) $s $s' _ _ _ _
                      (der_subst _ $dΓ $dr $sc $dA)
                      (der_subst _ $dΓ $dr (SCPush $sc $dA) $dB)
                      (der_subst _ $dΓ $dr (SCPush $sc $dA) $dt)
                      (der_subst _ $dΓ $dr $sc $du))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
  ↪ Jeq (TRefl _)
         (Jcong (ETT.tabs (subst $id (Shift* $id $r) $A) (subst (dbsucc $id) (Shift* (dbsucc $id) $r) $B))
           (teq_trans
             (Jcong
               (λ t, ETT.tapp t
                       (Shift1 (subst (dbsucc $id) (Shift* (dbsucc $id) $r) $B))
                       (Shift (subst $id (Shift* $id $r) $f))
                       (ETT.var db0))
               (teq_inv (teq_subst_shift $id (Shift* $id $r) $A)))
             (teq_trans
               (Jcong
                 (λ t, ETT.tapp (subst (dbsucc $id) (Shift (Shift* $id $r)) (Shift $A))
                         (Shift1 (subst (dbsucc $id) (Shift* (dbsucc $id) $r) $B))
                         t (ETT.var db0))
                 (teq_inv (teq_subst_shift $id (Shift* $id $r) $f)))
               (Jcong
                 (λ t, ETT.tapp (subst (dbsucc $id) (Shift (Shift* $id $r)) (Shift $A)) t
                         (subst (dbsucc $id) (Shift (Shift* $id $r)) (Shift $f))
                         (ETT.var db0))
                 (teq_inv (teq_subst_shift1 $id (Shift* $id $r) $B))))))
         (TRefl _)
         (der_eq_eta _ $s $s' _ _ _
                     (der_subst _ $dΓ $dr $sc $dA)
                     (der_subst _ $dΓ $dr (SCPush $sc $dA) $dB)
                     (der_subst _ $dΓ $dr $sc $df))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_π1 _ $s $s' $u _ _ $B $dA $du $dB $dv)
  ↪ der_eq_π1 _ $s $s' _ _ _ _
       (der_subst _ $dΓ $dr $sc $dA)
       (der_subst _ $dΓ $dr $sc $du)
       (der_subst _ $dΓ $dr (SCPush $sc $dA) $dB)
       (JT (teq_subst_apply $id $r $u $B)
           (der_subst _ $dΓ $dr $sc $dv))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_π2 _ $s $s' $u _ _ $B $dA $du $dB $dv)
  ↪  Jeq (teq_inv (teq_subst_apply $id $r $u $B))
          (TRefl _)
          (TRefl _)
          (der_eq_π2 _ $s $s' _ _ _ _
             (der_subst _ $dΓ $dr $sc $dA)
             (der_subst _ $dΓ $dr $sc $du)
             (der_subst _ $dΓ $dr (SCPush $sc $dA) $dB)
             (JT (teq_subst_apply $id $r $u $B)
                 (der_subst _ $dΓ $dr $sc $dv)))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_conversion _ $s _ _ _ _ $deqt $deqT)
  ↪ der_eq_conversion _ $s _ _ _ _
       (der_eq_subst $id $r $dΓ $dr $sc $deqt)
       (der_eq_subst $id $r $dΓ $dr $sc $deqT)
with der_eq_subst $id _ $dΓ $dr $sc (der_eq_lift _ $s _ _ _ _ $de)
  ↪ der_eq_lift _ $s _ _ _ _ (der_subst $id $dΓ $dr $sc $de)
with der_eq_subst $id _ $dΓ $dr $sc (der_eq_refl _ _ _ _ $du)
  ↪ der_eq_refl _ _ _ _ (der_subst $id $dΓ $dr $sc $du)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_trans _ $s _ _ _ _ $duv $dvw)
  ↪ der_eq_trans _ $s _ _ _ _
                  (der_eq_subst $id $r $dΓ $dr $sc $duv)
                  (der_eq_subst $id $r $dΓ $dr $sc $dvw)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_symm _ _ _ _ _ $duv)
  ↪ der_eq_symm _ _ _ _ _ (der_eq_subst $id $r $dΓ $dr $sc $duv)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_tfun _ $s $s' _ _ _ _ $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tfun _ $s $s' _ _ _ _
                      (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                      (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_tabs _ $s $s' _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ der_eq_cong_tabs _ $s $s' _ _ _ _ _ _
                      (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                      (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                      (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqt)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dt1)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dt2)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_tapp _ $s $s' _ _ $B1 _ _ _ $a1 _ $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ Jeq (teq_inv (teq_subst_apply $id $r $a1 $B1))
         (TRefl _)
         (TRefl _)
         (der_eq_cong_tapp _ $s $s' _ _ _ _ _ _ _ _
                           (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                           (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                           (der_eq_subst $id $r $dΓ $dr $sc $deqf)
                           (der_eq_subst $id $r $dΓ $dr $sc $deqa)
                           (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                           (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
                           (der_subst _ $dΓ $dr $sc $df1)
                           (der_subst _ $dΓ $dr $sc $df2)
                           (der_subst _ $dΓ $dr $sc $da1)
                           (der_subst _ $dΓ $dr $sc $da2))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_tsum _ $s $s' _ _ _ _ $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tsum _ $s $s' _ _ _ _
                      (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                      (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                      (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_tpair _ $s $s' _ _ $B1 $B2 $a1 $a2 _ _ $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_tpair _ $s $s' _ _ _ _ _ _ _ _
                       (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                       (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                       (der_eq_subst $id $r $dΓ $dr $sc $deqa)
                       (Jeq (teq_subst_apply $id $r $a1 $B1)
                            (TRefl _) (TRefl _)
                            (der_eq_subst $id $r $dΓ $dr $sc $deqb))
                       (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                       (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
                       (der_subst _ $dΓ $dr $sc $da1)
                       (der_subst _ $dΓ $dr $sc $da2)
                       (JT (teq_subst_apply $id $r $a1 $B1) (der_subst _ $dΓ $dr $sc $db1))
                       (JT (teq_subst_apply $id $r $a2 $B2) (der_subst _ $dΓ $dr $sc $db2))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_π1 _ $s $s' _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π1 _ $s $s' _ _ _ _ _ _
                    (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                    (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                    (der_eq_subst $id $r $dΓ $dr $sc $deqp)
                    (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                    (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
                    (der_subst _ $dΓ $dr $sc $dp1)
                    (der_subst _ $dΓ $dr $sc $dp2)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_π2 _ $s $s' $A1 _ $B1 _ $p1 _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ Jeq (teq_inv (teq_subst_apply $id $r (ETT.π1 $A1 $B1 $p1) $B1))
         (TRefl _)
         (TRefl _)
         (der_eq_cong_π2 _ $s $s' _ _ _ _ _ _
                         (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                         (der_eq_subst (dbsucc $id) $r $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $deqB)
                         (der_eq_subst $id $r $dΓ $dr $sc $deqp)
                         (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $dB1)
                         (der_subst _ $dΓ $dr (SCPush $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $dB2)
                         (der_subst _ $dΓ $dr $sc $dp1)
                         (der_subst _ $dΓ $dr $sc $dp2))
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_teq _ $s _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_teq _ $s _ _ _ _ _ _
                     (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                     (der_eq_subst $id $r $dΓ $dr $sc $deqa)
                     (der_eq_subst $id $r $dΓ $dr $sc $deqb)
                     (der_subst $id $dΓ $dr $sc $da1)
                     (der_subst $id $dΓ $dr $sc $da2)
                     (der_subst $id $dΓ $dr $sc $db1)
                     (der_subst $id $dΓ $dr $sc $db2)
with der_eq_subst $id $r $dΓ $dr $sc (der_eq_cong_trefl _ $s _ _ _ _ $deqA $deqa $da1 $da2)
  ↪ der_eq_cong_trefl _ $s _ _ _ _
                       (der_eq_subst $id $r $dΓ $dr $sc $deqA)
                       (der_eq_subst $id $r $dΓ $dr $sc $deqa)
                       (der_subst $id $dΓ $dr $sc $da1)
                       (der_subst $id $dΓ $dr $sc $da2)
;

symbol esc_to_sec {Γ : Context} {t1 t2 A1 A2 : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                  (dΓ : der_context Γ) (d1 : der Γ t1 A1 s) (d2 : der Γ t2 A2 s)
                  (deqt : der_eq Γ s A1 t1 t2) (deqT : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2)
                  : EqSubstContext (inv_sort dΓ d1) (inv_sort dΓ d2) id → EqContext;
rule ec_to_ctx1 (esc_to_sec $dΓ $dr1 _ _ _ $esc) ↪ sc_to_sctx $dr1 $dΓ (esc_to_sc1 $esc)
with ec_to_ctx2 (esc_to_sec $dΓ _ $dr2 _ _ $esc) ↪ sc_to_sctx $dr2 $dΓ (esc_to_sc2 $esc);
rule esc_to_sec $dΓ _ _ _ _ (ESC0 _ _ _ _) ↪ EC0 $dΓ
with esc_to_sec $dΓ $dr1 $dr2 $deqr $deqR (ESCPush $esc $d1 $d2)
  ↪ ECPush (esc_to_sec $dΓ $dr1 $dr2 $deqr $deqR $esc)
            (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $d1)
            (der_subst _ $dΓ $dr2 (esc_to_sc2 $esc) $d2)
            (deq_subst_convert _ _ _ $dΓ $deqR $dr1 $dr2 $esc $d1 $deqr);
symbol esc_to_ec {Γ : Context} {A1 A2 : ETT.Term} {s : ETT.Sort} {id : ETT.DBId}
                 {d1 : der Γ A1 (ETT.tsort s) (ETT.snext s)} {d2 : der Γ A2 (ETT.tsort s) (ETT.snext s)}
                 : EqSubstContext d1 d2 id → EqContext;
rule ec_to_ctx1 (esc_to_ec $esc) ↪ sc_to_ctx (esc_to_sc1 $esc)
with ec_to_ctx2 (esc_to_ec $esc) ↪ sc_to_ctx (esc_to_sc2 $esc);
rule esc_to_ec (ESC0 $dΓ $d1 $d2 $deq) ↪ ECPush (EC0 $dΓ) $d1 $d2 $deq
with esc_to_ec (ESCPush $esc $d1 $d2) ↪ ECPush (esc_to_ec $esc) $d1 $d2 (der_eq_refl _ _ _ _ $d1);

symbol renormalize_subst {Γ : Context} {s s' : ETT.Sort} {A t B : ETT.Term}
                         {sr : ETT.Sort} {R1 R2 r1 r2 : ETT.Term} {id : ETT.DBId}
                         (dΓ : der_context Γ) (dr1 : der Γ r1 R1 sr) (dr2 : der Γ r2 R2 sr)
                         (deqR : der_eq Γ (ETT.snext sr) (ETT.tsort sr) R1 R2) (deqr : der_eq Γ sr R1 r1 r2)
                         (esc : EqSubstContext (inv_sort dΓ dr1) (inv_sort dΓ dr2) id)
                         (dA : der (sc_to_ctx (esc_to_sc1 esc)) A (ETT.tsort s) (ETT.snext s))
                         (dB : der (Push A s (sc_to_ctx (esc_to_sc1 esc))) t B s') ≔
  convert_der'
   (ECPush (esc_to_sec dΓ dr1 dr2 deqr deqR esc)
     (convert_der' (esc_to_sec dΓ dr1 dr2 deqr deqR esc)
                   (der_subst _ dΓ dr2 (esc_to_sc2 esc) (convert_der (esc_to_ec esc) dA)))
     (der_subst _ dΓ dr2 (esc_to_sc2 esc) (convert_der (esc_to_ec esc) dA))
     (der_eq_refl _ _ _ _ (convert_der' (esc_to_sec dΓ dr1 dr2 deqr deqR esc)
                                        (der_subst _ dΓ dr2 (esc_to_sc2 esc) (convert_der (esc_to_ec esc) dA)))))
   (der_subst _ dΓ dr2 (SCPush (esc_to_sc2 esc) (convert_der (esc_to_ec esc) dA))
              (convert_der
                (ECPush (esc_to_ec esc) dA (convert_der (esc_to_ec esc) dA) (der_eq_refl _ _ _ _ dA))
                dB));
symbol der_subst_conj {Γ : Context} {s : ETT.Sort} {t A : ETT.Term}
                      {sr : ETT.Sort} {R1 R2 r1 r2 : ETT.Term} {id : ETT.DBId}
                      (dΓ : der_context Γ) (dr1 : der Γ r1 R1 sr) (dr2 : der Γ r2 R2 sr)
                      (deqR : der_eq Γ (ETT.snext sr) (ETT.tsort sr) R1 R2) (deqr : der_eq Γ sr R1 r1 r2)
                      (esc : EqSubstContext (inv_sort dΓ dr1) (inv_sort dΓ dr2) id)
                      (d : der (sc_to_ctx (esc_to_sc1 esc)) t A s) ≔
  convert_der' (esc_to_sec dΓ dr1 dr2 deqr deqR esc)
               (der_subst _ dΓ dr2 (esc_to_sc2 esc) (convert_der (esc_to_ec esc) d));

rule deq_subst_convert _ _ _ _ _ _ _ _ (der_sort _ $s) _
  ↪ der_eq_refl _ _ _ _ (der_sort _ $s)
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_prod _ $s $s' _ _ $dA $dB) $deqr
  ↪ der_eq_cong_tfun _ $s $s' _ _ _ _
                      (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                      (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                      (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                      (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_sigma _ $s $s' _ _ $dA $dB) $deqr
  ↪ der_eq_cong_tsum _ $s $s' _ _ _ _
                      (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                      (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                      (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                      (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_prop_type_eq _ $s _ _ _ $dA $du $dv) $deqr
  ↪ der_eq_cong_teq _ $s _ _ _ _ _ _
                     (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                     (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $du $deqr)
                     (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dv $deqr)
                     (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $du)
                     (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $du)
                     (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $dv)
                     (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $dv)

with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_var _ $i) $deqr
  ↪ deq_convert_var $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $i $deqr
with deq_convert_var db0 _ _ _ _ _ _ (ESC0 _ _ _ _) db0 $deqr
  ↪ $deqr
with deq_convert_var db0 $r1 _ _ _ _ _ (@ESC0 $Γ _ _ _ _ _ _ _) (dbsucc $i) _
  ↪ Jeq (teq_inv (teq_shift_cancel_subst db0 $r1 (Shift* $i (get $Γ $i))))
         (TRefl _)
         (TRefl _)
         (der_eq_refl _ _ _ _ (der_var _ $i))
with deq_convert_var (dbsucc $id) $r1 _ _ _ _ _ (@ESCPush _ _ _ $B _ _ _ _ _ _ _ _) db0 _
  ↪ Jeq (teq_inv (teq_subst_shift $id (Shift* $id $r1) $B))
         (TRefl _)
         (TRefl _)
         (der_eq_refl _ _ _ _ (der_var _ db0))
with deq_convert_var (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $d1 _) (dbsucc $i) $deqr
  ↪ Jeq (teq_inv (teq_subst_shift $id (Shift* $id $r1) (ShiftN $i (get (sc_to_ctx (esc_to_sc1 $esc)) $i))))
         (teq_inv (teq_select_shift $id $i (Shift* $id $r1)))
         (teq_inv (teq_select_shift $id $i (Shift* $id $r2)))
         (der_eq_shift0
           (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $d1)
           (sc_to_dsctx $dr1 $dΓ (esc_to_sc1 $esc))
           (deq_convert_var $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $i $deqr))

with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_type_conv _ _ _ _ _ $du $deq) $deqr
  ↪ der_eq_conversion _ _ _ _ _ _
       (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $du $deqr)
       (der_eq_subst $id _ $dΓ $dr1 (esc_to_sc1 $esc) $deq)
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_abs _ $s $s' _ _ _ $dA $dB $dt) $deqr
  ↪ der_eq_cong_tabs _ $s $s' _ _ _ _ _ _
                      (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                      (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                      (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dt $deqr)
                      (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                      (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
                      (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dt)
                      (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dt)
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_app _ $s $s' _ _ $u $B $dA $dB $dt $du) $deqr
  ↪ Jeq (teq_inv (teq_subst_apply $id $r1 $u $B))
         (TRefl _)
         (TRefl _)
         (der_eq_cong_tapp _ $s $s' _ _ _ _ _ _ _ _
                           (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                           (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                           (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dt $deqr)
                           (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $du $deqr)
                           (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                           (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
                           (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $dt)
                           (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $dt)
                           (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $du)
                           (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $du))
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_pair _ $s $s' $u _ _ $B $dA $du $dB $dv) $deqr
  ↪ der_eq_cong_tpair _ $s $s' _ _ _ _ _ _ _ _
                       (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                       (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                       (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $du $deqr)
                       (Jeq (teq_subst_apply $id $r1 $u $B)
                            (TRefl _)
                            (TRefl _)
                            (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dv $deqr))
                       (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                       (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
                       (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $du)
                       (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $du)
                       (JT (teq_subst_apply $id $r1 $u $B)
                           (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $dv))
                       (JT (teq_subst_apply $id $r2 $u $B)
                           (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $dv))
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_π1 _ $s $s' _ _ _ $dA $dB $dp) $deqr
  ↪ der_eq_cong_π1 _ $s $s' _ _ _ _ _ _
                    (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                    (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                    (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dp $deqr)
                    (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                    (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
                    (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $dp)
                    (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $dp)
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_π2 _ $s $s' $p $A $B $dA $dB $dp) $deqr
  ↪ Jeq (teq_inv (teq_subst_apply $id $r1 (ETT.π1 $A $B $p) $B))
         (TRefl _)
         (TRefl _)
         (der_eq_cong_π2 _ $s $s' _ _ _ _ _ _
                         (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                         (deq_subst_convert (dbsucc $id) $r1 $r2 $dΓ $deqR $dr1 $dr2 (ESCPush $esc $dA (convert_der (esc_to_ec $esc) $dA)) $dB $deqr)
                         (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dp $deqr)
                         (der_subst _ $dΓ $dr1 (SCPush (esc_to_sc1 $esc) $dA) $dB)
                         (renormalize_subst $dΓ $dr1 $dr2 $deqR $deqr $esc $dA $dB)
                         (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $dp)
                         (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $dp))
with deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc (der_refl _ $s _ _ $dA $du) $deqr
  ↪ der_eq_cong_trefl _ $s _ _ _ _
                       (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $dA $deqr)
                       (deq_subst_convert $id $r1 $r2 $dΓ $deqR $dr1 $dr2 $esc $du $deqr)
                       (der_subst _ $dΓ $dr1 (esc_to_sc1 $esc) $du)
                       (der_subst_conj $dΓ $dr1 $dr2 $deqR $deqr $esc $du)
;
