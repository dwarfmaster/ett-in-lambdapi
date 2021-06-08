
require ETT.XAst as ETT;
require open ETT.XTyping;
require open ETT.DeBruijn;
require open ETT.XLemmas;
require open ETT.ITT;
require open ETT.ILemmas;
require open ETT.Inversions;
require open ETT.HEq;
require open ETT.TranslationDefinition;
require open ETT.TranslationLemmas;

// SubstContext
constant symbol SubstContext {Γ : Context} {A : ETT.Term} {s : ETT.Sort} : der Γ A (ETT.tsort s) (ETT.snext s) → ETT.DBId → TYPE;
symbol sc_to_ctx {Γ : Context} {A : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                 : SubstContext d id → Context;
symbol sc_to_dctx {Γ : Context} {A : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                  (sc : SubstContext d id) : der_context (sc_to_ctx sc);
symbol sc_to_sctx {Γ : Context} {A t : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                  : der Γ t A s → SubstContext d id → Context;
symbol sc_to_dsctx {Γ : Context} {A t : ETT.Term} {s : ETT.Sort} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                   (dt : der Γ t A s) (sc : SubstContext d id) : der_context (sc_to_sctx dt sc);

constant symbol SC0 {Γ : Context} {s : ETT.Sort} {A : ETT.Term} (d : der Γ A (ETT.tsort s) (ETT.snext s)) : SubstContext d db0;
constant symbol SCPush {Γ : Context} {s s' : ETT.Sort} {A B : ETT.Term} {d : der Γ A (ETT.tsort s) (ETT.snext s)} {id : ETT.DBId}
                       (sc : SubstContext d id) : der (sc_to_ctx sc) B (ETT.tsort s') (ETT.snext s') → SubstContext d (dbsucc id);

rule sc_to_ctx (@SC0 $Γ $s $A _) ↪ Push $A $s $Γ
with sc_to_ctx (@SCPush _ _ $s _ $B _ _ $sc _) ↪ Push $B $s (sc_to_ctx $sc)
with sc_to_sctx _ (@SC0 $Γ _ _ _) ↪ $Γ
with @sc_to_sctx _ _ $t _ _ _ $dt (@SCPush _ _ $s _ $B _ $id $sc _) ↪ Push (subst $id (Shift* $id $t) $B) $s (sc_to_sctx $dt $sc);
rule sc_to_dctx (SC0 $d) ↪ pushΓ $d
with sc_to_dctx (SCPush _ $dB) ↪ pushΓ $dB;

// TODO deq_cong_subst
symbol deq_cong_subst {Γ : Context} (id : ETT.DBId)
                      {s s' : ETT.Sort} {A1 A2 B1 B2 f1 f2 t1 t2 : ETT.Term}
                      (deqA : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2)
                      (sc1 : SubstContext (inv_eq_t1 deqA) id) (sc2 : SubstContext (inv_eq_t2 deqA) id)
                      (_ : der_eq (sc_to_ctx sc1) (ETT.snext s') (ETT.tsort s') B1 B2)
                      (_ : der_eq (sc_to_ctx sc1) s' B1 f1 f2) (_ : der_eq Γ s A1 t1 t2)
                      (_ : der (sc_to_ctx sc1) B1 (ETT.tsort s') (ETT.snext s')) (_ : der (sc_to_ctx sc2) B2 (ETT.tsort s') (ETT.snext s'))
                      (_ : der (sc_to_ctx sc1) f1 B1 s') (_ : der (sc_to_ctx sc2) f2 B2 s')
                      (dt1 : der Γ t1 A1 s) (_ : der Γ t2 A2 s)
                      : der_eq (sc_to_sctx dt1 sc1) s' (subst id (Shift* id t1) B1) (subst id (Shift* id t1) f1) (subst id (Shift* id t2) f2);
rule @der_eq_cong_apply $Γ $s $s' $A1 $A2 _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2
  ↪ deq_cong_subst db0 $deqA
                    (SC0 (inv_eq_t1 $deqA)) (SC0 (inv_eq_t2 $deqA))
                    (der_eq_refl (Push $A1 $s $Γ) (ETT.snext (ETT.snext $s')) (ETT.tsort $s') (ETT.tsort (ETT.snext $s'))
                                 (der_sort (Push $A1 $s $Γ) $s' (inv_context $dB1)))
                    $deqB $deqt
                    (der_sort (Push $A1 $s $Γ) $s' (inv_context $dB1))
                    (der_sort (Push $A2 $s $Γ) $s' (inv_context $dB2))
                    $dB1 $dB2 $dt1 $dt2;

// TODO der_subst
symbol der_subst {Γ : Context} (id : ETT.DBId)
                 {s s' : ETT.Sort} {A B C u : ETT.Term}
                 (du : der Γ u A s) (sc : SubstContext (inv_sort du) id)
                 (_ : der (sc_to_ctx sc) C B s')
                 : der (sc_to_sctx du sc) (subst id (Shift* id u) C) (subst id (Shift* id u) B) s';
rule substitution $dB $du ↪ der_subst db0 $du (SC0 (inv_sort $du)) $dB;

//rule der_subst _ $sc _ (der_sort _ $s _) ↪ der_sort (sc_to_ctx $sc) $s (sc_to_dctx $sc)
//with der_subst $id $sc $d (der_prod _ $s $s' $A $B $dA $dB)
//  ↪ der_prod (sc_to_ctx $sc) $s $s' _ _
//              (der_subst $id $sc $d $dA)
//              (der_subst (dbsucc $id) (SCSucc $sc (der_subst $id $sc $d $dA)) $d $dB)
//;

// TODO τ_subst_n
//symbol τ_subst_n {Γ : TContext} (id : ETT.DBId) (sc : ShiftTContext Γ id)
//                 {s s' : ETT.Sort} {A B b a : ETT.Term}
//                 (da : der (τ_Γ Γ) a A s)
//                 (db : der (tsc_to_sctx (inv_sort da) sc) b B s') :
//  H (τ (tsc_to_stc (inv_sort da) (τ Γ da) sc) db)
//    (τ (tsc_to_tc sc) (der_subst id (tsc_to_sc sc) da db));
//rule τ_subst_eq $Γ $db $da ↪ τ_subst_n db0 (TSC0 $Γ (inv_context $da)) $da $db
//with τ_substT_eq $Γ $dB $da ↪ heq_to_eq (τ_subst_eq $Γ $dB $da);
