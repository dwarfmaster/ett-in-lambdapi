
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
require open ETT.Shifting;

// TODO deq_cong_subst
symbol deq_cong_subst {Γ : Context} (id : ETT.DBId) (sc : ShiftContext Γ id)
                      {s s' : ETT.Sort} {A1 A2 B1 B2 f1 f2 t1 t2 : ETT.Term}
                      (deqA : der_eq Γ (ETT.snext s) (ETT.tsort s) A1 A2) (_ : der_eq (sc_to_sctx (inv_eq_t1 deqA) sc) (ETT.snext s') (ETT.tsort s') B1 B2)
                      (_ : der_eq (sc_to_sctx (inv_eq_t1 deqA) sc) s' B1 f1 f2) (_ : der_eq Γ s A1 t1 t2)
                      (_ : der (sc_to_sctx (inv_eq_t1 deqA) sc) B1 (ETT.tsort s') (ETT.snext s')) (_ : der (sc_to_sctx (inv_eq_t2 deqA) sc) B2 (ETT.tsort s') (ETT.snext s'))
                      (_ : der (sc_to_sctx (inv_eq_t1 deqA) sc) f1 B1 s') (_ : der (sc_to_sctx (inv_eq_t2 deqA) sc) f2 B2 s')
                      (_ : der Γ t1 A1 s) (_ : der Γ t2 A2 s)
                      : der_eq (sc_to_ctx sc) s' (subst id (Shift* id t1) B1) (subst id (Shift* id t1) f1) (subst id (Shift* id t2) f2);
rule @der_eq_cong_apply $Γ $s $s' $A1 $A2 _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2
  ↪ deq_cong_subst db0 (SC0 (inv_eq_context $deqA)) $deqA
                    (der_eq_refl (Push $A1 $s $Γ) (ETT.snext (ETT.snext $s')) (ETT.tsort $s') (ETT.tsort (ETT.snext $s'))
                                 (der_sort (Push $A1 $s $Γ) $s' (inv_context $dB1)))
                    $deqB $deqt
                    (der_sort (Push $A1 $s $Γ) $s' (inv_context $dB1))
                    (der_sort (Push $A2 $s $Γ) $s' (inv_context $dB2))
                    $dB1 $dB2 $dt1 $dt2;

// TODO der_subst
symbol der_subst {Γ : Context} (id : ETT.DBId) (sc : ShiftContext Γ id)
                 {s s' : ETT.Sort} {A B C u : ETT.Term}
                 (du : der Γ u A s) (_ : der (sc_to_sctx (inv_sort du) sc) C B s')
                 : der (sc_to_ctx sc) (subst id (Shift* id u) C) (subst id (Shift* id u) B) s';
rule substitution $dB $du ↪ der_subst db0 (SC0 (inv_context $du)) $du $dB;

//rule der_subst _ $sc _ (der_sort _ $s _) ↪ der_sort (sc_to_ctx $sc) $s (sc_to_dctx $sc)
//with der_subst $id $sc $d (der_prod _ $s $s' $A $B $dA $dB)
//  ↪ der_prod (sc_to_ctx $sc) $s $s' _ _
//              (der_subst $id $sc $d $dA)
//              (der_subst (dbsucc $id) (SCSucc $sc $dA) (der_shift0 $dA $d) $dB)
//;

// TODO τ_subst_n
symbol τ_subst_n {Γ : TContext} (id : ETT.DBId) (sc : ShiftTContext Γ id)
                 {s s' : ETT.Sort} {A B b a : ETT.Term}
                 (da : der (τ_Γ Γ) a A s)
                 (db : der (tsc_to_sctx (inv_sort da) sc) b B s') :
  H (τ (tsc_to_stc (inv_sort da) (τ Γ da) sc) db)
    (τ (tsc_to_tc sc) (der_subst id (tsc_to_sc sc) da db));
rule τ_subst_eq $Γ $db $da ↪ τ_subst_n db0 (TSC0 $Γ (inv_context $da)) $da $db
with τ_substT_eq $Γ $dB $da ↪ heq_to_eq (τ_subst_eq $Γ $dB $da);

